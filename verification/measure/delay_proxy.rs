//! Forwards TCP links with added one-way latency and jitter, to emulate
//! zones between keepers on one machine or a fast LAN.
//!
//! Each `--link LISTEN=TARGET/DELAY_MS[/JITTER_MS]` accepts connections on
//! `LISTEN` and forwards them to `TARGET`. Bytes in each direction are held
//! `DELAY_MS` plus a uniform random `0..=JITTER_MS` after they arrive, never
//! overtaking earlier bytes, so a link's round trip gains twice the delay.
//! TLS passes through untouched: keepers authenticate each other by
//! certificate, not by address.
//!
//! To place keepers in zones, give each keeper its own configuration whose
//! `peers` and `bulk` entries for other keepers name that keeper's proxy
//! listeners, while its own entries stay its real addresses. For three zones
//! with 1 ms intra-zone and 6 ms inter-zone round trips, links within a zone
//! take `/0.5` and links across zones `/3/1`.
//!
//! ```sh
//! cargo run --release --features stream --example delay-proxy -- \
//!     --link 127.0.0.1:7101=127.0.0.1:7001/3/1 --link 127.0.0.1:7102=127.0.0.1:7002/0.5
//! ```

use std::{net::SocketAddr, time::Duration};

use tokio::{
    io::{AsyncReadExt, AsyncWriteExt},
    net::{TcpListener, TcpStream},
    sync::mpsc,
    time::Instant,
};

#[derive(Clone, Copy, Debug)]
struct Link {
    listen: SocketAddr,
    target: SocketAddr,
    delay: Duration,
    jitter: Duration,
}

fn parse(spec: &str) -> Link {
    let usage = format!("--link takes LISTEN=TARGET/DELAY_MS[/JITTER_MS], not {spec}");
    let (listen, rest) = spec.split_once('=').expect(&usage);
    let mut parts = rest.split('/');
    let target = parts.next().expect(&usage);
    let millis = |text: &str| Duration::from_secs_f64(text.parse::<f64>().expect(&usage) / 1e3);
    Link {
        listen: listen.parse().expect(&usage),
        target: target.parse().expect(&usage),
        delay: millis(parts.next().expect(&usage)),
        jitter: parts.next().map_or(Duration::ZERO, millis),
    }
}

/// xorshift64*, seeded per direction.
struct Random(u64);

impl Random {
    fn below(&mut self, limit: Duration) -> Duration {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        let unit = (self.0.wrapping_mul(0x2545_f491_4f6c_dd1d) >> 11) as f64 / (1u64 << 53) as f64;
        limit.mul_f64(unit)
    }
}

/// Waits until `due`. Tokio's timer fires on a millisecond tick, too coarse
/// for sub-millisecond zones, so the last stretch yields instead of sleeping.
async fn hold_until(due: Instant) {
    let tick = Duration::from_micros(1500);
    if due.saturating_duration_since(Instant::now()) > tick {
        tokio::time::sleep_until(due - tick).await;
    }
    while Instant::now() < due {
        tokio::task::yield_now().await;
    }
}

/// Copies `from` to `to`, releasing each chunk once its delay has passed.
async fn forward(
    mut from: tokio::net::tcp::OwnedReadHalf,
    mut to: tokio::net::tcp::OwnedWriteHalf,
    link: Link,
    seed: u64,
) {
    let (sender, mut receiver) = mpsc::unbounded_channel::<(Instant, Vec<u8>)>();
    let reader = async move {
        let mut random = Random(seed | 1);
        let mut last = Instant::now();
        let mut buffer = vec![0; 64 * 1024];
        loop {
            let read = match from.read(&mut buffer).await {
                Ok(0) | Err(_) => return,
                Ok(read) => read,
            };
            let due = (Instant::now() + link.delay + random.below(link.jitter)).max(last);
            last = due;
            if sender.send((due, buffer[..read].to_vec())).is_err() {
                return;
            }
        }
    };
    let writer = async move {
        while let Some((due, bytes)) = receiver.recv().await {
            hold_until(due).await;
            if to.write_all(&bytes).await.is_err() {
                return;
            }
        }
        let _ = to.shutdown().await;
    };
    tokio::join!(reader, writer);
}

async fn serve(link: Link) {
    let listener = TcpListener::bind(link.listen).await.unwrap();
    let mut connections = 0u64;
    loop {
        let Ok((inbound, _)) = listener.accept().await else {
            continue;
        };
        connections += 1;
        let seed = connections.wrapping_mul(0x9e37_79b9_7f4a_7c15) ^ link.listen.port() as u64;
        tokio::spawn(async move {
            let Ok(outbound) = TcpStream::connect(link.target).await else {
                return;
            };
            let _ = inbound.set_nodelay(true);
            let _ = outbound.set_nodelay(true);
            let (inbound_read, inbound_write) = inbound.into_split();
            let (outbound_read, outbound_write) = outbound.into_split();
            tokio::join!(
                forward(inbound_read, outbound_write, link, seed),
                forward(outbound_read, inbound_write, link, !seed),
            );
        });
    }
}

#[tokio::main]
async fn main() {
    let mut links = Vec::new();
    let mut input = std::env::args().skip(1);
    while let Some(flag) = input.next() {
        match flag.as_str() {
            "--link" => links.push(parse(&input.next().expect("--link needs a value"))),
            other => panic!("unknown flag {other}"),
        }
    }
    assert!(!links.is_empty(), "give at least one --link");
    let tasks = links
        .into_iter()
        .map(|link| tokio::spawn(serve(link)))
        .collect::<Vec<_>>();
    println!("delay-proxy ready");
    for task in tasks {
        task.await.unwrap();
    }
}
