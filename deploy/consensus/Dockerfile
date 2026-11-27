# Consensus keeper image. Build from the repository root:
#   docker build -f deploy/consensus/Dockerfile -t logkeeper-consensus:dev .
# The healthcheck needs the keeper's admin listener on 127.0.0.1:5741:
# `"admin": {"listen": "127.0.0.1:5741"}` in the keeper config.

FROM rust:1.94.1-slim-bookworm AS build
WORKDIR /src
COPY . .
RUN --mount=type=cache,target=/usr/local/cargo/registry \
    --mount=type=cache,target=/src/target \
    cargo build --locked --release --features stream --bin logkeeper \
    && install -m 0555 target/release/logkeeper /usr/local/bin/logkeeper

FROM debian:bookworm-slim
# curl serves the healthcheck and the Kubernetes probes and preStop hook; the
# plain admin listener only binds loopback.
RUN apt-get update \
    && apt-get install -y --no-install-recommends ca-certificates curl \
    && rm -rf /var/lib/apt/lists/* \
    && groupadd --system --gid 10001 logkeeper \
    && useradd --system --uid 10001 --gid 10001 --home-dir /var/lib/logkeeper \
        --shell /usr/sbin/nologin logkeeper \
    && install -d -o 10001 -g 10001 -m 0700 \
        /var/lib/logkeeper /var/lib/logkeeper/media /var/lib/logkeeper/registry
COPY --from=build /usr/local/bin/logkeeper /usr/local/bin/logkeeper
USER 10001:10001
# Media (WAL, segments, snapshots) and the enrollment registry live on
# separate volumes: the registry must survive loss of the media.
VOLUME ["/var/lib/logkeeper/media", "/var/lib/logkeeper/registry"]
# Application, control (peer) and bulk lanes.
EXPOSE 5441/tcp 5541/tcp 5641/tcp
HEALTHCHECK --interval=10s --timeout=3s --start-period=120s --retries=3 \
    CMD curl -fsS -o /dev/null http://127.0.0.1:5741/live || exit 1
STOPSIGNAL SIGTERM
ENTRYPOINT ["/usr/local/bin/logkeeper", "keeper"]
CMD ["--config", "/etc/logkeeper/keeper.json"]
