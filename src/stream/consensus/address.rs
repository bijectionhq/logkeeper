//! A keeper's network address in the inventory: `IP:port` or `name:port`.
//!
//! A DNS name resolves at every connect, so a keeper that moves to a new IP
//! (a rescheduled Kubernetes pod) is found again under the same name. The
//! name is never trusted for identity: every connection checks the keeper
//! URI in the certificate the peer presents against the keeper it meant to
//! reach.

use std::{
    fmt, io,
    net::{IpAddr, Ipv4Addr, SocketAddr},
    str::FromStr,
};

use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// `IP:port` (in canonical `SocketAddr` form) or a lowercased
/// `name:port`. Ordered and compared as text, so two spellings of one IP
/// address are equal and a name never equals an IP.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Address(String);

impl Address {
    pub fn parse(text: &str) -> io::Result<Self> {
        let invalid = || {
            io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("invalid keeper address {text:?}: expected IP:port or name:port"),
            )
        };
        if let Ok(address) = text.parse::<SocketAddr>() {
            return if address.port() == 0 {
                Err(invalid())
            } else {
                Ok(Self(address.to_string()))
            };
        }
        let (host, port) = text.rsplit_once(':').ok_or_else(invalid)?;
        let port = port.parse::<u16>().map_err(|_| invalid())?;
        if port == 0 || !valid_name(host) {
            return Err(invalid());
        }
        Ok(Self(format!("{}:{port}", host.to_ascii_lowercase())))
    }

    /// The address itself when it is an IP address.
    pub fn socket_addr(&self) -> Option<SocketAddr> {
        self.0.parse().ok()
    }

    /// Whether the address is a DNS name, resolved at each connect.
    pub fn is_name(&self) -> bool {
        self.socket_addr().is_none()
    }

    pub fn port(&self) -> u16 {
        match self.socket_addr() {
            Some(address) => address.port(),
            None => self
                .0
                .rsplit_once(':')
                .and_then(|(_, port)| port.parse().ok())
                .unwrap_or_default(),
        }
    }

    /// Where a keeper listens for this, its own inventory address: the IP
    /// address itself, or every interface on its port for a DNS name, whose
    /// IP the keeper may not know before the name is published (IPv4).
    pub fn bind_addr(&self) -> SocketAddr {
        self.socket_addr()
            .unwrap_or_else(|| SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), self.port()))
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// An RFC 1123 host name: dot-separated labels of letters, digits and
/// hyphens, none empty, none starting or ending with a hyphen.
fn valid_name(host: &str) -> bool {
    !host.is_empty()
        && host.len() <= 253
        && host.split('.').all(|label| {
            !label.is_empty()
                && label.len() <= 63
                && !label.starts_with('-')
                && !label.ends_with('-')
                && label.bytes().all(|byte| byte.is_ascii_alphanumeric() || byte == b'-')
        })
        // A name of digits and dots only is a malformed IP address.
        && !host.bytes().all(|byte| byte.is_ascii_digit() || byte == b'.')
}

impl fmt::Display for Address {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl FromStr for Address {
    type Err = io::Error;

    fn from_str(text: &str) -> io::Result<Self> {
        Self::parse(text)
    }
}

impl From<SocketAddr> for Address {
    fn from(address: SocketAddr) -> Self {
        Self(address.to_string())
    }
}

impl PartialEq<SocketAddr> for Address {
    fn eq(&self, other: &SocketAddr) -> bool {
        self.socket_addr() == Some(*other)
    }
}

impl Serialize for Address {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&self.0)
    }
}

impl<'de> Deserialize<'de> for Address {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let text = String::deserialize(deserializer)?;
        Self::parse(&text).map_err(serde::de::Error::custom)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_ip_and_name_addresses() {
        let ip = Address::parse("10.0.1.10:5441").unwrap();
        assert_eq!(ip.socket_addr(), Some("10.0.1.10:5441".parse().unwrap()));
        assert!(!ip.is_name());
        assert_eq!(ip.bind_addr(), "10.0.1.10:5441".parse().unwrap());
        let v6 = Address::parse("[::1]:7000").unwrap();
        assert_eq!(v6.as_str(), "[::1]:7000");

        let name = Address::parse("Keeper-0.Logkeeper.svc.cluster.local:5441").unwrap();
        assert!(name.is_name());
        assert_eq!(name.as_str(), "keeper-0.logkeeper.svc.cluster.local:5441");
        assert_eq!(name.port(), 5441);
        assert_eq!(name.bind_addr().port(), 5441);
        assert!(name.bind_addr().ip().is_unspecified());

        for bad in [
            "",
            "keeper",
            "keeper:0",
            "keeper:70000",
            ":5441",
            "-keeper:5441",
            "keeper..svc:5441",
            "kee per:5441",
            "10.0.1:5441",
            "10.0.1.10:0",
            "keeper_0:5441",
        ] {
            assert!(Address::parse(bad).is_err(), "{bad}");
        }
        let json: Address = serde_json::from_str("\"keeper-1:5441\"").unwrap();
        assert_eq!(serde_json::to_string(&json).unwrap(), "\"keeper-1:5441\"");
        assert!(serde_json::from_str::<Address>("\"keeper-1\"").is_err());
    }
}
