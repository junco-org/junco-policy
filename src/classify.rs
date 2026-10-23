//! Resource classifiers: first-match tables from concrete resources to the class labels rules
//! speak about.
//!
//! Rules over individual resources grow with the resources a principal touches. Rules over
//! *classes* (`secret`, `tests`, `external`) stay fixed: a caller classifies each concrete
//! resource it observes and builds its events from the class. A [`Classifier`] is an ordered table
//! of `(matcher, class)` entries whose first matching entry wins, with an optional fallback class
//! for resources no entry matches. [`Glob`] matches paths and [`Network`] matches IP addresses;
//! any other [`Matcher`] can be classified the same way.

use std::fmt;
use std::net::IpAddr;
use std::path::Path;

/// Decides whether a concrete resource belongs to one entry of a [`Classifier`].
pub trait Matcher<T: ?Sized> {
    /// Whether `value` matches.
    fn matches(&self, value: &T) -> bool;
}

/// An ordered first-match table from resources to classes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Classifier<M, C> {
    entries: Vec<(M, C)>,
    fallback: Option<C>,
}

impl<M, C> Default for Classifier<M, C> {
    fn default() -> Self {
        Self {
            entries: Vec::new(),
            fallback: None,
        }
    }
}

impl<M, C: Copy> Classifier<M, C> {
    /// A table with no entries: it classifies nothing.
    pub fn new() -> Self {
        Self::default()
    }

    /// A table whose unmatched resources fall back to `class`.
    pub fn with_fallback(class: C) -> Self {
        Self {
            entries: Vec::new(),
            fallback: Some(class),
        }
    }

    /// Appends an entry; earlier entries take precedence.
    #[must_use]
    pub fn class(mut self, matcher: M, class: C) -> Self {
        self.entries.push((matcher, class));
        self
    }

    /// The class of the first entry matching `value`, else the fallback, if any.
    pub fn classify<T: ?Sized>(&self, value: &T) -> Option<C>
    where
        M: Matcher<T>,
    {
        self.entries
            .iter()
            .find(|(matcher, _)| matcher.matches(value))
            .map_or(self.fallback, |&(_, class)| Some(class))
    }

    /// The entries in precedence order.
    pub fn entries(&self) -> impl Iterator<Item = (&M, C)> {
        self.entries
            .iter()
            .map(|(matcher, class)| (matcher, *class))
    }

    /// The class of resources no entry matches.
    pub const fn fallback(&self) -> Option<C> {
        self.fallback
    }
}

/// A path glob: `*` and `?` stay within one path component and `**` spans any number of them.
/// Matching is case-sensitive; a leading `.` needs no literal match.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Glob(glob::Pattern);

const GLOB_OPTIONS: glob::MatchOptions = glob::MatchOptions {
    case_sensitive: true,
    require_literal_separator: true,
    require_literal_leading_dot: false,
};

impl Glob {
    /// Compiles `pattern`.
    ///
    /// # Errors
    /// When `pattern` is not a valid glob.
    pub fn new(pattern: &str) -> Result<Self, InvalidPattern> {
        glob::Pattern::new(pattern)
            .map(Self)
            .map_err(|error| InvalidPattern(format!("invalid glob {pattern:?}: {error}")))
    }

    /// The source pattern.
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

impl Matcher<Path> for Glob {
    fn matches(&self, value: &Path) -> bool {
        self.0.matches_path_with(value, GLOB_OPTIONS)
    }
}

impl Matcher<str> for Glob {
    fn matches(&self, value: &str) -> bool {
        self.0.matches_with(value, GLOB_OPTIONS)
    }
}

/// An IPv4 or IPv6 network in CIDR form. An IPv4-mapped IPv6 address is matched as its IPv4
/// address, so `::ffff:10.0.0.1` is inside `10.0.0.0/8`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Network {
    address: IpAddr,
    prefix: u8,
}

impl Network {
    /// Parses `address` or `address/prefix`; a bare address is a single-host network.
    ///
    /// # Errors
    /// When the address does not parse or the prefix exceeds the family's width.
    pub fn parse(text: &str) -> Result<Self, InvalidPattern> {
        let invalid = || InvalidPattern(format!("invalid network {text:?}"));
        let (address, prefix) = text
            .split_once('/')
            .map_or((text, None), |(address, prefix)| (address, Some(prefix)));
        let address: IpAddr = address.parse().map_err(|_| invalid())?;
        let width = if address.is_ipv4() { 32 } else { 128 };
        let prefix = prefix.map_or(Ok(width), |prefix| prefix.parse().map_err(|_| invalid()))?;
        if prefix > width {
            return Err(invalid());
        }
        Ok(Self {
            address: address.to_canonical(),
            prefix,
        })
    }

    /// Whether `address` lies inside this network.
    pub fn contains(&self, address: IpAddr) -> bool {
        match (self.address, address.to_canonical()) {
            (IpAddr::V4(network), IpAddr::V4(address)) => {
                prefix_equal(&network.octets(), &address.octets(), self.prefix)
            }
            (IpAddr::V6(network), IpAddr::V6(address)) => {
                prefix_equal(&network.octets(), &address.octets(), self.prefix)
            }
            _ => false,
        }
    }
}

impl fmt::Display for Network {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}/{}", self.address, self.prefix)
    }
}

impl Matcher<IpAddr> for Network {
    fn matches(&self, value: &IpAddr) -> bool {
        self.contains(*value)
    }
}

/// Whether the first `prefix` bits of `left` and `right` agree.
fn prefix_equal(left: &[u8], right: &[u8], prefix: u8) -> bool {
    let full = usize::from(prefix / 8);
    let bits = prefix % 8;
    left[..full] == right[..full]
        && (bits == 0 || (left[full] ^ right[full]) & (0xff << (8 - bits)) == 0)
}

/// A malformed glob or network.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
#[error("{0}")]
pub struct InvalidPattern(String);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_first_matching_entry_wins_and_unmatched_resources_fall_back() {
        let paths = Classifier::with_fallback("src")
            .class(Glob::new("**/.env").unwrap(), "secret")
            .class(Glob::new("tests/**").unwrap(), "tests")
            .class(Glob::new("**/*.env").unwrap(), "config");
        assert_eq!(paths.classify(Path::new("deploy/.env")), Some("secret"));
        assert_eq!(paths.classify(Path::new("tests/a/b.rs")), Some("tests"));
        assert_eq!(paths.classify(Path::new("tests/.env")), Some("secret"));
        assert_eq!(paths.classify(Path::new("lib.rs")), Some("src"));
        let outside = Classifier::new().class(Glob::new("/etc/shadow").unwrap(), "secret");
        assert_eq!(outside.classify(Path::new("/etc/passwd")), None);
    }

    #[test]
    fn globs_keep_single_stars_within_one_component() {
        let glob = Glob::new("src/*.rs").unwrap();
        assert!(glob.matches(Path::new("src/lib.rs")));
        assert!(!glob.matches(Path::new("src/shell/mod.rs")));
        assert!(Glob::new("*").unwrap().matches(".hidden"));
        assert!(Glob::new("[").is_err());
    }

    #[test]
    fn networks_match_by_prefix_and_mapped_ipv4_as_ipv4() {
        let private = Network::parse("10.0.0.0/8").unwrap();
        let ip = |text: &str| text.parse::<IpAddr>().unwrap();
        assert!(private.contains(ip("10.1.2.3")));
        assert!(!private.contains(ip("11.0.0.1")));
        assert!(private.contains(ip("::ffff:10.0.0.1")));
        assert!(!private.contains(ip("::a00:1")));
        let narrow = Network::parse("192.168.1.128/25").unwrap();
        assert!(narrow.contains(ip("192.168.1.200")));
        assert!(!narrow.contains(ip("192.168.1.127")));
        let documentation = Network::parse("2001:db8::/32").unwrap();
        assert!(documentation.contains(ip("2001:db8::1")));
        assert!(!documentation.contains(ip("2001:db9::1")));
        assert!(Network::parse("0.0.0.0/0").unwrap().contains(ip("8.8.8.8")));
        assert!(!Network::parse("0.0.0.0/0").unwrap().contains(ip("::1")));
        assert_eq!(
            Network::parse("10.0.0.1").unwrap().to_string(),
            "10.0.0.1/32"
        );
        for invalid in ["10.0.0.0/33", "::/129", "10.0.0/8", "10.0.0.0/x", "host"] {
            assert!(Network::parse(invalid).is_err(), "{invalid}");
        }
    }
}
