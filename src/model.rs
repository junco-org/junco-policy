use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Principal(String);

impl Principal {
    pub fn new(value: impl Into<String>) -> Self {
        Self(value.into())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl From<&str> for Principal {
    fn from(value: &str) -> Self {
        Self::new(value)
    }
}

impl From<String> for Principal {
    fn from(value: String) -> Self {
        Self(value)
    }
}

impl fmt::Display for Principal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Resource(Vec<String>);

impl Resource {
    pub fn new(segments: impl IntoIterator<Item = impl Into<String>>) -> Self {
        Self(segments.into_iter().map(Into::into).collect())
    }

    pub fn segments(&self) -> &[String] {
        &self.0
    }
}

impl<const N: usize> From<[&str; N]> for Resource {
    fn from(segments: [&str; N]) -> Self {
        Self::new(segments)
    }
}

impl From<Vec<&str>> for Resource {
    fn from(segments: Vec<&str>) -> Self {
        Self::new(segments)
    }
}

impl From<Vec<String>> for Resource {
    fn from(segments: Vec<String>) -> Self {
        Self(segments)
    }
}

impl fmt::Display for Resource {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0.join("/"))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Action {
    Read,
    Edit,
    Stage,
    Unstage,
    Commit { message: Option<String> },
    Checkout,
    Stash,
    Diff,
    History,
}

impl Action {
    pub fn commit(message: impl Into<String>) -> Self {
        Self::Commit {
            message: Some(message.into()),
        }
    }

    pub fn commit_without_message() -> Self {
        Self::Commit { message: None }
    }
}

impl fmt::Display for Action {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Read => f.write_str("read"),
            Self::Edit => f.write_str("edit"),
            Self::Stage => f.write_str("stage"),
            Self::Unstage => f.write_str("unstage"),
            Self::Commit {
                message: Some(message),
            } => write!(f, "commit({message:?})"),
            Self::Commit { message: None } => f.write_str("commit(<missing message>)"),
            Self::Checkout => f.write_str("checkout"),
            Self::Stash => f.write_str("stash"),
            Self::Diff => f.write_str("diff"),
            Self::History => f.write_str("history"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Event {
    pub principal: Principal,
    pub action: Action,
    pub resource: Resource,
}

impl Event {
    pub fn new(
        principal: impl Into<Principal>,
        action: Action,
        resource: impl Into<Resource>,
    ) -> Self {
        Self {
            principal: principal.into(),
            action,
            resource: resource.into(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Request<M> {
    pub event: Event,
    pub metadata: M,
}

impl<M> Request<M> {
    pub fn new(event: Event, metadata: M) -> Self {
        Self { event, metadata }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Grant<M> {
    pub event: Event,
    pub metadata: M,
}
