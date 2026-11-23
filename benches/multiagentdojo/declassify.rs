//! When a sink argument of a tainted agent may still pass: the value is one no injection could
//! have chosen, because it is syntactically harmless or anchored in the user's prompt or in a
//! lookup result that third parties cannot write.

use std::collections::HashSet;

use serde_json::Value;

/// What an argument does when its value is chosen by an attacker.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Role {
    Email,
    Iban,
    Id,
    Url,
    Date,
    DateTime,
    Number,
    /// A user-named value: the whole value must appear in the prompt.
    Text,
    /// Message content: every actionable identifier in it must be anchored.
    Free,
    /// No effect an attacker gains.
    Open,
}

/// The role of every argument of every `tools::SINKS` entry; unknown keys are `Text`.
pub fn role(tool: &str, key: &str) -> Role {
    const PAYMENTS: [&str; 3] = [
        "send_money",
        "schedule_transaction",
        "update_scheduled_transaction",
    ];
    let payment = PAYMENTS.contains(&tool);
    match (tool, key) {
        ("send_email", "recipients" | "cc" | "bcc")
        | ("create_calendar_event" | "add_calendar_event_participants", "participants")
        | ("share_file", "email")
        | ("invite_user_to_slack", "user_email") => Role::Email,
        (_, "recipient") if payment => Role::Iban,
        ("delete_email", "email_id")
        | (
            "cancel_calendar_event"
            | "reschedule_calendar_event"
            | "add_calendar_event_participants",
            "event_id",
        )
        | ("append_to_file" | "delete_file" | "share_file", "file_id")
        | ("update_scheduled_transaction", "id") => Role::Id,
        ("get_webpage" | "post_webpage", "url") => Role::Url,
        ("reserve_hotel", "start_day" | "end_day") => Role::Date,
        (_, "date") if payment => Role::Date,
        ("reserve_restaurant", "start_time")
        | ("reserve_car_rental" | "create_calendar_event", "start_time" | "end_time")
        | ("reschedule_calendar_event", "new_start_time" | "new_end_time") => Role::DateTime,
        (_, "amount") if payment => Role::Number,
        ("send_email", "subject" | "body" | "attachments")
        | ("append_to_file" | "post_webpage", "content")
        | ("send_direct_message" | "send_channel_message", "body") => Role::Free,
        (_, "subject") if payment => Role::Free,
        ("create_file", "filename" | "content")
        | ("schedule_transaction" | "update_scheduled_transaction", "recurring")
        | ("share_file", "permission") => Role::Open,
        _ => Role::Text,
    }
}

/// Static lookups whose results no sink can write; their values anchor tainted arguments.
pub const ANCHOR_LOOKUPS: &[&str] = &[
    "search_contacts_by_name",
    "search_contacts_by_email",
    "get_current_day",
    "get_iban",
    "get_balance",
    "get_user_info",
    "get_scheduled_transactions",
    "get_user_information",
    "get_flight_information",
    "get_all_hotels_in_city",
    "get_hotels_prices",
    "get_hotels_address",
    "get_all_restaurants_in_city",
    "get_cuisine_type_for_restaurants",
    "get_restaurants_address",
    "get_dietary_restrictions_for_all_restaurants",
    "get_contact_information_for_restaurants",
    "get_price_for_restaurants",
    "check_restaurant_opening_hours",
    "get_all_car_rental_companies_in_city",
    "get_car_types_available",
    "get_car_fuel_options",
    "get_car_rental_address",
    "get_car_price_per_day",
];

/// Sinks whose result is an environment record that may hold third-party text.
pub const ECHO_SINKS: &[&str] = &[
    "reschedule_calendar_event",
    "add_calendar_event_participants",
    "append_to_file",
    "share_file",
    "delete_file",
];

/// One task's anchors, shared by every agent: the prompt and the trusted lookup results.
pub struct Anchors {
    prompt: String,
    prompt_words: HashSet<String>,
    trusted_words: HashSet<String>,
}

impl Anchors {
    pub fn new(prompt: &str) -> Self {
        let prompt = prompt.to_lowercase();
        let mut prompt_words = HashSet::new();
        add_words(&prompt, &mut prompt_words);
        Self {
            prompt,
            prompt_words,
            trusted_words: HashSet::new(),
        }
    }

    /// Records a trusted lookup result: every key, string and number in it.
    pub fn record(&mut self, value: &Value) {
        match value {
            Value::String(text) => add_words(&text.to_lowercase(), &mut self.trusted_words),
            Value::Number(number) => {
                self.trusted_words.insert(number.to_string());
            }
            Value::Array(items) => items.iter().for_each(|item| self.record(item)),
            Value::Object(fields) => fields.iter().for_each(|(key, item)| {
                add_words(&key.to_lowercase(), &mut self.trusted_words);
                self.record(item);
            }),
            Value::Null | Value::Bool(_) => {}
        }
    }

    /// Whether a scalar (a string, or a number's decimal form) is anchored for `role`.
    pub fn anchored(&self, role: Role, value: &str) -> bool {
        let text = value.trim().to_lowercase();
        let either =
            |word: &str| self.prompt_words.contains(word) || self.trusted_words.contains(word);
        match role {
            Role::Text => text.is_empty() || (text.len() >= 3 && self.prompt.contains(&text)),
            Role::Email => either(&text),
            Role::Url => either(&text) || either(url_key(&text)),
            Role::Iban => either(&text.replace(' ', "")),
            Role::Id => self.trusted_words.contains(&text),
            Role::Date | Role::DateTime | Role::Number | Role::Free | Role::Open => false,
        }
    }
}

/// Indexes each token of `text`, each identifier found inside it, and each URL without its scheme.
fn add_words(text: &str, words: &mut HashSet<String>) {
    for token in tokens(text) {
        words.insert(token.to_owned());
    }
    for identifier in identifiers(text) {
        words.insert(url_key(&identifier).to_owned());
        words.insert(identifier);
    }
}

/// A URL without `http://` or `https://`, so `www.x.com` anchors `https://www.x.com`.
fn url_key(url: &str) -> &str {
    url.strip_prefix("https://")
        .or_else(|| url.strip_prefix("http://"))
        .unwrap_or(url)
}

fn is_separator(c: char) -> bool {
    c.is_whitespace() || ",;()<>[]{}\"'|`".contains(c)
}

/// Whitespace- and punctuation-separated words with trailing sentence punctuation removed.
fn tokens(text: &str) -> impl Iterator<Item = &str> {
    text.split(is_separator)
        .map(|token| token.trim_end_matches(['.', ':', '!', '?']))
        .filter(|token| !token.is_empty())
}

/// Actionable identifiers anywhere in `text` (lowercased): email addresses, URLs starting with
/// `http://`, `https://` or `www.`, IBANs, and the whole text without whitespace if it is an IBAN.
/// Found by scanning, not tokenizing, so `see:www.x.com` still yields `www.x.com`.
fn identifiers(text: &str) -> Vec<String> {
    let lower = text.to_lowercase();
    let bytes = lower.as_bytes();
    let mut found = Vec::new();
    for (at, _) in lower.match_indices('@') {
        let local = |b: u8| b.is_ascii_alphanumeric() || b"._%+-".contains(&b);
        let domain = |b: u8| b.is_ascii_alphanumeric() || b".-".contains(&b);
        let start = bytes[..at]
            .iter()
            .rposition(|&b| !local(b))
            .map_or(0, |i| i + 1);
        let end = bytes[at + 1..]
            .iter()
            .position(|&b| !domain(b))
            .map_or(bytes.len(), |i| at + 1 + i);
        let email = lower[start..end].trim_end_matches(['.', '-']);
        if is_email(email) {
            found.push(email.to_owned());
        }
    }
    let mut cursor = 0;
    while let Some(offset) = ["http://", "https://", "www."]
        .iter()
        .filter_map(|prefix| lower[cursor..].find(prefix))
        .min()
    {
        let start = cursor + offset;
        let end = lower[start..]
            .find(is_separator)
            .map_or(lower.len(), |i| start + i);
        let url = lower[start..end].trim_end_matches(['.', ':', '!', '?', ',']);
        if !url.is_empty() {
            found.push(url.to_owned());
        }
        cursor = end.max(start + 1);
    }
    for run in lower.split(|c: char| !c.is_ascii_alphanumeric()) {
        if is_iban(run) {
            found.push(run.to_owned());
        }
    }
    let compact: String = lower.chars().filter(|c| !c.is_whitespace()).collect();
    if is_iban(&compact) {
        found.push(compact);
    }
    found
}

/// Whether a tainted agent's argument may be declassified: its value cannot carry an injection's
/// goal. `enabled = false` is the taint-only ablation: only `Open` arguments pass.
pub fn endorse(
    role: Role,
    value: &Value,
    has_recipients: bool,
    anchors: &Anchors,
    enabled: bool,
) -> bool {
    if role == Role::Open {
        return true;
    }
    if !enabled {
        return false;
    }
    match value {
        Value::Null | Value::Bool(_) => true,
        Value::Array(items) => items
            .iter()
            .all(|item| endorse(role, item, has_recipients, anchors, true)),
        Value::Object(fields) => fields.iter().all(|(key, item)| {
            scalar(role, key, has_recipients, anchors)
                && endorse(role, item, has_recipients, anchors, true)
        }),
        Value::String(text) => scalar(role, text, has_recipients, anchors),
        Value::Number(number) => scalar(role, &number.to_string(), has_recipients, anchors),
    }
}

fn scalar(role: Role, text: &str, has_recipients: bool, anchors: &Anchors) -> bool {
    let text = text.trim();
    match role {
        Role::Date => is_date(text),
        Role::DateTime => is_datetime(text),
        Role::Number => is_number(text),
        Role::Email => is_email(text) && anchors.anchored(role, text),
        Role::Url => is_url(text) && anchors.anchored(role, text),
        Role::Iban => is_iban(text) && anchors.anchored(role, text),
        Role::Id | Role::Text => anchors.anchored(role, text),
        Role::Free if has_recipients => identifiers(text)
            .iter()
            .all(|identifier| anchors.anchored(identifier_role(identifier), identifier)),
        Role::Free => anchors.anchored(Role::Text, text),
        Role::Open => true,
    }
}

fn identifier_role(identifier: &str) -> Role {
    if is_email(identifier) {
        Role::Email
    } else if is_iban(identifier) {
        Role::Iban
    } else {
        Role::Url
    }
}

pub fn is_email(text: &str) -> bool {
    let text = text.trim();
    let mut parts = text.split('@');
    let (Some(local), Some(domain), None) = (parts.next(), parts.next(), parts.next()) else {
        return false;
    };
    !local.is_empty()
        && !local.contains(char::is_whitespace)
        && domain.contains('.')
        && !domain.starts_with('.')
        && !domain.ends_with('.')
        && domain
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b == b'.' || b == b'-')
}

pub fn is_iban(text: &str) -> bool {
    let compact: String = text.trim().chars().filter(|&c| c != ' ').collect();
    let bytes = compact.to_ascii_uppercase().into_bytes();
    (12..=34).contains(&bytes.len())
        && bytes[..2].iter().all(u8::is_ascii_uppercase)
        && bytes[2..4].iter().all(u8::is_ascii_digit)
        && bytes[4..]
            .iter()
            .all(|b| b.is_ascii_uppercase() || b.is_ascii_digit())
}

fn digits(text: &str) -> Option<u32> {
    text.bytes()
        .all(|b| b.is_ascii_digit())
        .then(|| text.parse().ok())
        .flatten()
}

pub fn is_date(text: &str) -> bool {
    let text = text.trim();
    let bytes = text.as_bytes();
    bytes.len() == 10
        && bytes[4] == b'-'
        && bytes[7] == b'-'
        && digits(&text[..4]).is_some()
        && digits(&text[5..7]).is_some_and(|month| (1..=12).contains(&month))
        && digits(&text[8..]).is_some_and(|day| (1..=31).contains(&day))
}

pub fn is_datetime(text: &str) -> bool {
    let text = text.trim();
    if text.len() <= 10 {
        return is_date(text);
    }
    let Some((date, time)) = text.split_at_checked(10) else {
        return false;
    };
    let Some(time) = time.strip_prefix(['T', ' ']) else {
        return false;
    };
    let mut fields = time.split(':');
    let hour = fields.next().filter(|f| f.len() == 2).and_then(digits);
    let minute = fields.next().filter(|f| f.len() == 2).and_then(digits);
    let second = fields
        .next()
        .map(|f| (f.len() == 2).then(|| digits(f)).flatten());
    is_date(date)
        && hour.is_some_and(|h| h < 24)
        && minute.is_some_and(|m| m < 60)
        && second.is_none_or(|s| s.is_some_and(|s| s < 60))
        && fields.next().is_none()
}

pub fn is_number(text: &str) -> bool {
    text.trim().parse::<f64>().is_ok_and(f64::is_finite)
}

pub fn is_url(text: &str) -> bool {
    let text = text.trim();
    if text.is_empty() || text.contains(char::is_whitespace) {
        return false;
    }
    let lower = text.to_lowercase();
    if ["http://", "https://", "www."]
        .iter()
        .any(|prefix| lower.starts_with(prefix))
    {
        return true;
    }
    let host = lower.split('/').next().unwrap_or_default();
    let Some((name, tld)) = host.rsplit_once('.') else {
        return false;
    };
    !name.is_empty()
        && name
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b == b'.' || b == b'-')
        && tld.len() >= 2
        && tld.bytes().all(|b| b.is_ascii_alphabetic())
}
