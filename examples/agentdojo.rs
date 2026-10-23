//! AgentDojo (ethz-spylab/agentdojo) tables for the replay harness in `common`.
//!
//! Usage: `cargo run --release --example agentdojo -- <runs-dir|log.json>`

mod common;

use common::Kind::{Fetch, Read, Sink};
use common::{Benchmark, Kind};

/// (tool name, kind, argument names that identify the destination / source object)
const TOOLS: &[(&str, Kind, &[&str])] = &[
    // workspace
    ("get_current_day", Read, &[]),
    ("get_unread_emails", Read, &[]),
    ("get_sent_emails", Read, &[]),
    ("get_received_emails", Read, &[]),
    ("get_draft_emails", Read, &[]),
    ("search_emails", Read, &[]),
    ("search_contacts_by_name", Read, &[]),
    ("search_contacts_by_email", Read, &[]),
    ("search_calendar_events", Read, &[]),
    ("get_day_calendar_events", Read, &[]),
    ("search_files_by_filename", Read, &[]),
    ("get_file_by_id", Read, &[]),
    ("list_files", Read, &[]),
    ("search_files", Read, &[]),
    ("send_email", Sink, &["recipients", "cc", "bcc"]),
    ("delete_email", Sink, &[]),
    ("create_calendar_event", Sink, &["participants"]),
    ("cancel_calendar_event", Sink, &[]),
    ("reschedule_calendar_event", Sink, &[]),
    ("add_calendar_event_participants", Sink, &["participants"]),
    ("append_to_file", Sink, &[]),
    ("create_file", Sink, &[]),
    ("delete_file", Sink, &[]),
    ("share_file", Sink, &["email"]),
    // slack
    ("get_channels", Read, &[]),
    ("read_channel_messages", Read, &[]),
    ("read_inbox", Read, &[]),
    ("get_users_in_channel", Read, &[]),
    ("get_webpage", Fetch, &["url"]),
    ("add_user_to_channel", Sink, &["user"]),
    ("send_direct_message", Sink, &["recipient"]),
    ("send_channel_message", Sink, &["channel"]),
    ("invite_user_to_slack", Sink, &["user_email"]),
    ("remove_user_from_slack", Sink, &["user"]),
    ("post_webpage", Sink, &["url"]),
    // travel (calendar and email tools shared with workspace above)
    ("get_user_information", Read, &[]),
    ("get_all_hotels_in_city", Read, &[]),
    ("get_hotels_prices", Read, &[]),
    ("get_rating_reviews_for_hotels", Read, &[]),
    ("get_hotels_address", Read, &[]),
    ("get_all_restaurants_in_city", Read, &[]),
    ("get_cuisine_type_for_restaurants", Read, &[]),
    ("get_restaurants_address", Read, &[]),
    ("get_rating_reviews_for_restaurants", Read, &[]),
    ("get_dietary_restrictions_for_all_restaurants", Read, &[]),
    ("get_contact_information_for_restaurants", Read, &[]),
    ("get_price_for_restaurants", Read, &[]),
    ("check_restaurant_opening_hours", Read, &[]),
    ("get_all_car_rental_companies_in_city", Read, &[]),
    ("get_car_types_available", Read, &[]),
    ("get_rating_reviews_for_car_rental", Read, &[]),
    ("get_car_fuel_options", Read, &[]),
    ("get_car_rental_address", Read, &[]),
    ("get_car_price_per_day", Read, &[]),
    ("get_flight_information", Read, &[]),
    ("reserve_hotel", Sink, &["hotel"]),
    ("reserve_restaurant", Sink, &["restaurant"]),
    ("reserve_car_rental", Sink, &["company"]),
    // banking
    ("get_iban", Read, &[]),
    ("get_balance", Read, &[]),
    ("get_most_recent_transactions", Read, &[]),
    ("get_scheduled_transactions", Read, &[]),
    ("read_file", Read, &["file_path"]),
    ("get_user_info", Read, &[]),
    ("send_money", Sink, &["recipient"]),
    ("schedule_transaction", Sink, &["recipient"]),
    ("update_scheduled_transaction", Sink, &["recipient"]),
    ("update_password", Sink, &[]),
    ("update_user_info", Sink, &[]),
];

/// Reads whose results carry other parties' text (every AgentDojo injection vector lives in one
/// of these). Keys are `tool:destination` with `/` replaced by `|`.
const UNTRUSTED_SOURCES: &[&str] = &[
    // workspace: received mail bodies, calendar descriptions, drive file contents
    "get_unread_emails:*",
    "get_received_emails:*",
    "search_emails:*",
    "search_calendar_events:*",
    "get_day_calendar_events:*",
    "search_files_by_filename:*",
    "get_file_by_id:*",
    "list_files:*",
    "search_files:*",
    // slack: web pages, channel names/messages, inbox
    "get_webpage:*",
    "get_channels:*",
    "read_channel_messages:*",
    "read_inbox:*",
    // travel: reviews
    "get_rating_reviews_for_hotels:*",
    "get_rating_reviews_for_restaurants:*",
    "get_rating_reviews_for_car_rental:*",
    // banking: counterparty transaction subjects, uploaded files
    "get_most_recent_transactions:*",
    "read_file:*",
];

fn main() {
    common::run(&Benchmark {
        tools: TOOLS,
        untrusted_sources: UNTRUSTED_SOURCES,
    });
}
