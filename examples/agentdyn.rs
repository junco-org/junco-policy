//! AgentDyn (SaFo-Lab/AgentDyn) tables for the replay harness in `common`.
//!
//! Same convention as the AgentDojo tables: state mutations and outbound transfers are sinks,
//! queries are reads, web contacts that return content are fetches. `login_*` and the OTP calls
//! (`verify_*`) are reads: credentials go to the user's own platform, and an OTP completes a sink
//! already judged when it was issued.
//!
//! Usage: `cargo run --release --example agentdyn -- <runs-dir|log.json>`

mod common;

use common::Kind::{Fetch, Read, Sink};
use common::{Benchmark, Kind};

/// (tool name, kind, argument names that identify the destination / source object)
const TOOLS: &[(&str, Kind, &[&str])] = &[
    // shared: mail, files, calendar, web, bank
    ("send_email", Sink, &["recipients", "cc", "bcc"]),
    ("get_unread_emails", Read, &[]),
    ("get_received_emails", Read, &[]),
    ("get_sent_emails", Read, &[]),
    ("search_emails", Read, &[]),
    ("delete_email", Sink, &[]),
    ("list_directory", Read, &["path"]),
    ("read_file", Read, &["path"]),
    ("create_file", Sink, &["path"]),
    ("create_dir", Sink, &["path"]),
    ("delete_node", Sink, &["path"]),
    ("copy_node", Sink, &["destination_path"]),
    ("move_node", Sink, &["destination_path"]),
    ("browse_webpage", Fetch, &["url"]),
    ("input_to_webpage", Fetch, &["url"]),
    ("download_file_through_url", Fetch, &["url"]),
    ("download_file_through_id", Fetch, &["file_id"]),
    ("get_current_day", Read, &[]),
    ("get_day_calendar_events", Read, &[]),
    ("search_calendar_events", Read, &[]),
    ("create_calendar_event", Sink, &["participants"]),
    ("add_calendar_event_participants", Sink, &["participants"]),
    ("cancel_calendar_event", Sink, &[]),
    ("reschedule_calendar_event", Sink, &[]),
    ("send_money", Sink, &["recipient"]),
    ("get_balance", Read, &[]),
    ("verify_transaction", Read, &[]),
    // shopping
    ("login_shopping_account", Read, &[]),
    ("verify_shopping_account", Read, &[]),
    ("get_shopping_account_user_information", Read, &[]),
    ("update_shopping_account_password", Sink, &[]),
    ("update_shopping_account_user_info", Sink, &[]),
    ("get_shopping_linked_unread_emails", Read, &[]),
    ("get_shopping_linked_received_emails", Read, &[]),
    ("search_product", Read, &[]),
    ("view_order_history", Read, &[]),
    ("get_invoice", Read, &["order_id"]),
    ("refund_order", Sink, &["order_id"]),
    ("view_cart", Read, &[]),
    ("cart_total", Read, &[]),
    ("view_available_discounts", Read, &[]),
    ("cart_add_product", Sink, &["product_id"]),
    ("cart_remove_product", Sink, &["product_id"]),
    ("clear_cart", Sink, &[]),
    ("checkout_selected_cart", Sink, &["product_ids"]),
    // github
    ("login_github_account", Read, &[]),
    ("verify_github_account", Read, &[]),
    ("get_github_linked_unread_emails", Read, &[]),
    ("get_logged_in_github_user_information", Read, &[]),
    (
        "get_github_account_user_information",
        Read,
        &["username", "email"],
    ),
    ("get_github_repository_information", Read, &["repo_name"]),
    ("git_get_linked_ssh_keys", Read, &[]),
    ("git_clone", Fetch, &["repo_name"]),
    ("git_pull", Fetch, &["repo_name"]),
    // a rejected push returns the conflicting file contents
    ("git_push", Fetch, &["local_path"]),
    ("update_github_account_password", Sink, &[]),
    ("git_create_repo", Sink, &["repo_name"]),
    ("git_delete_repo", Sink, &["repo_name"]),
    (
        "git_transfer_repo_ownership",
        Sink,
        &["new_owner_username", "new_owner_email"],
    ),
    ("git_invite_collaborators", Sink, &["collaborator_email"]),
    ("git_issue", Sink, &["repo_name"]),
    ("git_star", Sink, &["repo_name"]),
    ("git_unstar", Sink, &["repo_name"]),
    ("git_add_ssh_key", Sink, &[]),
    ("git_delete_ssh_key", Sink, &[]),
];

/// Reads whose results carry other parties' text (every AgentDyn injection vector lives in one
/// of these). Keys are `tool:destination` with `/` replaced by `|`.
const UNTRUSTED_SOURCES: &[&str] = &[
    // mail: inbox bodies (the OTP mails share the inbox with injected mails)
    "get_unread_emails:*",
    "get_received_emails:*",
    "search_emails:*",
    "get_shopping_linked_unread_emails:*",
    "get_shopping_linked_received_emails:*",
    "get_github_linked_unread_emails:*",
    // web: pages, form responses, downloads
    "browse_webpage:*",
    "input_to_webpage:*",
    "download_file_through_url:*",
    "download_file_through_id:*",
    // files: downloads, invoices, planted notes, cloned repositories, push conflicts
    "read_file:*",
    "git_clone:*",
    "git_pull:*",
    "git_push:*",
    // calendar descriptions
    "search_calendar_events:*",
    "get_day_calendar_events:*",
    // platform content written by others: product reviews, repository README/issues
    "search_product:*",
    "get_github_repository_information:*",
];

fn main() {
    common::run(&Benchmark {
        tools: TOOLS,
        untrusted_sources: UNTRUSTED_SOURCES,
    });
}
