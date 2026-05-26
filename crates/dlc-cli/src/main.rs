//! `dlc` — DLC reference CLI.
//!
//! Two subcommands at GA: `dlc issue` (mint a proof term) and `dlc verify`
//! (check one). Week-1 stub prints help only.

fn main() {
    eprintln!("dlc — Delegation Logic Calculus CLI");
    eprintln!("usage: dlc <issue|verify> [options]");
    eprintln!();
    eprintln!("Week-1 skeleton; subcommands wired in at M3.M14.");
    std::process::exit(2);
}
