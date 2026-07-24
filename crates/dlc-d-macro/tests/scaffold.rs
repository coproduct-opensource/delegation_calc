//! Scaffold-level checks: the `#[agent_service]` attribute applies to items and is a no-op
//! pass-through at this increment. (Envelope-enforcement fixtures — good programs compile,
//! the three violation classes fail — arrive with the Tier-1/Tier-2 increments via `trybuild`.)

use dlc_d_macro::agent_service;

#[agent_service(cap = Invoke<Tool> @ issuer, flow = chi <= l_low, budget = Faults<1>)]
fn governed_agent() -> u32 {
    42
}

#[agent_service]
struct GovernedService;

#[test]
fn scaffold_passes_through_fn() {
    assert_eq!(governed_agent(), 42);
}

#[test]
fn scaffold_passes_through_item() {
    let _ = GovernedService;
}
