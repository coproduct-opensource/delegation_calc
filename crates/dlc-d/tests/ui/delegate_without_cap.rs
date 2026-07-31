//! The `delegate = attenuate_only` axis declares a posture ABOUT the issuer — without a `cap`
//! axis there is no issuer to certify, and the macro says so at the axis rather than emitting
//! nothing (an axis that silently lowers to nothing is the vacuity this fabric exists to kill).
use dlc_d::agent_service;

#[agent_service(delegate = attenuate_only)]
fn ungoverned() -> u32 {
    1
}

fn main() {}
