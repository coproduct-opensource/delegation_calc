//! The purity tripwire: the shell schedules, it never computes state.
//!
//! `spec/r6-1-node-design.md` §0 and §7.4. The whole value of this crate rests on
//! every model-state transition being a call into a function the R2
//! correspondence proved refines the Lean model. That property is invisible to
//! the type system and easy to void with one convenient inline update, so it is
//! asserted here over the crate's own source: a future edit that assigns to a
//! store, an `applied` counter or a log — or that replaces the view with
//! anything other than a verified transition — fails the build instead of
//! silently turning the transported guarantees into decoration.
//!
//! This is a tripwire, not a proof of purity (it greps text). It catches the
//! shape the mistake actually takes.

const LIB: &str = include_str!("../src/lib.rs");
const NET: &str = include_str!("../src/net.rs");
const MAIN: &str = include_str!("../src/main.rs");
const DEMO: &str = include_str!("../src/demo.rs");
const AUTH: &str = include_str!("../src/auth.rs");
const NETAUTH: &str = include_str!("../src/netauth.rs");

fn sources() -> [(&'static str, &'static str); 6] {
    [
        ("src/lib.rs", LIB),
        ("src/net.rs", NET),
        ("src/main.rs", MAIN),
        ("src/demo.rs", DEMO),
        // The authenticated node also transitions model state, and only through
        // `commit`/`world_step` — the tripwire scans it too.
        ("src/auth.rs", AUTH),
        // The async authenticated transport: must carry bytes via `codec`, never
        // grow its own encoder.
        ("src/netauth.rs", NETAUTH),
    ]
}

/// Assignment forms only — struct-literal initialisation (`store: …`) is how
/// `Node::new` legitimately seeds the view, and `store ==` is a comparison, not a
/// mutation. Distinguishing those is the whole content of this predicate: a
/// tripwire that fires on `==` would be red for the wrong reason and would be
/// silenced rather than fixed.
fn assigns(code: &str, pat: &str) -> bool {
    let mut rest = code;
    while let Some(i) = rest.find(pat) {
        let after = &rest[i + pat.len()..];
        if !after.starts_with('=') {
            return true;
        }
        rest = &rest[i + pat.len()..];
    }
    false
}

const FORBIDDEN: [&str; 6] = [
    ".store =",
    ".applied =",
    ".log =",
    ".replicas =",
    ".log.push",
    ".replicas.push",
];

/// The detector fires on a real violation and stays quiet on the legitimate
/// forms. Without this, a broken predicate would report a green purity check
/// over any source at all.
#[test]
fn the_detector_actually_detects() {
    // Genuine violations.
    assert!(assigns("self.view.replicas[0].store = t;", ".store ="));
    assert!(assigns("r.applied = r.applied + 1;", ".applied ="));
    assert!(assigns("self.view.log.push(cmd);", ".log.push"));
    // Legitimate forms that must NOT trip it.
    assert!(!assigns("v.replicas[0].store == first.store", ".store ="));
    assert!(!assigns(
        "Replica { id, store: init, applied: 0 }",
        ".store ="
    ));
    assert!(!assigns("replicas.push(r.clone())", ".replicas.push"));
}

/// No model-state field is ever assigned in the shell.
#[test]
fn shell_never_assigns_model_state() {
    for (name, src) in sources() {
        for (n, line) in src.lines().enumerate() {
            let code = line.split("//").next().unwrap_or(line);
            for pat in FORBIDDEN {
                assert!(
                    !assigns(code, pat),
                    "{name}:{}: shell assigns model state (`{pat}`) — \
                     every transition must go through dlc_core::rsm",
                    n + 1
                );
            }
        }
    }
}

/// The view is only ever replaced by a verified transition.
///
/// Every `self.view = …` in the crate must be produced by `dlc_core::rsm::commit`
/// or `dlc_core::rsm::world_step` — the two functions covered by
/// `rust_capability_safety` and `rust_world_step_correct` respectively.
#[test]
fn view_is_only_replaced_by_verified_transitions() {
    let mut assignments = 0;
    for (name, src) in sources() {
        for (n, line) in src.lines().enumerate() {
            let code = line.split("//").next().unwrap_or(line);
            if !code.contains("self.view =") {
                continue;
            }
            assignments += 1;
            let verified =
                code.contains("commit(&self.view") || code.contains("world_step(&self.view)");
            assert!(
                verified,
                "{name}:{}: the view is replaced by something other than a \
                 verified transition: {}",
                n + 1,
                code.trim()
            );
        }
    }
    // The check must actually be checking something. Two per node type
    // (`Node::apply_commit` and `AuthNode::apply_commit`, each a
    // commit-then-drain-via-world_step pair) = 4.
    assert_eq!(
        assignments, 4,
        "expected exactly the commit and world_step transitions in Node and \
         AuthNode; if a transition was added, verify it is corresponded and \
         update this count"
    );
}

/// The SHELL introduces no term encoding of its own.
///
/// Scope note (updated for R6.1b): this scans the shell + transport files via
/// `sources()`. It deliberately does NOT scan the two legitimate encoders:
/// `proto.rs` (the authenticated protocol layer — signed framing, now that the
/// Tamarin + ProVerif models exist) and `codec.rs` (the `AuthMsg` wire frame).
/// Both encode terms by REUSING `dlc_protocol::wire` — the same encoder
/// `says`-credentials are signed under — rather than inventing a second canonical
/// form. What this test guards is that the shell and the async transport never
/// grow their OWN ad-hoc encoder: `netauth.rs` must carry bytes through `codec`,
/// the scheduler must not `serde`/`ciborium` anything itself.
#[test]
fn shell_introduces_no_term_encoding() {
    let forbidden = ["serde", "ciborium", "to_bytes", "from_bytes", "serialize"];
    for (name, src) in sources() {
        for (n, line) in src.lines().enumerate() {
            let code = line.split("//").next().unwrap_or(line);
            for pat in forbidden {
                assert!(
                    !code.contains(pat),
                    "{name}:{}: `{pat}` — a wire encoding needs a Tamarin model first",
                    n + 1
                );
            }
        }
    }
}
