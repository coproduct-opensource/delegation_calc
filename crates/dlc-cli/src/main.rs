//! `dlc` — DLC reference CLI.
//!
//! Drives the end-to-end Phase-1 flow:
//!
//! ```text
//! dlc keygen   --seed <hex32>
//! dlc issue    --seed <hex32> [--epoch-ms <n>]
//! dlc grant    --seed <hex32>
//! dlc delegate --grant <hex> --token <hex>
//! dlc attenuate --token <hex>
//! dlc verify   --token <hex> --claim <spec> --key <pid-hex>:<pk-hex>...
//!              [--assume speaksfor:<q-pid>:<p-pid>]
//! ```
//!
//! Claim spec grammar: `top` | `atom:<n>` | `says:<principal>:<claim>`
//! where `<principal>` is a 64-char hex principal id or
//! `acting(<principal>,<principal>)`.
//!
//! HONESTY NOTE (Phase 1): `grant` signs the de-Bruijn term `Var 0`,
//! whose meaning comes from the verifier-supplied assumption context.
//! The signature does NOT bind the assumption's content — a grant made
//! under one assumption verifies under another. This is exactly the
//! class of gap the attacker-based T2 (open; see the ledger) must
//! close; the CLI exists to exercise the pipeline, not to be deployed.

use std::process::ExitCode;

use dlc_core::judgment::KeyRing;
use dlc_core::principal::{KeyRecord, Principal, PrincipalId};
use dlc_core::syntax::{Prop, Signature, Term};
use dlc_core::time::TimeBound;
use dlc_crypto::ed25519;
use dlc_protocol::wire;
use dlc_verifier::VerifyResult;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let result = match args.first().map(String::as_str) {
        Some("keygen") => cmd_keygen(&args[1..]),
        Some("issue") => cmd_issue(&args[1..]),
        Some("grant") => cmd_grant(&args[1..]),
        Some("delegate") => cmd_delegate(&args[1..]),
        Some("attenuate") => cmd_attenuate(&args[1..]),
        Some("wrap") => cmd_wrap(&args[1..]),
        Some("verify") => cmd_verify(&args[1..]),
        _ => Err(USAGE.to_string()),
    };
    match result {
        Ok(code) => code,
        Err(msg) => {
            eprintln!("{msg}");
            ExitCode::from(2)
        }
    }
}

const USAGE: &str = "dlc — Delegation Logic Calculus CLI
usage: dlc <keygen|issue|grant|delegate|attenuate|wrap|verify> [options]
see crate docs for the full flow";

// ----- subcommands ---------------------------------------------------------

fn cmd_keygen(args: &[String]) -> Result<ExitCode, String> {
    let seed = require_seed(args)?;
    let pk = ed25519::public_key(&seed);
    let pid = dlc_crypto::principal_id(&pk);
    println!("principal={}", hex_encode(&pid));
    println!("public_key={}", hex_encode(&pk));
    Ok(ExitCode::SUCCESS)
}

/// Issue: `Sign(p, Now(τ), sig)` proving `p says ⊤`.
fn cmd_issue(args: &[String]) -> Result<ExitCode, String> {
    let seed = require_seed(args)?;
    let epoch_ms = flag(args, "--epoch-ms")
        .map(|s| s.parse::<u64>().map_err(|e| format!("--epoch-ms: {e}")))
        .transpose()?
        .unwrap_or(0);
    let inner = Term::Now(TimeBound { epoch_ms });
    let token = sign_over(&seed, inner);
    println!("token={}", hex_encode(&wire::encode(&token)));
    Ok(ExitCode::SUCCESS)
}

/// Grant: `Sign(p, Var 0, sig)` — under an assumption context whose slot 0
/// is `speaksfor:<q>:<p>`, this proves `p says (q ⇒ p)`. See the module
/// honesty note.
fn cmd_grant(args: &[String]) -> Result<ExitCode, String> {
    let seed = require_seed(args)?;
    let token = sign_over(&seed, Term::Var(0));
    println!("token={}", hex_encode(&wire::encode(&token)));
    Ok(ExitCode::SUCCESS)
}

/// Delegate: `Delegate(grant, token)` proving `(p ⊓ q) says φ`.
fn cmd_delegate(args: &[String]) -> Result<ExitCode, String> {
    let grant = decode_token_flag(args, "--grant")?;
    let token = decode_token_flag(args, "--token")?;
    let combined = Term::Delegate(Box::new(grant), Box::new(token));
    println!("token={}", hex_encode(&wire::encode(&combined)));
    Ok(ExitCode::SUCCESS)
}

/// Attenuate (degenerate form): `Attenuate(token, ⊤)`.
fn cmd_attenuate(args: &[String]) -> Result<ExitCode, String> {
    let token = decode_token_flag(args, "--token")?;
    let attenuated = Term::Attenuate(Box::new(token), Box::new(Prop::Top));
    println!("token={}", hex_encode(&wire::encode(&attenuated)));
    Ok(ExitCode::SUCCESS)
}

/// Wrap a token in a COSE_Sign1 envelope signed by the presenter.
fn cmd_wrap(args: &[String]) -> Result<ExitCode, String> {
    let seed = require_seed(args)?;
    let token_hex = flag(args, "--token").ok_or("wrap: --token required")?;
    let cose = dlc_protocol::envelope::wrap_sign1(&hex_decode(&token_hex)?, &seed)
        .map_err(|e| format!("wrap: {e}"))?;
    println!("cose={}", hex_encode(&cose));
    Ok(ExitCode::SUCCESS)
}

fn cmd_verify(args: &[String]) -> Result<ExitCode, String> {
    let token_hex = flag(args, "--token").ok_or("verify: --token required")?;
    let mut wire_bytes = hex_decode(&token_hex)?;
    let claim_spec = flag(args, "--claim").ok_or("verify: --claim required")?;
    let claimed = parse_claim(&claim_spec)?;

    let mut keyring = KeyRing::default();
    for k in flags(args, "--key") {
        let (pid_hex, pk_hex) = k
            .split_once(':')
            .ok_or("--key: expected <pid-hex>:<pk-hex>")?;
        keyring.entries.push(KeyRecord {
            principal: PrincipalId(hex_decode32(pid_hex)?),
            alg: ed25519::ALG_ED25519,
            public_key: hex_decode(pk_hex)?,
        });
    }

    // --cose: the token is a COSE_Sign1 envelope; check the presenter
    // signature and verify the inner payload.
    if args.iter().any(|a| a == "--cose") {
        let (payload, presenter) = dlc_protocol::envelope::unwrap_sign1(&wire_bytes, &keyring)
            .map_err(|e| format!("cose: {e}"))?;
        println!("presenter={}", hex_encode(&presenter.0));
        wire_bytes = payload;
    }

    let mut assumptions = Vec::new();
    for a in flags(args, "--assume") {
        assumptions.push(parse_assumption(&a)?);
    }

    match dlc_verifier::check::verify_with_assumptions(
        &wire_bytes,
        &claimed,
        &keyring,
        &assumptions,
    ) {
        VerifyResult::Ok => {
            println!("verify=ok");
            Ok(ExitCode::SUCCESS)
        }
        VerifyResult::Fail { reason, .. } => {
            println!("verify=fail reason={reason}");
            Ok(ExitCode::FAILURE)
        }
    }
}

// ----- token construction --------------------------------------------------

fn sign_over(seed: &[u8; 32], inner: Term) -> Term {
    let pk = ed25519::public_key(seed);
    let pid = dlc_crypto::principal_id(&pk);
    let canonical = wire::canonical_bytes(&inner);
    let sig_bytes = ed25519::sign(seed, &canonical);
    Term::Sign(
        Principal::Atom(PrincipalId(pid)),
        Box::new(inner),
        Signature {
            alg: ed25519::ALG_ED25519,
            bytes: sig_bytes.to_vec(),
        },
    )
}

// ----- claim / assumption parsing ------------------------------------------

fn parse_claim(spec: &str) -> Result<Prop, String> {
    if spec == "top" {
        return Ok(Prop::Top);
    }
    if let Some(n) = spec.strip_prefix("atom:") {
        return Ok(Prop::Atom(n.parse().map_err(|e| format!("atom: {e}"))?));
    }
    if let Some(rest) = spec.strip_prefix("says:") {
        let (principal, inner) = split_principal(rest)?;
        let inner = inner
            .strip_prefix(':')
            .ok_or("says: expected `:` after principal")?;
        return Ok(Prop::Says(principal, Box::new(parse_claim(inner)?)));
    }
    Err(format!("unrecognized claim spec: {spec}"))
}

fn parse_assumption(spec: &str) -> Result<Prop, String> {
    if let Some(rest) = spec.strip_prefix("speaksfor:") {
        let (q_hex, p_hex) = rest
            .split_once(':')
            .ok_or("--assume speaksfor: expected <q-pid>:<p-pid>")?;
        return Ok(Prop::SpeaksFor(
            Principal::Atom(PrincipalId(hex_decode32(q_hex)?)),
            Principal::Atom(PrincipalId(hex_decode32(p_hex)?)),
        ));
    }
    Err(format!("unrecognized assumption spec: {spec}"))
}

/// Parse a leading principal from `input`; return it plus the remainder.
/// Grammar: 64 hex chars, or `acting(<principal>,<principal>)`.
fn split_principal(input: &str) -> Result<(Principal, &str), String> {
    if let Some(rest) = input.strip_prefix("acting(") {
        let (a, rest) = split_principal(rest)?;
        let rest = rest.strip_prefix(',').ok_or("acting: expected `,`")?;
        let (b, rest) = split_principal(rest)?;
        let rest = rest.strip_prefix(')').ok_or("acting: expected `)`")?;
        return Ok((Principal::Acting(Box::new(a), Box::new(b)), rest));
    }
    if input.len() >= 64 {
        let (hex, rest) = input.split_at(64);
        return Ok((Principal::Atom(PrincipalId(hex_decode32(hex)?)), rest));
    }
    Err(format!("expected principal at: {input}"))
}

// ----- tiny arg / hex helpers ----------------------------------------------

fn flag(args: &[String], name: &str) -> Option<String> {
    args.iter()
        .position(|a| a == name)
        .and_then(|i| args.get(i + 1).cloned())
}

fn flags(args: &[String], name: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut i = 0;
    while i + 1 < args.len() {
        if args[i] == name {
            out.push(args[i + 1].clone());
            i += 2;
        } else {
            i += 1;
        }
    }
    out
}

fn require_seed(args: &[String]) -> Result<[u8; 32], String> {
    hex_decode32(&flag(args, "--seed").ok_or("--seed <hex32> required")?)
}

fn decode_token_flag(args: &[String], name: &str) -> Result<Term, String> {
    let hex = flag(args, name).ok_or_else(|| format!("{name} required"))?;
    wire::decode(&hex_decode(&hex)?).map_err(|e| format!("{name}: decode failed: {e}"))
}

fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn hex_decode(s: &str) -> Result<Vec<u8>, String> {
    let s = s.trim();
    if s.len() % 2 != 0 {
        return Err("hex: odd length".into());
    }
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).map_err(|e| format!("hex: {e}")))
        .collect()
}

fn hex_decode32(s: &str) -> Result<[u8; 32], String> {
    let v = hex_decode(s)?;
    v.try_into().map_err(|_| "hex: expected 32 bytes".into())
}
