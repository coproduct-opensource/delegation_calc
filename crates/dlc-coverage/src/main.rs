//! The decide-coverage gate.
//!
//! ```text
//! dlc-coverage            # measure and compare against the pinned baseline
//! dlc-coverage --update   # re-pin (must be a deliberate, reviewable diff)
//! ```
//!
//! Exit codes: `0` unchanged, `1` changed (in either direction), `2` could not measure.
//! The third is distinct on purpose — a parse failure must never read as full coverage.

use std::collections::BTreeSet;
use std::process::ExitCode;

use dlc_coverage::{binders, compare, Baseline, Coverage, SOUNDNESS_THEOREM};

const SYNTAX: &str = "crates/dlc-core/src/syntax.rs";
const LEAN: &str = "lean/DLC/DecideSquare.lean";
const BASELINE: &str = ".decide-coverage.json";

fn list(s: &BTreeSet<String>) -> String {
    s.iter().cloned().collect::<Vec<_>>().join(", ")
}

fn json_report(cov: &Coverage, status: &str) -> String {
    let unproven: Vec<&String> = cov.unproven_owned();
    serde_json::json!({
        "total": cov.all.len(),
        "proven": cov.proven.len(),
        "percent": (cov.percent() * 10.0).round() / 10.0,
        "status": status,
        "unproven": unproven,
    })
    .to_string()
}

fn main() -> ExitCode {
    let update = std::env::args().any(|a| a == "--update");
    let as_json = std::env::args().any(|a| a == "--json");
    let root = std::env::var("DLC_ROOT").unwrap_or_else(|_| ".".into());

    let read = |p: &str| std::fs::read_to_string(format!("{root}/{p}"));
    let (Ok(syntax), Ok(lean)) = (read(SYNTAX), read(LEAN)) else {
        if as_json {
            println!("{}", serde_json::json!({"total":0,"proven":0,"percent":0.0,"status":"unmeasurable"}));
        }
        eprintln!(
            "::error::dlc-coverage: cannot read {SYNTAX} and/or {LEAN} under `{root}`.\n\
             Run from the repository root, or set DLC_ROOT."
        );
        return ExitCode::from(2);
    };

    let cov = match Coverage::measure(&syntax, &lean) {
        Ok(c) => c,
        Err(e) => {
            if as_json {
                println!("{}", serde_json::json!({"total":0,"proven":0,"percent":0.0,"status":"unmeasurable"}));
            }
            eprintln!("::error::dlc-coverage: {e}");
            return ExitCode::from(2);
        }
    };

    let unproven = cov.unproven();
    if as_json {
        // Status is decided below against the baseline; measure first, report once.
        let path = format!("{root}/{BASELINE}");
        let status = match std::fs::read_to_string(&path)
            .ok()
            .and_then(|t| serde_json::from_str::<Baseline>(&t).ok())
        {
            None => "unpinned",
            Some(b) => {
                let v = compare(&cov, &b);
                if v.is_regression() {
                    "regressed"
                } else if v.is_clean() {
                    "ok"
                } else {
                    "changed"
                }
            }
        };
        println!("{}", json_report(&cov, status));
        return if status == "ok" { ExitCode::SUCCESS } else { ExitCode::from(1) };
    }
    println!("DLC decide-coverage");
    println!();
    println!("  Term constructors ({SYNTAX}): {}", cov.all.len());
    println!("  Proven in PropFrag ({LEAN}): {}", cov.proven.len());
    println!("  Coverage: {:.1}%", cov.percent());
    println!();
    // The number is meaningless without the theorem it is a fraction OF, so print the
    // preconditions every run. A bare percentage is the thing people round up.
    println!("  PROVEN RELATIVE TO `{SOUNDNESS_THEOREM}`, under:");
    for b in binders(&cov.soundness) {
        println!("    {b}");
    }
    println!();
    println!("  UNPROVEN ({}):", unproven.len());
    for u in &unproven {
        println!("    {u}");
    }
    println!();

    let path = format!("{root}/{BASELINE}");
    if update {
        let b = Baseline::of(&cov);
        match std::fs::write(&path, format!("{}\n", serde_json::to_string_pretty(&b).unwrap())) {
            Ok(()) => {
                println!("re-pinned {BASELINE}: {} of {} proven", cov.proven.len(), cov.all.len());
                return ExitCode::SUCCESS;
            }
            Err(e) => {
                eprintln!("::error::cannot write {path}: {e}");
                return ExitCode::from(2);
            }
        }
    }

    let text = match std::fs::read_to_string(&path) {
        Ok(t) => t,
        Err(_) => {
            eprintln!(
                "::error::no {BASELINE} baseline. Create it deliberately with `--update`; an \
                 absent baseline must not be treated as a passing one."
            );
            return ExitCode::from(2);
        }
    };
    let base: Baseline = match serde_json::from_str(&text) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("::error::malformed {BASELINE}: {e}");
            return ExitCode::from(2);
        }
    };

    let v = compare(&cov, &base);
    if v.is_clean() {
        println!("OK — unchanged from the pinned baseline.");
        return ExitCode::SUCCESS;
    }

    if !v.regressed.is_empty() {
        println!("::error::COVERAGE REGRESSED — proof lost for: {}", list(&v.regressed));
        println!("  These constructors were inside PropFrag and are not any more.");
    }
    if !v.removed_constructors.is_empty() {
        println!(
            "::error::CONSTRUCTORS DELETED: {}",
            list(&v.removed_constructors)
        );
        println!("  Deleting an arm raises the percentage without proving anything.");
        println!("  If the deletion is intended, re-pin deliberately with --update.");
    }
    if let Some((was, now)) = &v.soundness_changed {
        println!("::error::THE SOUNDNESS THEOREM CHANGED.");
        println!("  Every \"proven\" constructor means something different now.");
        println!("  pinned: {was}");
        println!("  now:    {now}");
    }
    if !v.improved.is_empty() {
        println!("COVERAGE ROSE — newly proven: {}", list(&v.improved));
        println!("  Record it: `dlc-coverage --update`. A rise that is not written down");
        println!("  becomes the new silent allowance, and the next fall back to it reads clean.");
    }
    if !v.added_constructors.is_empty() {
        println!("NEW CONSTRUCTORS (unproven): {}", list(&v.added_constructors));
        println!("  The denominator grew. Re-pin with --update once that is intended.");
    }
    println!();
    println!(
        "{}",
        if v.is_regression() {
            "FAIL — coverage went backwards."
        } else {
            "FAIL — coverage changed; re-pin so the change is visible in the diff."
        }
    );
    ExitCode::from(1)
}
