//! Decide-coverage: what fraction of the calculus does `rust_infer_sound` actually cover?
//!
//! `decide_pure` implements an arm for every `Term` constructor. `DecideSquare.PropFrag` — the
//! fragment the soundness theorem is proved over — covers a subset. The gap is the honest answer
//! to "is DLC verified", and until it is a number in CI it is a thing people round up.
//!
//! # Both sets are DERIVED, never declared
//!
//! The constructor list is parsed out of `crates/dlc-core/src/syntax.rs`, and the proven set out
//! of `lean/DLC/DecideSquare.lean`. Neither is a hand-maintained list in this crate, because a
//! hand-maintained list is a third place for the truth to live and the first place it goes stale.
//!
//! The Lean side is read by the `syntax.Term.X` reference inside each `PropFrag` constructor
//! rather than by the constructor's own name (`| var`, `| withinIntro`, …). That avoids guessing
//! a `camelCase → UpperCamelCase` mapping, and it makes the link to Rust exact: a `PropFrag`
//! constructor naming a `Term` variant that does not exist is a hard error, not a silent miss.
//!
//! # Fail closed
//!
//! Every parse failure is an error, never an empty result. "Found no constructors" must not be
//! reportable as "100% covered" — that is precisely the shape of the fail-open axiom gate found
//! in a sibling repository, where an audit that did not run printed that it had passed.

#![forbid(unsafe_code)]

use std::collections::BTreeSet;
use std::fmt;

/// Why coverage could not be measured. Distinct from "measured, and it is low".
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScanError {
    /// The `pub enum Term { … }` block was not found.
    NoTermEnum,
    /// The `inductive PropFrag` block was not found.
    NoPropFrag,
    /// The block was found but yielded nothing. A gate that reports zero constructors has not
    /// measured anything, and must not be mistaken for full coverage.
    EmptyTermEnum,
    /// Ditto for the proven set.
    EmptyPropFrag,
    /// `PropFrag` names a `Term` constructor that `syntax.rs` does not define — the Lean side and
    /// the Rust side have drifted apart, and no coverage number computed across them means
    /// anything until that is resolved.
    UnknownConstructor {
        /// The name `PropFrag` referenced.
        name: String,
    },
    /// The soundness theorem itself is missing. Without it the constructor count measures
    /// nothing: a fragment is only meaningful relative to the theorem proved over it.
    NoTheorem {
        /// The theorem that could not be found.
        name: String,
    },
}

impl fmt::Display for ScanError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ScanError::NoTermEnum => f.write_str("`pub enum Term {` not found in syntax.rs"),
            ScanError::NoPropFrag => {
                f.write_str("`inductive PropFrag` not found in DecideSquare.lean")
            }
            ScanError::EmptyTermEnum => f.write_str(
                "the Term enum yielded no constructors — refusing to report coverage over an \
                 empty denominator",
            ),
            ScanError::EmptyPropFrag => f.write_str(
                "PropFrag yielded no constructors — refusing to report 0% or 100% over an empty \
                 proven set",
            ),
            ScanError::NoTheorem { name } => write!(
                f,
                "`theorem {name}` not found: the fragment is only meaningful relative to the \
                 theorem proved over it, so a missing theorem is not a coverage number of any size"
            ),
            ScanError::UnknownConstructor { name } => write!(
                f,
                "PropFrag covers `syntax.Term.{name}`, which syntax.rs does not define: the Lean \
                 fragment and the Rust kernel have drifted"
            ),
        }
    }
}

impl std::error::Error for ScanError {}

/// Extract the constructor names of the `Term` enum from `syntax.rs`.
///
/// Scoped to the `Term` block specifically — a naive scan of the file also collects `Prop`'s
/// twelve constructors and silently inflates the denominator by half.
///
/// # Errors
/// [`ScanError::NoTermEnum`], [`ScanError::EmptyTermEnum`].
pub fn term_constructors(src: &str) -> Result<BTreeSet<String>, ScanError> {
    let start = src.find("pub enum Term {").ok_or(ScanError::NoTermEnum)?;
    let body = &src[start + "pub enum Term {".len()..];

    let mut out = BTreeSet::new();
    let mut depth = 1i32;
    for line in body.lines() {
        let t = line.trim();
        // Track nesting so a `{` inside a variant payload cannot end the scan early.
        depth += line.matches('{').count() as i32;
        depth -= line.matches('}').count() as i32;
        if depth <= 0 {
            break;
        }
        if t.starts_with("//") || t.starts_with('#') || t.is_empty() {
            continue;
        }
        // A variant: an UpperCamelCase identifier followed by a payload, brace, or comma.
        let name: String = t.chars().take_while(char::is_ascii_alphanumeric).collect();
        if name.is_empty() || !name.starts_with(|c: char| c.is_ascii_uppercase()) {
            continue;
        }
        let rest = t[name.len()..].trim_start();
        if rest.starts_with('(') || rest.starts_with('{') || rest.starts_with(',') || rest.is_empty()
        {
            out.insert(name);
        }
    }

    if out.is_empty() {
        return Err(ScanError::EmptyTermEnum);
    }
    Ok(out)
}

/// Extract the `Term` constructors covered by `PropFrag` from `DecideSquare.lean`.
///
/// Reads the `syntax.Term.X` each constructor references, not the constructor's own name.
///
/// # Errors
/// [`ScanError::NoPropFrag`], [`ScanError::EmptyPropFrag`].
pub fn propfrag_constructors(src: &str) -> Result<BTreeSet<String>, ScanError> {
    let start = src.find("inductive PropFrag").ok_or(ScanError::NoPropFrag)?;
    let body = &src[start..];

    let mut out = BTreeSet::new();
    for line in body.lines().skip(1) {
        let t = line.trim();
        // The block ends at the first line that is neither a constructor nor blank/comment.
        if t.is_empty() || t.starts_with("--") || t.starts_with("/-") {
            continue;
        }
        if !t.starts_with('|') {
            break;
        }
        let mut rest = t;
        while let Some(i) = rest.find("syntax.Term.") {
            rest = &rest[i + "syntax.Term.".len()..];
            let name: String = rest.chars().take_while(char::is_ascii_alphanumeric).collect();
            if !name.is_empty() {
                out.insert(name);
            }
        }
    }

    if out.is_empty() {
        return Err(ScanError::EmptyPropFrag);
    }
    Ok(out)
}

/// The theorem whose fragment `PropFrag` is. Pinned by name so a rename is a hard error.
pub const SOUNDNESS_THEOREM: &str = "rust_infer_sound";

/// Extract a theorem's STATEMENT — everything from `theorem <name>` up to the proof — with
/// whitespace normalised so reformatting does not fire but any token change does.
///
/// Pinning the statement matters as much as counting the fragment. A hypothesis added to
/// `rust_infer_sound` narrows what every "proven" constructor means, and the constructor count
/// would not move at all. The number would stay 12/26 while the claim shrank underneath it.
///
/// # Errors
/// [`ScanError::NoTheorem`].
pub fn theorem_statement(lean: &str, name: &str) -> Result<String, ScanError> {
    let needle = format!("theorem {name}");
    // Require it at the start of a line, so a mention inside a doc comment is not mistaken
    // for the declaration.
    // Line-anchored AND terminated: `theorem rust_infer_sound` is a PREFIX of
    // `theorem rust_infer_sound_witness_now`, which lives in the same file. Without the
    // terminator check, renaming the real theorem silently measures its neighbour and reports a
    // coverage number about the wrong claim.
    let start = lean
        .match_indices(&needle)
        .find(|(i, _)| {
            let at_line_start = *i == 0 || lean.as_bytes()[i - 1] == b'\n';
            let after = lean.as_bytes().get(i + needle.len()).copied();
            let terminated = !matches!(after, Some(c)
                if c.is_ascii_alphanumeric() || c == b'_' || c == b'\'' || c == b'.');
            at_line_start && terminated
        })
        .map(|(i, _)| i)
        .ok_or_else(|| ScanError::NoTheorem {
            name: name.to_string(),
        })?;
    let rest = &lean[start..];
    let end = rest.find(":= by").or_else(|| rest.find(":=\n")).unwrap_or(rest.len());
    Ok(rest[..end].split_whitespace().collect::<Vec<_>>().join(" "))
}

/// The parenthesised binders of a statement, in order — the preconditions a reader must see
/// alongside any coverage number.
#[must_use]
pub fn binders(statement: &str) -> Vec<String> {
    let mut out = Vec::new();
    let b = statement.as_bytes();
    let mut i = 0;
    while i < b.len() {
        if b[i] == b'(' {
            let mut depth = 1;
            let start = i;
            i += 1;
            while i < b.len() && depth > 0 {
                match b[i] {
                    b'(' => depth += 1,
                    b')' => depth -= 1,
                    _ => {}
                }
                i += 1;
            }
            let group = &statement[start..i];
            if group.contains(" : ") {
                out.push(group.to_string());
            }
        } else {
            i += 1;
        }
    }
    out
}

/// A coverage measurement.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Coverage {
    /// Every `Term` constructor `decide_pure` must handle.
    pub all: BTreeSet<String>,
    /// Those inside `PropFrag`, which `rust_infer_sound` is proved over.
    pub proven: BTreeSet<String>,
    /// The normalised statement of the soundness theorem. A fragment size means nothing
    /// without the theorem it is a fragment OF.
    pub soundness: String,
}

impl Coverage {
    /// Measure, checking that the two sides agree on what exists.
    ///
    /// # Errors
    /// Any [`ScanError`], including drift between the Lean fragment and the Rust kernel.
    pub fn measure(syntax_rs: &str, decide_square_lean: &str) -> Result<Coverage, ScanError> {
        let all = term_constructors(syntax_rs)?;
        let proven = propfrag_constructors(decide_square_lean)?;
        for p in &proven {
            if !all.contains(p) {
                return Err(ScanError::UnknownConstructor { name: p.clone() });
            }
        }
        let soundness = theorem_statement(decide_square_lean, SOUNDNESS_THEOREM)?;
        Ok(Coverage {
            all,
            proven,
            soundness,
        })
    }

    /// Constructors with an implementation but no soundness proof.
    #[must_use]
    pub fn unproven(&self) -> BTreeSet<String> {
        self.all.difference(&self.proven).cloned().collect()
    }

    /// The unproven set as an owned, ordered list — for JSON reports.
    #[must_use]
    pub fn unproven_owned(&self) -> Vec<&String> {
        self.all.difference(&self.proven).collect()
    }

    /// Proven constructors as a percentage, to one decimal place.
    #[must_use]
    pub fn percent(&self) -> f64 {
        if self.all.is_empty() {
            return 0.0;
        }
        (self.proven.len() as f64) * 100.0 / (self.all.len() as f64)
    }
}

// ---------------------------------------------------------------------------
// The ratchet
// ---------------------------------------------------------------------------

/// The pinned baseline: the exact set proven when it was last recorded.
///
/// The **set** is pinned, not the count. A count is gameable in two directions: deleting a
/// constructor raises the percentage without proving anything, and swapping one proven
/// constructor for another leaves the count untouched while losing a theorem.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Baseline {
    /// Why this file exists, carried in the file so a reader need not find the docs.
    pub note: String,
    /// Every `Term` constructor at the time of pinning — the denominator, carried in full so a
    /// later run can NAME what was added or removed rather than infer it from a count.
    pub all: Vec<String>,
    /// The proven set at the time of pinning.
    pub proven: Vec<String>,
    /// The soundness theorem's statement at the time of pinning. Pinned so that narrowing the
    /// theorem — adding a hypothesis — cannot leave the coverage number untouched.
    pub soundness: String,
}

impl Baseline {
    /// Pin the current measurement.
    #[must_use]
    pub fn of(c: &Coverage) -> Baseline {
        Baseline {
            note: "Pinned decide-coverage. The SET is the ratchet, not the count: deleting a \
                   constructor would raise the percentage without proving anything. Both \
                   directions fail — a rise must be recorded here deliberately, or an \
                   improvement silently becomes the new allowance."
                .to_string(),
            all: c.all.iter().cloned().collect(),
            proven: c.proven.iter().cloned().collect(),
            soundness: c.soundness.clone(),
        }
    }

    /// The pinned proven set.
    #[must_use]
    pub fn proven_set(&self) -> BTreeSet<String> {
        self.proven.iter().cloned().collect()
    }

    /// The pinned constructor set.
    #[must_use]
    pub fn all_set(&self) -> BTreeSet<String> {
        self.all.iter().cloned().collect()
    }
}

/// How the current measurement differs from the pinned baseline.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Verdict {
    /// Proven before, not proven now. **A lost theorem.**
    pub regressed: BTreeSet<String>,
    /// Proven now, not pinned. An improvement that must be recorded.
    pub improved: BTreeSet<String>,
    /// Constructors added since pinning — the denominator grew.
    pub added_constructors: BTreeSet<String>,
    /// Constructors removed since pinning. Raises the percentage without proving anything.
    pub removed_constructors: BTreeSet<String>,
    /// The soundness theorem's statement changed: `(pinned, now)`. Any change — a new
    /// hypothesis, a weakened conclusion — is a change to what every proven constructor means.
    pub soundness_changed: Option<(String, String)>,
}

impl Verdict {
    /// Is anything to report?
    #[must_use]
    pub fn is_clean(&self) -> bool {
        self.regressed.is_empty()
            && self.improved.is_empty()
            && self.added_constructors.is_empty()
            && self.removed_constructors.is_empty()
            && self.soundness_changed.is_none()
    }

    /// Did coverage go backwards? The direction that is a defect rather than paperwork.
    #[must_use]
    pub fn is_regression(&self) -> bool {
        !self.regressed.is_empty()
            || !self.removed_constructors.is_empty()
            || self.soundness_changed.is_some()
    }
}

/// Compare a measurement against its baseline.
#[must_use]
pub fn compare(c: &Coverage, b: &Baseline) -> Verdict {
    let pinned_proven = b.proven_set();
    let pinned_all = b.all_set();
    Verdict {
        regressed: pinned_proven.difference(&c.proven).cloned().collect(),
        improved: c.proven.difference(&pinned_proven).cloned().collect(),
        added_constructors: c.all.difference(&pinned_all).cloned().collect(),
        removed_constructors: pinned_all.difference(&c.all).cloned().collect(),
        soundness_changed: if c.soundness == b.soundness {
            None
        } else {
            Some((b.soundness.clone(), c.soundness.clone()))
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const SYNTAX: &str = r#"
pub enum Prop {
    /// doc
    Top,
    Atom(u32),
    Imp(Box<Prop>, Box<Prop>),
}

/// Proof term forms.
pub enum Term {
    /// Variable reference.
    Var(u32),
    #[allow(dead_code)]
    Lam(Box<Prop>, Box<Term>),
    App(Box<Term>, Box<Term>),
    Now(TimeBound),
}
"#;

    const LEAN: &str = r#"
inductive PropFrag : syntax.Term → Prop where
  | var (i) : PropFrag (syntax.Term.Var i)
  | now (t) : PropFrag (syntax.Term.Now t)
  | lam (phi body) : PropFrag body → PropFrag (syntax.Term.Lam phi body)

theorem infer_square_frag : True := trivial

theorem rust_infer_sound (ctx : judgment.Ctx) (term : syntax.Term)
    (hpf : PropFrag term) (hlin : ctx.linear.val = []) : True := by
  trivial
"#;

    #[test]
    fn the_term_enum_is_scoped_and_prop_is_not_counted() {
        // A naive scan of the file also collects Prop's constructors and inflates the
        // denominator by half — which would silently halve the reported coverage.
        let t = term_constructors(SYNTAX).unwrap();
        assert_eq!(t, ["App", "Lam", "Now", "Var"].map(String::from).into());
        assert!(!t.contains("Atom"));
        assert!(!t.contains("Imp"));
    }

    #[test]
    fn attributes_and_doc_comments_are_not_constructors() {
        let t = term_constructors(SYNTAX).unwrap();
        assert_eq!(t.len(), 4);
    }

    #[test]
    fn propfrag_is_read_by_its_term_reference_not_its_own_name() {
        // The Lean constructors are `var`/`now`/`lam`; what we want is the `syntax.Term.X` each
        // references, so no camelCase mapping has to be guessed.
        let p = propfrag_constructors(LEAN).unwrap();
        assert_eq!(p, ["Lam", "Now", "Var"].map(String::from).into());
    }

    #[test]
    fn the_propfrag_block_ends_at_the_next_declaration() {
        // `theorem infer_square_frag` must not be scanned for constructors.
        let p = propfrag_constructors(LEAN).unwrap();
        assert_eq!(p.len(), 3);
    }

    #[test]
    fn coverage_is_the_ratio_and_names_the_gap() {
        let c = Coverage::measure(SYNTAX, LEAN).unwrap();
        assert_eq!(c.all.len(), 4);
        assert_eq!(c.proven.len(), 3);
        assert_eq!(c.unproven(), ["App"].map(String::from).into());
        assert!((c.percent() - 75.0).abs() < 1e-9);
    }

    #[test]
    fn a_fragment_with_no_theorem_behind_it_is_not_a_coverage_number() {
        // A PropFrag with nothing proved over it measures nothing. Refusing here is the same
        // fail-closed discipline as the empty-enum case.
        let lean_no_thm = "inductive PropFrag : syntax.Term → Prop where\n  | var (i) : PropFrag (syntax.Term.Var i)\n";
        assert_eq!(
            Coverage::measure(SYNTAX, lean_no_thm),
            Err(ScanError::NoTheorem {
                name: "rust_infer_sound".into()
            })
        );
    }

    #[test]
    fn the_soundness_statement_is_carried_and_its_binders_are_visible() {
        let c = Coverage::measure(SYNTAX, LEAN).unwrap();
        assert!(c.soundness.contains("rust_infer_sound"));
        // The additive-only fence must be visible to anyone reading the number.
        assert!(binders(&c.soundness).iter().any(|b| b.contains("linear.val = []")));
    }

    #[test]
    fn changing_the_theorem_is_a_regression_even_with_the_count_unchanged() {
        let c = Coverage::measure(SYNTAX, LEAN).unwrap();
        let b = Baseline::of(&c);
        let mut narrowed = c.clone();
        narrowed.soundness.push_str(" (hextra : ctx.additive.val = [])");
        let v = compare(&narrowed, &b);
        assert_eq!(narrowed.proven.len(), c.proven.len(), "the count did not move");
        assert!(v.is_regression(), "...but the claim narrowed, so it must still be RED");
        assert!(v.soundness_changed.is_some());
    }

    // --- fail closed ---

    #[test]
    fn a_missing_term_enum_is_an_error_not_full_coverage() {
        assert_eq!(term_constructors("fn main() {}"), Err(ScanError::NoTermEnum));
    }

    #[test]
    fn a_missing_propfrag_is_an_error_not_zero_coverage() {
        assert_eq!(propfrag_constructors("-- nothing"), Err(ScanError::NoPropFrag));
    }

    #[test]
    fn an_empty_term_enum_is_an_error() {
        // THE fail-open shape: nothing found must never read as a clean result.
        assert_eq!(
            term_constructors("pub enum Term {\n}\n"),
            Err(ScanError::EmptyTermEnum)
        );
    }

    #[test]
    fn an_empty_propfrag_is_an_error() {
        assert_eq!(
            propfrag_constructors("inductive PropFrag : syntax.Term → Prop where\n\ntheorem x := 1"),
            Err(ScanError::EmptyPropFrag)
        );
    }

    #[test]
    fn lean_referencing_a_constructor_rust_does_not_define_is_drift() {
        let lean = "inductive PropFrag : syntax.Term → Prop where\n  | ghost (x) : PropFrag (syntax.Term.Ghost x)\n";
        assert_eq!(
            Coverage::measure(SYNTAX, lean),
            Err(ScanError::UnknownConstructor {
                name: "Ghost".into()
            })
        );
    }

    #[test]
    fn a_theorem_name_is_not_matched_by_prefix() {
        // REGRESSION. `theorem rust_infer_sound` is a prefix of
        // `theorem rust_infer_sound_witness_now`, which is in the same file. Renaming the real
        // theorem must be NoTheorem, not a silent measurement of its neighbour.
        let lean = "theorem renamed_away (ctx : A) : B := by\n\
                    theorem rust_infer_sound_witness_now : C := by\n";
        assert_eq!(
            theorem_statement(lean, "rust_infer_sound"),
            Err(ScanError::NoTheorem {
                name: "rust_infer_sound".into()
            })
        );
    }

    #[test]
    fn a_statement_is_normalised_but_token_sensitive() {
        let a = "theorem t (x : A)\n    (y : B) : C := by\n  trivial";
        let b = "theorem t (x : A) (y : B) : C := by\n  trivial";
        assert_eq!(theorem_statement(a, "t").unwrap(), theorem_statement(b, "t").unwrap());
        let c = "theorem t (x : A) (y : B) (z : D) : C := by";
        assert_ne!(theorem_statement(a, "t").unwrap(), theorem_statement(c, "t").unwrap());
    }

    #[test]
    fn binders_are_extracted_in_order() {
        let st = "theorem t (ctx : Ctx) (hlin : ctx.linear.val = []) (h : f x = ok (some y)) : Z";
        let b = binders(st);
        assert_eq!(b.len(), 3);
        assert!(b[1].contains("hlin"));
        assert!(b[2].contains("ok (some y)"), "nested parens must not truncate a binder");
    }

    // --- the ratchet ---

    fn cov(all: &[&str], proven: &[&str]) -> Coverage {
        Coverage {
            all: all.iter().map(|s| (*s).to_string()).collect(),
            proven: proven.iter().map(|s| (*s).to_string()).collect(),
            soundness: "theorem t : X".into(),
        }
    }

    #[test]
    fn an_unchanged_measurement_is_clean() {
        let c = cov(&["A", "B", "C"], &["A", "B"]);
        let b = Baseline::of(&c);
        assert!(compare(&c, &b).is_clean());
    }

    #[test]
    fn losing_a_proven_constructor_is_a_regression() {
        let before = cov(&["A", "B", "C"], &["A", "B"]);
        let b = Baseline::of(&before);
        let after = cov(&["A", "B", "C"], &["A"]);
        let v = compare(&after, &b);
        assert!(v.is_regression());
        assert_eq!(v.regressed, ["B"].map(String::from).into());
    }

    #[test]
    fn proving_a_new_constructor_also_fails_until_recorded() {
        // Both directions fail. A rise that is not written down turns an improvement into the
        // new silent allowance, and the next fall back to it reads as clean.
        let before = cov(&["A", "B", "C"], &["A"]);
        let b = Baseline::of(&before);
        let after = cov(&["A", "B", "C"], &["A", "B"]);
        let v = compare(&after, &b);
        assert!(!v.is_clean());
        assert!(!v.is_regression(), "an improvement is paperwork, not a defect");
        assert_eq!(v.improved, ["B"].map(String::from).into());
    }

    #[test]
    fn deleting_a_constructor_to_raise_the_percentage_is_caught() {
        // THE gaming move: drop the unproven arm, coverage jumps to 100%.
        let before = cov(&["A", "B", "C"], &["A", "B"]);
        let b = Baseline::of(&before);
        let after = cov(&["A", "B"], &["A", "B"]);
        assert!((after.percent() - 100.0).abs() < 1e-9, "the percentage did rise");
        let v = compare(&after, &b);
        assert!(v.is_regression(), "...and the ratchet must still refuse it");
        assert_eq!(v.removed_constructors, ["C"].map(String::from).into());
    }

    #[test]
    fn adding_an_unproven_constructor_is_reported() {
        let before = cov(&["A", "B"], &["A", "B"]);
        let b = Baseline::of(&before);
        let after = cov(&["A", "B", "D"], &["A", "B"]);
        let v = compare(&after, &b);
        assert!(!v.is_clean());
        assert_eq!(v.added_constructors, ["D"].map(String::from).into());
        assert!(!v.is_regression(), "adding work to do is not losing a theorem");
    }

    #[test]
    fn a_swap_that_preserves_the_count_is_still_a_regression() {
        // Why the SET is pinned and not the count: B lost, D gained, count unchanged.
        let before = cov(&["A", "B", "C", "D"], &["A", "B"]);
        let b = Baseline::of(&before);
        let after = cov(&["A", "B", "C", "D"], &["A", "D"]);
        assert_eq!(after.proven.len(), b.proven.len(), "the count is identical");
        let v = compare(&after, &b);
        assert!(v.is_regression());
        assert_eq!(v.regressed, ["B"].map(String::from).into());
    }
}
