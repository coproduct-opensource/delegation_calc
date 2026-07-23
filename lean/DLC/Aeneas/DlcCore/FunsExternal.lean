-- HAND-FILLED external-function models for the Aeneas translation of
-- `crates/dlc-core` (the `dlc_core` LLBC). This file is the "rename the
-- template and fill the holes" companion to `FunsExternal_Template.lean`
-- (see the Aeneas README, `-split-files`): Aeneas emits the *signatures* of
-- external functions as `axiom`s in the template; the user renames to
-- `FunsExternal.lean` and supplies trusted models. `Funs.lean` imports
-- `DlcCore.FunsExternal` (this file), NOT the template.
--
-- Regeneration contract: Aeneas re-emits `FunsExternal_Template.lean` on every
-- `scripts/check-drift.sh` run and the drift gate diffs it. THIS file is
-- hand-maintained and is deliberately excluded from the "committed but not
-- generated" arm of the drift diff (see scripts/check-drift.sh). If the set of
-- external functions changes, the template will drift; reconcile this file by
-- hand against the new template.
--
-- SOUNDNESS RULING (R2.2a). Each external is classified as either:
--   [COMPUTE-PATH def]  reachable from the correspondence compute path
--       (reduce_with_fuel / reduce.step / apply_command / apply_prefix /
--        deliver / world_step / commit). These MUST be real, computing,
--        machine-checked `def`s — an axiom here would let `apply_command`
--        fail to compute and could make an R2.2b square vacuous or unsound.
--   [OFF-PATH axiom]  NOT reachable from any correspondence compute path
--       (Debug/`fmt`, `Hash`/`hash`, `PartialEq::ne` default, and the
--        `ifc::Label::join` set/dedup helpers, which `reduce.step` never
--        calls). A faithful model is either impossible (opaque hasher /
--        formatter) or unnecessary; kept as `axiom` with a per-item reason.
--
-- Compute-path reachability was established by call-graph inspection of
-- Funs.lean at 4bf9ff1: `reduce.step` (3556-5293) calls only Box::as_ref
-- among these externals; `apply_command`/`deliver`/`world_step`/`commit` call
-- only local clones + primitives; Command::clone (structural) is the sole
-- compute-path consumer of Option::clone.
import Aeneas
import DlcCore.Types
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048
open dlc_core

/-- [core::array::{impl core::hash::Hash for [T; N]}::hash]:
    Source: '/rustc/library/core/src/array/mod.rs', lines 349:4-349:50
    Name pattern: [core::array::{core::hash::Hash<[@T; @N]>}::hash]
    Visibility: public -/
-- [OFF-PATH axiom] `Hash::hash` feeds an opaque `Hasher`; no correspondence
-- theorem computes through a hash. Used only inside other `hash` impls
-- (e.g. PrincipalId hashing). A faithful model is impossible (the hasher is
-- abstract) and unnecessary. Kept as an axiom.
@[rust_fun "core::array::{core::hash::Hash<[@T; @N]>}::hash"]
axiom Array.Insts.CoreHashHash.hash
  {T : Type} {H : Type} {N : Std.Usize} (hashHashInst : core.hash.Hash T)
  (hashHasherInst : core.hash.Hasher H) :
  Array T N → H → Result H

-- NOTE (R2.2a-unblock): the `debug_tuple_field2_finish` / `debug_tuple_field3_finish`
-- externals were removed here. They were referenced ONLY by the recursive
-- derived `Debug::fmt` bodies for `Principal`/`Obligation`/`Prop`/`Term`, which
-- are now opacified in translation (charon `--opaque`), so Aeneas no longer
-- emits those bodies and no longer declares these two helpers in the template.
-- The single-field variant `debug_tuple_field1_finish` is still emitted by the
-- non-recursive `Debug` impls and remains a real (Aeneas-provided) external.

/-- [core::hash::impls::{impl core::hash::Hash for u8}::hash]:
    Source: '/rustc/library/core/src/hash/mod.rs', lines 812:16-812:56
    Name pattern: [core::hash::impls::{core::hash::Hash<u8>}::hash]
    Visibility: public -/
-- [OFF-PATH axiom] scalar `Hash::hash` into an opaque hasher. Kept as an axiom.
@[rust_fun "core::hash::impls::{core::hash::Hash<u8>}::hash"]
axiom U8.Insts.CoreHashHash.hash
  {H : Type} (HasherInst : core.hash.Hasher H) : Std.U8 → H → Result H

/-- [core::hash::impls::{impl core::hash::Hash for isize}::hash]:
    Source: '/rustc/library/core/src/hash/mod.rs', lines 812:16-812:56
    Name pattern: [core::hash::impls::{core::hash::Hash<isize>}::hash]
    Visibility: public -/
-- [OFF-PATH axiom] scalar `Hash::hash` into an opaque hasher. Kept as an axiom.
@[rust_fun "core::hash::impls::{core::hash::Hash<isize>}::hash"]
axiom Isize.Insts.CoreHashHash.hash
  {H : Type} (HasherInst : core.hash.Hasher H) : Std.Isize → H → Result H

/-- [core::hash::impls::{impl core::hash::Hash for u64}::hash]:
    Source: '/rustc/library/core/src/hash/mod.rs', lines 812:16-812:56
    Name pattern: [core::hash::impls::{core::hash::Hash<u64>}::hash]
    Visibility: public -/
-- [OFF-PATH axiom] scalar `Hash::hash` into an opaque hasher. Kept as an axiom.
@[rust_fun "core::hash::impls::{core::hash::Hash<u64>}::hash"]
axiom U64.Insts.CoreHashHash.hash
  {H : Type} (HasherInst : core.hash.Hasher H) : Std.U64 → H → Result H

/-- [core::option::{impl core::fmt::Debug for core::option::Option<T>}::fmt]:
    Source: '/rustc/library/core/src/option.rs', lines 591:15-591:20
    Name pattern: [core::option::{core::fmt::Debug<core::option::Option<@T>>}::fmt]
    Visibility: public -/
-- [OFF-PATH axiom] `Debug::fmt` for Option; formatting only. Kept as an axiom.
@[rust_fun "core::option::{core::fmt::Debug<core::option::Option<@T>>}::fmt"]
axiom core.option.Option.Insts.CoreFmtDebug.fmt
  {T : Type} (fmtDebugInst : core.fmt.Debug T) :
  Option T → core.fmt.Formatter → Result ((core.result.Result Unit
    core.fmt.Error) × core.fmt.Formatter)

/-- [core::option::{impl core::clone::Clone for core::option::Option<T>}::clone]:
    Source: '/rustc/library/core/src/option.rs', lines 2277:4-2277:27
    Name pattern: [core::option::{core::clone::Clone<core::option::Option<@T>>}::clone]
    Visibility: public -/
-- [COMPUTE-PATH def] Option::clone IS reachable: `rsm.Command.Insts`.
-- `CoreCloneClone.clone` clones the `cap : Option Prop` field, and
-- `world_step`/`commit` clone every Command. The faithful structural model
-- clones the inner value via its own Clone instance (Rust semantics), so it
-- computes and is provably identity when the inner clone is.
@[rust_fun
  "core::option::{core::clone::Clone<core::option::Option<@T>>}::clone"]
def core.option.Option.Insts.CoreCloneClone.clone
  {T : Type} (cloneCloneInst : core.clone.Clone T) :
  Option T → Result (Option T)
  | none => ok none
  | some x => do
    let x1 ← cloneCloneInst.clone x
    ok (some x1)

/-- [core::option::{impl core::cmp::PartialEq<core::option::Option<T>> for core::option::Option<T>}::eq]:
    Source: '/rustc/library/core/src/option.rs', lines 2440:4-2440:38
    Name pattern: [core::option::{core::cmp::PartialEq<core::option::Option<@T>, core::option::Option<@T>>}::eq]
    Visibility: public -/
-- [COMPUTE-PATH def] Structural Option equality delegating to the inner
-- PartialEq. Used by Command::eq (and, in the DlcDRsm tree, by consensus
-- `decided`). Faithful, total, computing.
@[rust_fun
  "core::option::{core::cmp::PartialEq<core::option::Option<@T>, core::option::Option<@T>>}::eq"]
def core.option.Option.Insts.CoreCmpPartialEqOption.eq
  {T : Type} (cmpPartialEqInst : core.cmp.PartialEq T T) :
  Option T → Option T → Result Bool
  | none, none => ok true
  | some a, some b => cmpPartialEqInst.eq a b
  | _, _ => ok false

/-- [core::option::{impl core::ops::try_trait::Try for core::option::Option<T>}::branch]:
    Source: '/rustc/library/core/src/option.rs', lines 2779:4-2779:64
    Name pattern: [core::option::{core::ops::try_trait::Try<core::option::Option<@T>>}::branch]
    Visibility: public -/
-- [COMPUTE-PATH def] The `?`-operator desugaring on Option. Used pervasively
-- in `decide.infer`. Standard `Try::branch` semantics: None short-circuits
-- (Break None), Some continues. Faithful, total, computing.
@[rust_fun
  "core::option::{core::ops::try_trait::Try<core::option::Option<@T>>}::branch"]
def core.option.Option.Insts.CoreOpsTry_traitTry.branch
  {T : Type} :
  Option T → Result (core.ops.control_flow.ControlFlow (Option
    core.convert.Infallible) T)
  | none => ok (core.ops.control_flow.ControlFlow.Break none)
  | some v => ok (core.ops.control_flow.ControlFlow.Continue v)

/-- [core::option::{impl core::ops::try_trait::FromResidual<core::option::Option<core::convert::Infallible>> for core::option::Option<T>}::from_residual]:
    Source: '/rustc/library/core/src/option.rs', lines 2793:4-2793:67
    Name pattern: [core::option::{core::ops::try_trait::FromResidual<core::option::Option<@T>, core::option::Option<core::convert::Infallible>>}::from_residual]
    Visibility: public -/
-- [COMPUTE-PATH def] The residual half of the `?` desugaring. The residual
-- `Option Infallible` can only be `none` (Infallible is uninhabited), which
-- rebuilds `None` at the caller's `Option T`. The `some e` case is
-- discharged by `nomatch` since `e : Infallible` is impossible.
@[rust_fun
  "core::option::{core::ops::try_trait::FromResidual<core::option::Option<@T>, core::option::Option<core::convert::Infallible>>}::from_residual"]
def
  core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
  (T : Type) : Option core.convert.Infallible → Result (Option T)
  | none => ok none
  | some e => nomatch e

/-- [alloc::boxed::{impl core::cmp::PartialEq<alloc::boxed::Box<T>> for alloc::boxed::Box<T>}::ne]:
    Source: '/rustc/library/alloc/src/boxed.rs', lines 2127:4-2127:38
    Name pattern: [alloc::boxed::{core::cmp::PartialEq<Box<@T>, Box<@T>>}::ne]
    Visibility: public -/
-- [OFF-PATH axiom] `PartialEq::ne` for Box. Unreferenced anywhere in Funs.lean
-- (the reducer/eq use the derived `.eq` directly, never `.ne`). Kept as an
-- axiom; providing a body would be dead code.
@[rust_fun "alloc::boxed::{core::cmp::PartialEq<Box<@T>, Box<@T>>}::ne"]
axiom Box.Insts.CoreCmpPartialEqBox.ne
  {T : Type} (A : Type) (corecmpPartialEqInst : core.cmp.PartialEq T T) :
  T → T → Result Bool

-- NOTE (R2.2a-unblock): the `Box::Hash::hash` and `Box::Debug::fmt` externals
-- were removed here. They were referenced ONLY by the recursive derived
-- `Hash`/`Debug` bodies for `Principal`/`Obligation`/`Prop`/`Term` (which box
-- their sub-terms). Those bodies are now opacified in translation, so Aeneas no
-- longer emits them and no longer declares these two Box externals in the
-- template. `Box::PartialEq::ne` and `Box::AsRef::as_ref` (below) are still
-- referenced and remain.

/-- [alloc::boxed::{impl core::convert::AsRef<T> for alloc::boxed::Box<T>}::as_ref]:
    Source: '/rustc/library/alloc/src/boxed.rs', lines 2352:4-2352:26
    Name pattern: [alloc::boxed::{core::convert::AsRef<Box<@T>, @T>}::as_ref]
    Visibility: public -/
-- [COMPUTE-PATH def] `Box<T>::as_ref` returns `&T`. In Aeneas's pure model a
-- `Box<T>` is represented directly as `T`, so `as_ref` is the identity. This
-- is heavily used inside `reduce.step` (unboxing sub-terms of App/Lam/Pair/…),
-- so it MUST compute. Identity model.
@[rust_fun "alloc::boxed::{core::convert::AsRef<Box<@T>, @T>}::as_ref"]
def Box.Insts.CoreConvertAsRef.as_ref {T : Type} (A : Type) : T → Result T :=
  fun t => ok t

/-- [alloc::slice::{[T]}::sort]:
    Source: '/rustc/library/alloc/src/slice.rs', lines 131:4-133:15
    Name pattern: [alloc::slice::{[@T]}::sort]
    Visibility: public -/
-- [OFF-PATH axiom] `<[T]>::sort`. Sole call site is `ifc::Label::join`
-- (canonicalising a label's Vec<u32>), which `reduce.step`/`apply_command`/
-- `deliver`/`world_step`/`commit` never call — verified by call-graph
-- inspection. A faithful sort model is nontrivial and, being provably off the
-- correspondence compute path, unnecessary. Kept as an axiom; revisit if a
-- future theorem reaches `ifc::Label::join`.
@[rust_fun "alloc::slice::{[@T]}::sort"]
axiom alloc.slice.Slice.sort
  {T : Type} (corecmpOrdInst : core.cmp.Ord T) : Slice T → Result (Slice T)

/-- [alloc::vec::{alloc::vec::Vec<T>}::dedup]:
    Source: '/rustc/library/alloc/src/vec/mod.rs', lines 3701:4-3701:27
    Name pattern: [alloc::vec::{alloc::vec::Vec<@T>}::dedup]
    Visibility: public -/
-- [OFF-PATH axiom] `Vec::dedup`. Same sole call site as `sort` above
-- (`ifc::Label::join`), off the correspondence compute path. Kept as an axiom.
@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::dedup"]
axiom alloc.vec.Vec.dedup
  {T : Type} (A : Type) (corecmpPartialEqInst : core.cmp.PartialEq T T) :
  alloc.vec.Vec T → Result (alloc.vec.Vec T)

/-- [alloc::vec::{impl core::hash::Hash for alloc::vec::Vec<T>}::hash]:
    Source: '/rustc/library/alloc/src/vec/mod.rs', lines 3859:4-3859:44
    Name pattern: [alloc::vec::{core::hash::Hash<alloc::vec::Vec<@T>>}::hash]
    Visibility: public -/
-- [OFF-PATH axiom] `Hash::hash` for Vec into an opaque hasher. Kept as an axiom.
@[rust_fun "alloc::vec::{core::hash::Hash<alloc::vec::Vec<@T>>}::hash"]
axiom alloc.vec.Vec.Insts.CoreHashHash.hash
  {T : Type} (A : Type) {H : Type} (corehashHashInst : core.hash.Hash T)
  (corehashHasherInst : core.hash.Hasher H) :
  alloc.vec.Vec T → H → Result H

/-- [alloc::vec::{impl core::default::Default for alloc::vec::Vec<T>}::default]:
    Source: '/rustc/library/alloc/src/vec/mod.rs', lines 4304:4-4304:26
    Name pattern: [alloc::vec::{core::default::Default<alloc::vec::Vec<@T>>}::default]
    Visibility: public -/
-- [COMPUTE-PATH def] `Vec::default` is the empty vector. Trivial, total,
-- computing; matches `alloc.vec.Vec.new` used elsewhere in the tree.
@[rust_fun
  "alloc::vec::{core::default::Default<alloc::vec::Vec<@T>>}::default"]
def alloc.vec.Vec.Insts.CoreDefaultDefault.default
  (T : Type) : Result (alloc.vec.Vec T) :=
  ok (alloc.vec.Vec.new T)

-- ────────────────────────────────────────────────────────────────────────────
-- Opacified recursive `Debug` / `Hash` impls (R2.2a-unblock).
--
-- The derived `Debug`/`Hash` impls for the RECURSIVE core types
-- (`Prop`, `Term`, `Obligation`, `Principal`) are made OPAQUE in translation via
-- charon `--opaque` (see scripts/aeneas-translate.sh + scripts/check-drift.sh).
-- Aeneas emits a recursive derived `fmt`/`hash` body that self-references the
-- impl's own instance with a FORWARD reference and no `mutual` block; under Lean
-- 4.31 that does not elaborate (`Unknown constant …Insts.CoreFmtDebug`).
-- Opacifying keeps the instance *record* in `Funs.lean` (it now references the
-- axioms below) but drops the offending body, so the tree compiles.
--
-- [OFF-PATH axiom] Every entry here is `Debug::fmt` or `Hash::hash`. Neither is
-- on any correspondence compute path: `reduce_with_fuel`/`reduce.step`/
-- `apply_command`/`apply_prefix`/`deliver`/`world_step`/`commit` never format or
-- hash a value (verified by call-graph inspection). `fmt` only writes to an
-- opaque `Formatter`; `hash` only feeds an opaque `Hasher`. A faithful model is
-- both impossible (formatter/hasher are abstract) and unnecessary, so each is an
-- axiom. The Rust `#[derive(Debug, Hash)]` is UNCHANGED — `assert_eq!` and any
-- `HashMap` keys still get their real derived impls at run time; only the Lean
-- *translation* treats these two off-path traits as opaque.

/-- [dlc_core::syntax::{impl core::fmt::Debug for dlc_core::syntax::Prop}::fmt]:
    Source: 'crates/dlc-core/src/syntax.rs', lines 16:16-16:21
    Visibility: public -/
axiom syntax.Prop.Insts.CoreFmtDebug.fmt
  :
  syntax.Prop → core.fmt.Formatter → Result ((core.result.Result Unit
    core.fmt.Error) × core.fmt.Formatter)

/-- [dlc_core::syntax::{impl core::fmt::Debug for dlc_core::syntax::Term}::fmt]:
    Source: 'crates/dlc-core/src/syntax.rs', lines 56:16-56:21
    Visibility: public -/
axiom syntax.Term.Insts.CoreFmtDebug.fmt
  :
  syntax.Term → core.fmt.Formatter → Result ((core.result.Result Unit
    core.fmt.Error) × core.fmt.Formatter)

/-- [dlc_core::obligation::{impl core::fmt::Debug for dlc_core::obligation::Obligation}::fmt]:
    Source: 'crates/dlc-core/src/obligation.rs', lines 20:16-20:21
    Visibility: public -/
axiom obligation.Obligation.Insts.CoreFmtDebug.fmt
  :
  obligation.Obligation → core.fmt.Formatter → Result ((core.result.Result
    Unit core.fmt.Error) × core.fmt.Formatter)

/-- [dlc_core::principal::{impl core::fmt::Debug for dlc_core::principal::Principal}::fmt]:
    Source: 'crates/dlc-core/src/principal.rs', lines 8:16-8:21
    Visibility: public -/
axiom principal.Principal.Insts.CoreFmtDebug.fmt
  :
  principal.Principal → core.fmt.Formatter → Result ((core.result.Result
    Unit core.fmt.Error) × core.fmt.Formatter)

/-- [dlc_core::principal::{impl core::hash::Hash for dlc_core::principal::Principal}::hash]:
    Source: 'crates/dlc-core/src/principal.rs', lines 8:38-8:42
    Visibility: public -/
axiom principal.Principal.Insts.CoreHashHash.hash
  {__H : Type} (corehashHasherInst : core.hash.Hasher __H) :
  principal.Principal → __H → Result __H
