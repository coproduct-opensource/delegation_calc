-- HAND-FILLED external-function models for the Aeneas translation of
-- `crates/dlc-d-rsm` (the `dlc_d_rsm` LLBC, which inlines `dlc_core`'s types).
-- Companion to `FunsExternal_Template.lean` (Aeneas `-split-files` emits the
-- template; the user renames + fills the holes). `Funs.lean` imports
-- `DlcDRsm.FunsExternal` (this file). Hand-maintained; excluded from the
-- "committed but not generated" arm of scripts/check-drift.sh.
--
-- SOUNDNESS RULING (R2.2a). The sole external is `dlc_core::rsm::Command`'s
-- derived `PartialEq::eq`. It is emitted external here (not in the DlcCore
-- tree) because in the `dlc_d_rsm` LLBC the `Command` PartialEq impl comes
-- from the inlined `dlc_core` dependency and Charon exposed only its signature.
--
-- [COMPUTE-PATH def] Command::eq IS on the DlcDRsm compute path:
-- `consensus.decided` calls it to count matching votes toward a quorum
-- (`consensus.decided_loop.body`). So it MUST be a real, computing, structural
-- equality — an axiom would let `decided` fail to compute. We model Rust's
-- derived structural `PartialEq` by deriving `BEq` for the whole reachable
-- AST (Term/Prop/Principal/Obligation/… and their leaf scalar/Vec/Array
-- fields, which carry Aeneas-provided `BEq`+`LawfulBEq`) and defining `eq` as
-- boolean `==`. This is the faithful model of `#[derive(PartialEq)]`.
--
-- NOTE: the DlcDRsm tree ships NO correspondence proof (R2.1/R2.2a); the R2.2b
-- correspondence targets the DlcCore tree. This def exists so the lib COMPILES
-- and so a future consensus correspondence has a real (non-vacuous) eq to
-- reason about.
import Aeneas
import DlcDRsm.Types
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048
open dlc_d_rsm

-- Structural `BEq` for the reachable AST, leaves first. The scalar, `Array`
-- and `Vec` field types already carry `BEq` (+ `LawfulBEq`) from Aeneas.Std,
-- so each derivation only needs the previously-derived component instances.
deriving instance BEq for dlc_core.time.TimeBound
deriving instance BEq for dlc_core.obligation.DpBudget
deriving instance BEq for dlc_core.principal.Principal
deriving instance BEq for dlc_core.obligation.Obligation
deriving instance BEq for dlc_core.syntax.Signature
deriving instance BEq for dlc_core.syntax.Prop
deriving instance BEq for dlc_core.syntax.Term
deriving instance BEq for dlc_core.rsm.Command

/-- [dlc_core::rsm::{impl core::cmp::PartialEq<dlc_core::rsm::Command> for dlc_core::rsm::Command}::eq]:
    Source: 'crates/dlc-core/src/rsm.rs', lines 127:23-127:32
    Name pattern: [dlc_core::rsm::{core::cmp::PartialEq<dlc_core::rsm::Command, dlc_core::rsm::Command>}::eq]
    Visibility: public -/
@[rust_fun
  "dlc_core::rsm::{core::cmp::PartialEq<dlc_core::rsm::Command, dlc_core::rsm::Command>}::eq"]
def dlc_core.rsm.Command.Insts.CoreCmpPartialEqCommand.eq
  (c1 c2 : dlc_core.rsm.Command) : Result Bool :=
  ok (c1 == c2)
