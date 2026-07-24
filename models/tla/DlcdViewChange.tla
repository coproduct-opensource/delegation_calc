------------------------------ MODULE DlcdViewChange ------------------------------
(***************************************************************************)
(* Bounded TEMPORAL-liveness model of the DLC-D view-change protocol under  *)
(* partial synchrony.  Companion to models/tamarin/dlcd-viewchange{,-byz}.  *)
(* spthy: those give REACHABILITY (progress is POSSIBLE via view-change);   *)
(* this gives the temporal <> (progress is INEVITABLE under fairness) — the *)
(* "always eventually decides" the Tamarin exists-traces cannot express     *)
(* (spec/bft-liveness-design.md §4).                                        *)
(*                                                                          *)
(* Partial synchrony / GST (Dwork-Lynch-Stockmeyer 1988): after GST the     *)
(* network is synchronous, and leader rotation leader(v) = v mod N reaches  *)
(* a CORRECT leader within f+1 views (at most f of n = 3f+1 are faulty).    *)
(* Modelled by FaultyViews (the views with a faulty / silent / equivocating *)
(* leader) being a PROPER subset that a correct view follows.  FLP (1985):  *)
(* WITHOUT this assumption liveness is impossible — ACP's TLA+ omits it,     *)
(* DLC-D states it explicitly (the honest difference, positioning-doc §3).  *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS MaxView,          \* bound the view space so TLC is finite
          FaultyViews       \* views whose leader is Byzantine / crashed (no decision)

VARIABLES view,             \* current view number
          decided           \* TRUE once a value is decided by a quorum

vars == <<view, decided>>

Views == 0 .. MaxView

(* The partial-synchrony assumption made explicit: SOME reachable view has a  *)
(* correct leader.  This is what leader rotation + <= f faults guarantees and *)
(* what FLP shows liveness cannot do without.                                 *)
ASSUME \E v \in Views : v \notin FaultyViews

TypeOK == /\ view \in Views
          /\ decided \in BOOLEAN

Init == view = 0 /\ decided = FALSE

(* A correct-leader view (not faulty), once reached, drives a decision — a    *)
(* quorum of honest replicas votes for its proposal (abstracted to one step). *)
Decide == /\ ~decided
          /\ view \notin FaultyViews
          /\ decided' = TRUE
          /\ view' = view

(* A faulty view times out; the quorum VIEW-CHANGE advances to the next leader.*)
DoViewChange == /\ ~decided
                /\ view \in FaultyViews
                /\ view < MaxView
                /\ view' = view + 1
                /\ decided' = decided

(* Terminal stutter once decided — keeps behaviours infinite for temporal logic.*)
Stutter == decided /\ UNCHANGED vars

Next == Decide \/ DoViewChange \/ Stutter

(* Weak fairness on progress: a continuously-enabled decision or view-change   *)
(* eventually fires (the GST "messages are delivered" assumption).             *)
Spec == Init /\ [][Next]_vars /\ WF_vars(Decide) /\ WF_vars(DoViewChange)

(* SAFETY: once decided, stays decided — stable agreement, no un-decision.     *)
DecidedStable == [][decided => decided']_vars

(* LIVENESS (the point of this model): a decision is EVENTUALLY reached — the   *)
(* temporal <> that the Tamarin reachability lemmas do not provide.            *)
Liveness == <>decided
=============================================================================
