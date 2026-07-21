----------------------------- MODULE LifeCycle ------------------------------
(***************************************************************************)
(* A-actor (individual) life-cycle as a monotone state machine, model-checked.*)
(*                                                                          *)
(* SCORE traceability:                                                       *)
(*   - Lean  : formal/Formal/Score/Core.lean (`LifeCyclePhase`, §)           *)
(*             the phase ENUM + `hasSponsorship` + `localCouplingAccumulates`;*)
(*             the phase-transition dynamics are unformalized.               *)
(*   - vault : obsidian/SCORE/agents/LifeCyclePhases.md;                     *)
(*             obsidian/SCORE/methodology/ModelCheckedDynamics.md            *)
(*                                                                          *)
(* Four phases, encoded 0..3 for the monotone ordering:                     *)
(*   0 Childhood   (<18)   inscription core; coupling inherited             *)
(*   1 Student     (18-24) mobile; local coupling accumulates very slowly   *)
(*   2 Householder (25-64) local coupling accumulation (primary HOA period) *)
(*   3 Retirement  (65+)   local coupling maximal; sponsorship activates     *)
(*                         (`hasSponsorship`: maintains HOA-attractor infra) *)
(* `coupling` is the local (HOA-relevant) coupling weight, which             *)
(* `localCouplingAccumulates` says grows monotonically -- and only in the    *)
(* settled Householder/Retirement phases.                                    *)
(***************************************************************************)
EXTENDS Integers

CONSTANTS L               \* local coupling levels 0..L
ASSUME LCa == L \in Nat /\ L > 0

Phase == 0 .. 3           \* Childhood=0, Student=1, Householder=2, Retirement=3
Lvl   == 0 .. L

VARIABLES phase, coupling
vars == <<phase, coupling>>

Sponsorship == phase = 3   \* hasSponsorship: only in Retirement (Core.lean)

TypeOK == phase \in Phase /\ coupling \in Lvl
Init   == phase = 0 /\ coupling = 0

\* Age progression: phase only advances (monotone; life-cycle is age-driven).
Advance    == phase < 3 /\ phase' = phase + 1 /\ UNCHANGED coupling
\* Local coupling accumulates -- but only in the settled phases (Householder,
\* Retirement). Childhood/Student do not accumulate local (HOA-relevant) coupling.
Accumulate == phase >= 2 /\ coupling < L /\ coupling' = coupling + 1 /\ UNCHANGED phase

Next == Advance \/ Accumulate
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Properties.                                                             *)
(***************************************************************************)

\* Monotone progression: phase and local coupling never decrease, and coupling
\* accumulates ONLY in the settled (Householder/Retirement) phases.
Monotone == [][ /\ phase' >= phase
                /\ coupling' >= coupling
                /\ (coupling' > coupling) => (phase >= 2) ]_vars

\* Reachability probe: negate to make TLC emit the trajectory to the peak-coupling
\* Retirement SPONSOR -- the agent that maintains HOA-attractor infrastructure,
\* reachable only after passing through the Householder accumulation phase.
NoPeakSponsor == ~(phase = 3 /\ coupling = L)
=============================================================================
