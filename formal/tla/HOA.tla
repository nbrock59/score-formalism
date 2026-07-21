--------------------------------- MODULE HOA ---------------------------------
(***************************************************************************)
(* HOA within-basin maintenance with hysteresis (formation != dissolution),*)
(* model-checked with TLC.                                                  *)
(*                                                                          *)
(* SCORE traceability:                                                      *)
(*   - Lean  : formal/Formal/Score/HOAMaintenance.lean  (§HM1-HM8)          *)
(*             discretized instance of the additive combine (§HM4) +        *)
(*             `hoaMaintainedWithin` (§HM8, an instance of                  *)
(*             `MaintainedWithinIfPreserved` from SelfStabilization.lean).  *)
(*   - vault : obsidian/SCORE/methodology/ModelCheckedDynamics.md           *)
(*             obsidian/SCORE/emergence/mechanism/Hysteresis.md             *)
(*                                                                          *)
(* Names mirror the Lean: Weight = combineAdditive (substrate + endowment); *)
(* Formation / Dissolution thresholds with Dissolution < Formation         *)
(* (`hysteresis_gap`); Engagement = Formation - Dissolution                 *)
(* (combineAdditive.engagementThreshold); HOAExists = Weight >= Formation;  *)
(* Basin = substrate >= Dissolution (substrate-based, per the (B'')         *)
(* correction); Engaged = endowment >= Engagement (`feedbackEngaged`).      *)
(***************************************************************************)
EXTENDS Integers

CONSTANTS L, Formation, Dissolution
\* Discretized CouplingWeight levels 0..L. Dissolution/Formation are the
\* hysteresis thresholds; L must let the loop close the gap (Engagement <= L)
\* and let weight reach Formation.
ASSUME HysteresisGap ==
    /\ L \in Nat /\ Formation \in Nat /\ Dissolution \in Nat
    /\ 0 < Dissolution                    \* dissolutionThreshold_pos
    /\ Dissolution < Formation            \* hysteresis_gap: dissolution < formation
    /\ Formation - Dissolution =< L       \* engagement reachable
    /\ Formation =< 2 * L                 \* weight (substrate+endowment) can reach formation

Engagement == Formation - Dissolution     \* combineAdditive.engagementThreshold (§HM4)
Lvl        == 0 .. L

VARIABLES substrate, endowment            \* HOAState: substrate + loopEndowment
vars == <<substrate, endowment>>

Weight    == substrate + endowment        \* combineAdditive: combine s e == s + e
HOAExists == Weight >= Formation          \* §HM5 HOAExists: weight >= formation
Basin     == substrate >= Dissolution     \* §HM5 Basin (substrate-based)
Engaged   == endowment >= Engagement      \* §HM6 feedbackEngaged
InWindow  == /\ substrate >= Dissolution  \* §HM5 HysteresisWindow (bistable)
             /\ substrate <  Formation

TypeOK == substrate \in Lvl /\ endowment \in Lvl

(***************************************************************************)
(* Abstract HOAMove (§HM6) made concrete for checking: one micro-step      *)
(* changes substrate OR endowment by +/-1, within bounds. The peer-specific*)
(* microdynamics the Lean leaves as `axiom HOAMove`.                       *)
(***************************************************************************)
StepSub == \E d \in {-1, 1} : (substrate + d) \in Lvl
             /\ substrate' = substrate + d /\ endowment' = endowment
StepEnd == \E d \in {-1, 1} : (endowment + d) \in Lvl
             /\ endowment' = endowment + d /\ substrate' = substrate
Step == StepSub \/ StepEnd

(***************************************************************************)
(* (1) WITHIN-BASIN MAINTENANCE (§HM8) -- discharge.                        *)
(* Premise of `MaintainedWithinIfPreserved`: start with an existing HOA in *)
(* basin; every move preserves basin AND engages feedback. Claim: HOAExists *)
(* is then an invariant. (closes_hysteresis_gap: substrate' >= Dissolution  *)
(* AND endowment' >= Engagement  =>  Weight' >= Formation.)                 *)
(***************************************************************************)
InitMaint == TypeOK /\ HOAExists /\ Basin
NextMaint == Step /\ (substrate' >= Dissolution) /\ (endowment' >= Engagement)
SpecMaint == InitMaint /\ [][NextMaint]_vars
MaintInv  == HOAExists           \* HOLDS: the maintenance theorem, model-checked

(***************************************************************************)
(* (2) DISSOLUTION OUTSIDE THE BASIN -- counterexample.                    *)
(* Drop the basin/feedback constraints (unconstrained moves). The same     *)
(* start no longer maintains HOAExists: leaving the basin dissolves it --   *)
(* "the global guarantee does not survive the boundary" (SelfStabilization  *)
(* SS3). MaintInv is VIOLATED here.                                         *)
(***************************************************************************)
InitDiss == TypeOK /\ HOAExists /\ Basin
NextDiss == Step
SpecDiss == InitDiss /\ [][NextDiss]_vars

(***************************************************************************)
(* (3) BISTABILITY / NO SPONTANEOUS FORMATION -- the formation != dissolution*)
(* asymmetry. In the hysteresis window (Dissolution <= substrate < Formation)*)
(* an unformed structure whose loop stays disengaged never forms: HOAExists  *)
(* is unreachable. Same substrate that MAINTAINS a formed HOA (case 1) will   *)
(* NOT form one -- history-dependence = hysteresis.                          *)
(***************************************************************************)
InitBist == TypeOK /\ (~HOAExists) /\ InWindow /\ (endowment < Engagement)
NextBist == Step /\ (substrate' >= Dissolution) /\ (substrate' < Formation)
                 /\ (endowment' < Engagement)
SpecBist == InitBist /\ [][NextBist]_vars
UnformedInv == ~HOAExists        \* HOLDS: unformed is a second stable equilibrium
=============================================================================
