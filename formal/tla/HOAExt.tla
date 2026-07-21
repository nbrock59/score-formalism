------------------------------- MODULE HOAExt -------------------------------
(***************************************************************************)
(* HOA maintenance with the ceiling-residue basin extension (§ 3.2),        *)
(* model-checked with TLC.                                                   *)
(*                                                                          *)
(* SCORE traceability:                                                       *)
(*   - Lean  : formal/Formal/Score/HOAMaintenance.lean  (§HM9-HM11, §HM18-19)*)
(*             the canonical additive x linear discharge                     *)
(*             `additiveLinearResidueAugmented` +                            *)
(*             `hoaMaintainedExtendedDerived`.                               *)
(*   - vault : obsidian/SCORE/methodology/ModelCheckedDynamics.md            *)
(*             obsidian/SCORE/emergence/mechanism/Hysteresis.md (§ 3.2)      *)
(*                                                                          *)
(* Extends HOA.tla's base maintenance (§HM8) with a ceiling-residue          *)
(* dimension. Ceiling residue (Path-A structural manifold-overlap deepening) *)
(* lowers the substrate a formed HOA needs, extending the maintenance basin  *)
(* BELOW the formal dissolution threshold.                                   *)
(*                                                                          *)
(* Names mirror the Lean additive x linear discharge (§HM19):               *)
(*   ExtWeight      = additiveLinearResidueAugmented.extendedCombine         *)
(*                    = substrate + endowment + residue                      *)
(*   EffDissolution = linearCeilingResidue.effectiveDissolution              *)
(*                    = max(0, Dissolution - residue)                        *)
(*   HOAExistsExt   = HOAExistsExtended  (ExtWeight >= Formation)            *)
(*   ExtendedBasin  = substrate >= EffDissolution  (§HM11)                   *)
(*   Basin          = substrate >= Dissolution     (§HM5 formal basin)       *)
(*   Engaged        = endowment >= Engagement       (feedbackEngaged)        *)
(***************************************************************************)
EXTENDS Integers

CONSTANTS L, Formation, Dissolution
ASSUME HysteresisGap ==
    /\ L \in Nat /\ Formation \in Nat /\ Dissolution \in Nat
    /\ 0 < Dissolution
    /\ Dissolution < Formation
    /\ Formation - Dissolution =< L
    /\ Formation =< 3 * L                 \* ExtWeight = substrate+endowment+residue reaches Formation

Engagement == Formation - Dissolution
Lvl        == 0 .. L

VARIABLES substrate, endowment, residue   \* HOAState: + ceilingResidue (§HM1)
vars == <<substrate, endowment, residue>>

ExtWeight      == substrate + endowment + residue          \* §HM19 additive x linear
EffDissolution == IF Dissolution - residue > 0             \* linearCeilingResidue (§HM10)
                    THEN Dissolution - residue ELSE 0       \*   = max(0, Dissolution - residue)
HOAExistsExt   == ExtWeight >= Formation                   \* §HM18 HOAExistsExtended
ExtendedBasin  == substrate >= EffDissolution              \* §HM11 ExtendedBasin
Basin          == substrate >= Dissolution                 \* §HM5 formal basin
Engaged        == endowment >= Engagement                  \* §HM6 feedbackEngaged

TypeOK == substrate \in Lvl /\ endowment \in Lvl /\ residue \in Lvl

(***************************************************************************)
(* Abstract HOAMove (§HM6) over the residue-augmented state: one micro-step *)
(* changes substrate, endowment, OR residue by +/-1, within bounds.        *)
(***************************************************************************)
Bump(x, x2, keepA, keepA2, keepB, keepB2) ==
    \E d \in {-1, 1} : (x + d) \in Lvl /\ x2 = x + d /\ keepA2 = keepA /\ keepB2 = keepB
StepSub == Bump(substrate, substrate', endowment, endowment', residue, residue')
StepEnd == Bump(endowment, endowment', substrate, substrate', residue, residue')
StepRes == Bump(residue,   residue',   substrate, substrate', endowment, endowment')
Step == StepSub \/ StepEnd \/ StepRes

(***************************************************************************)
(* (1) EXTENDED MAINTENANCE (§HM11 / §HM19 discharge).                      *)
(* From an existing (extended) HOA in the extended basin, every move that   *)
(* stays in the extended basin AND engages feedback preserves HOAExistsExt. *)
(* (closes_extended_gap: substrate' >= Dissolution - residue' AND           *)
(*  endowment' >= Engagement  =>  substrate'+endowment'+residue' >= Formation)*)
(***************************************************************************)
InitMaint == TypeOK /\ HOAExistsExt /\ ExtendedBasin
NextMaint == Step /\ (substrate' >= EffDissolution') /\ (endowment' >= Engagement)
SpecMaint == InitMaint /\ [][NextMaint]_vars
MaintInv  == HOAExistsExt          \* HOLDS: extended maintenance, model-checked

(***************************************************************************)
(* (2) STRICT EXTENSION (the headline §HM11 result).                       *)
(* Ceiling residue extends the basin BELOW the formal dissolution floor:    *)
(* the SpecMaint reachable set contains maintained HOAs with                *)
(* substrate < Dissolution (outside the formal Basin). Asserting            *)
(* NeedsFullBasin (HOAExistsExt => Basin) is FALSE -- TLC returns a         *)
(* witness maintained on residue below the formal floor. ExtendedBasin is   *)
(* strictly weaker than Basin (`basin_implies_extendedBasin`).              *)
(***************************************************************************)
NeedsFullBasin == HOAExistsExt => Basin    \* VIOLATED: witness below the formal floor

(***************************************************************************)
(* (3) BOUNDED / CONDITIONAL EXTENSION.                                    *)
(* The extension is not permanent: with moves unconstrained, eroding the    *)
(* residue (or disengaging feedback) drops ExtWeight below Formation and    *)
(* dissolves the HOA. Same start as (1); MaintInv is VIOLATED (e.g. a       *)
(* residue 3->2 step with zero substrate/endowment).                        *)
(***************************************************************************)
InitBound == TypeOK /\ HOAExistsExt /\ ExtendedBasin
NextBound == Step
SpecBound == InitBound /\ [][NextBound]_vars
=============================================================================
