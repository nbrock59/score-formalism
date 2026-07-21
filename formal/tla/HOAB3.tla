------------------------------- MODULE HOAB3 --------------------------------
(***************************************************************************)
(* HOA maintenance with the B3-substrate prosthetic basin extension (§3.3), *)
(* model-checked with TLC.                                                   *)
(*                                                                          *)
(* SCORE traceability:                                                       *)
(*   - Lean  : formal/Formal/Score/HOAMaintenance.lean  (§HM12-HM14, §HM20-21)*)
(*             the canonical additive x linear-floored discharge             *)
(*             `additiveLinearFlooredB3Augmented` +                          *)
(*             `hoaMaintainedFormalExtendedDerived`.                         *)
(*   - vault : obsidian/SCORE/methodology/ModelCheckedDynamics.md            *)
(*             obsidian/SCORE/emergence/mechanism/Hysteresis.md (§ 3.3)      *)
(*                                                                          *)
(* Sibling of HOAExt.tla (§ 3.2 ceiling residue). The formal B3 substrate    *)
(* (constitution, bylaws, roles) reduces the informal substrate a formed     *)
(* HOA needs -- BUT NOT below an irreducible minimum ("a formal structure    *)
(* rejected by all informal networks is paper without power"). That floor    *)
(* is the § 3.3 distinguishing feature the § 3.2 ceiling-residue mechanism    *)
(* lacks (ceiling residue reaches substrate = 0; B3 substrate cannot).       *)
(*                                                                          *)
(* Names mirror the Lean additive x linear-floored discharge (§HM21):       *)
(*   ExtWeight      = additiveLinearFlooredB3Augmented.extendedCombine       *)
(*                    = substrate + endowment + b3                           *)
(*   EffDissolution = linearFlooredB3Substrate.effectiveDissolution          *)
(*                    = max(IrreducibleMin, Dissolution - b3)                *)
(*   HOAExistsExt   = HOAExistsFormalExtended  (ExtWeight >= Formation)      *)
(*   FormalExtendedBasin = substrate >= EffDissolution   (§HM14)            *)
(*   Basin          = substrate >= Dissolution   (§HM5 formal basin)        *)
(*   Engaged        = endowment >= Engagement    (feedbackEngaged)          *)
(***************************************************************************)
EXTENDS Integers

CONSTANTS L, Formation, Dissolution, IrreducibleMin
ASSUME B3Assumption ==
    /\ L \in Nat /\ Formation \in Nat /\ Dissolution \in Nat /\ IrreducibleMin \in Nat
    /\ 0 < IrreducibleMin                     \* irreducibleMinimum_pos (§HM12)
    /\ IrreducibleMin =< Dissolution          \* irreducibleMinimum_below_dissolution
    /\ Dissolution < Formation                \* hysteresis_gap
    /\ Formation - Dissolution =< L
    /\ Formation =< 3 * L

Engagement == Formation - Dissolution
Lvl        == 0 .. L

VARIABLES substrate, endowment, b3          \* HOAState: + formalB3Substrate (§HM1)
vars == <<substrate, endowment, b3>>

ExtWeight      == substrate + endowment + b3            \* §HM21 additive x linear-floored
EffDissolution == IF Dissolution - b3 > IrreducibleMin  \* linearFlooredB3Substrate (§HM13)
                    THEN Dissolution - b3                \*   = max(IrreducibleMin,
                    ELSE IrreducibleMin                  \*         Dissolution - b3)
HOAExistsExt        == ExtWeight >= Formation           \* §HM20 HOAExistsFormalExtended
FormalExtendedBasin == substrate >= EffDissolution      \* §HM14 FormalExtendedBasin
Basin               == substrate >= Dissolution         \* §HM5 formal basin
Engaged             == endowment >= Engagement          \* §HM6 feedbackEngaged

TypeOK == substrate \in Lvl /\ endowment \in Lvl /\ b3 \in Lvl

(***************************************************************************)
(* Abstract HOAMove over the B3-augmented state: one micro-step changes     *)
(* substrate, endowment, OR b3 by +/-1, within bounds.                     *)
(***************************************************************************)
Bump(x, x2, keepA, keepA2, keepB, keepB2) ==
    \E d \in {-1, 1} : (x + d) \in Lvl /\ x2 = x + d /\ keepA2 = keepA /\ keepB2 = keepB
StepSub == Bump(substrate, substrate', endowment, endowment', b3, b3')
StepEnd == Bump(endowment, endowment', substrate, substrate', b3, b3')
StepB3  == Bump(b3,        b3',        substrate, substrate', endowment, endowment')
Step == StepSub \/ StepEnd \/ StepB3

(***************************************************************************)
(* (1) FORMAL-EXTENDED MAINTENANCE (§HM14 / §HM21 discharge).               *)
(* From an existing formal-extended HOA in the formal-extended basin, every *)
(* move that stays in that basin AND engages feedback preserves HOAExistsExt.*)
(* (closes_extended_gap_b3: substrate' >= max(IrreducibleMin,               *)
(*  Dissolution - b3') AND endowment' >= Engagement                        *)
(*   =>  substrate' + endowment' + b3' >= Formation)                       *)
(***************************************************************************)
InitMaint == TypeOK /\ HOAExistsExt /\ FormalExtendedBasin
NextMaint == Step /\ (substrate' >= EffDissolution') /\ (endowment' >= Engagement)
SpecMaint == InitMaint /\ [][NextMaint]_vars
MaintInv  == HOAExistsExt          \* HOLDS: formal-extended maintenance, model-checked

(***************************************************************************)
(* (2) STRICT EXTENSION -- the B3 layer extends the basin below the formal  *)
(* dissolution floor (like ceiling residue): NeedsFullBasin is VIOLATED.    *)
(* Witness: a maintained HOA at substrate < Dissolution, held up by formal  *)
(* B3 substrate. `basin_implies_extendedBasin`-analog (FormalExtendedBasin  *)
(* strictly weaker than Basin).                                             *)
(***************************************************************************)
NeedsFullBasin == HOAExistsExt => Basin       \* VIOLATED: maintained below the formal floor

(***************************************************************************)
(* (3) THE IRREDUCIBLE FLOOR -- the § 3.3 "not infinite" wrinkle, and the   *)
(* whole point of B3 vs ceiling residue: FlooredAtIrreducible HOLDS. No      *)
(* matter how much formal B3 substrate, a maintained HOA ALWAYS has          *)
(* substrate >= IrreducibleMin. The extension floors at IrreducibleMin > 0   *)
(* (bounded_below_by_irreducible, §HM12) -- unlike ceiling residue, which    *)
(* reaches substrate = 0 (HOAExt.tla case 2). "Paper without power."         *)
(***************************************************************************)
FlooredAtIrreducible == HOAExistsExt => (substrate >= IrreducibleMin)   \* HOLDS
=============================================================================
