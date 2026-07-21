------------------------------- MODULE HOAComp ------------------------------
(***************************************************************************)
(* HOA maintenance with the COMPOSITE basin extension (§ 3.2 ⊕ § 3.3),      *)
(* model-checked with TLC.                                                   *)
(*                                                                          *)
(* SCORE traceability:                                                       *)
(*   - Lean  : formal/Formal/Score/HOAMaintenance.lean  (§HM15-HM17)         *)
(*             CompositeBasinExtensionPolicy + the three canonical           *)
(*             instances (compositeMin, compositeAdditiveReductions,         *)
(*             compositeMultiplicativeFactors). Unlike §HM11/§HM14, the      *)
(*             §HM17 preservation rule is STILL AXIOMATIC                    *)
(*             (`hoaPreservedByCompositelyExtendedBasinMove_ifFeedbackEngaged`)*)
(*             because the composition shape is unsettled                    *)
(*             (Hysteresis.md open question #2).                             *)
(*   - vault : obsidian/SCORE/methodology/ModelCheckedDynamics.md            *)
(*             obsidian/SCORE/emergence/mechanism/Hysteresis.md              *)
(*                                                                          *)
(* Composes ceiling residue (HOAExt.tla, floorless) with B3 substrate        *)
(* (HOAB3.tla, floored). This pilot is AHEAD of the Lean: it (a) provides    *)
(* model-checked evidence the §HM17 axiom is dischargeable for the additive- *)
(* reductions composition, (b) machine-compares the three composition        *)
(* shapes, and (c) shows composing the floorless mechanism removes the B3    *)
(* floor -- concretely informing open question #2.                          *)
(*                                                                          *)
(* Names mirror the Lean §HM16 compositions:                                *)
(*   EffC    = ceiling-residue effectiveDissolution   = max(0, D - residue)  *)
(*   EffB    = B3 effectiveDissolution                = max(IrrMin, D - b3)  *)
(*   CompMin = compositeMin                = min(EffC, EffB)                 *)
(*   CompAdd = compositeAdditiveReductions = max(0, EffC + EffB - D)         *)
(*   CompMul = compositeMultiplicativeFactors ~ (EffC * EffB) \div D         *)
(*             (integer-floored; exact multiplicative needs rationals -- so  *)
(*              CompMul is used only in the comparison, not in maintenance)  *)
(***************************************************************************)
EXTENDS Integers

CONSTANTS L, Formation, Dissolution, IrreducibleMin
ASSUME CompAssumption ==
    /\ L \in Nat /\ Formation \in Nat /\ Dissolution \in Nat /\ IrreducibleMin \in Nat
    /\ 0 < IrreducibleMin
    /\ IrreducibleMin =< Dissolution
    /\ Dissolution < Formation
    /\ Formation - Dissolution =< L
    /\ Formation =< 4 * L                 \* ExtWeight = substrate+endowment+residue+b3

Engagement == Formation - Dissolution
Lvl        == 0 .. L
Max(a, b)  == IF a > b THEN a ELSE b
Min(a, b)  == IF a < b THEN a ELSE b

VARIABLES substrate, endowment, residue, b3   \* HOAState: both extension fields
vars == <<substrate, endowment, residue, b3>>

ExtWeight == substrate + endowment + residue + b3   \* the additive ⊕ additive composite

EffC == Max(0, Dissolution - residue)               \* ceiling residue (floorless)
EffB == Max(IrreducibleMin, Dissolution - b3)       \* B3 substrate (floored)

CompMin == Min(EffC, EffB)                           \* compositeMin (§HM16)
CompAdd == Max(0, EffC + EffB - Dissolution)         \* compositeAdditiveReductions
CompMul == (EffC * EffB) \div Dissolution            \* compositeMultiplicativeFactors (floored)

HOAExistsExt         == ExtWeight >= Formation
CompositelyExtBasin  == substrate >= CompAdd         \* §HM17, additive-reductions composition
Basin                == substrate >= Dissolution
Engaged              == endowment >= Engagement

TypeOK == substrate \in Lvl /\ endowment \in Lvl /\ residue \in Lvl /\ b3 \in Lvl

(***************************************************************************)
(* Abstract HOAMove over the composite state: one micro-step changes one of *)
(* the four fields by +/-1, within bounds.                                 *)
(***************************************************************************)
B(x, x2, kA, kA2, kB, kB2, kC, kC2) ==
    \E d \in {-1, 1} : (x + d) \in Lvl /\ x2 = x + d
        /\ kA2 = kA /\ kB2 = kB /\ kC2 = kC
Step ==
    \/ B(substrate, substrate', endowment, endowment', residue, residue', b3, b3')
    \/ B(endowment, endowment', substrate, substrate', residue, residue', b3, b3')
    \/ B(residue,   residue',   substrate, substrate', endowment, endowment', b3, b3')
    \/ B(b3,        b3',        substrate, substrate', endowment, endowment', residue, residue')

(***************************************************************************)
(* (1) COMPOSITE MAINTENANCE (additive-reductions) HOLDS.                   *)
(* Model-checked evidence that the (axiomatic) §HM17 preservation rule is    *)
(* dischargeable for the additive-reductions composition with additive       *)
(* combines: substrate' >= CompAdd' AND endowment' >= Engagement            *)
(*   =>  substrate' + endowment' + residue' + b3' >= Formation.              *)
(***************************************************************************)
InitMaint == TypeOK /\ HOAExistsExt /\ CompositelyExtBasin
NextMaint == Step /\ (substrate' >= CompAdd') /\ (endowment' >= Engagement)
SpecMaint == InitMaint /\ [][NextMaint]_vars
MaintInv  == HOAExistsExt

(***************************************************************************)
(* (2) COMPOSITION COMPARISON (§HM15 bounded_above_by_min + the ordering    *)
(* of the three §HM16 shapes). A pure-arithmetic invariant over the full     *)
(* state space: all three composites are at most min(EffC, EffB) (at least   *)
(* as permissive as either mechanism alone), and the additive/multiplicative *)
(* shapes are at most the min shape (strictly more permissive in some        *)
(* states). This machine-checks the §HM16 `bounded_above_by_min` proofs and  *)
(* concretely answers "how do the three compositions compare".               *)
(***************************************************************************)
InitAll == TypeOK
NextAll == Step
SpecAll == InitAll /\ [][NextAll]_vars
Comparison ==
    /\ CompMin =< EffC        /\ CompMin =< EffB        \* min ≤ either (trivially)
    /\ CompAdd =< CompMin                                \* additive ≤ min (more permissive)
    /\ CompMul =< CompMin                                \* multiplicative ≤ min
    /\ CompAdd >= 0           /\ CompMul >= 0            \* both non-negative

(***************************************************************************)
(* (3) FLOOR LOSS -- composing the floorless ceiling mechanism REMOVES the   *)
(* B3 irreducible floor. On SpecMaint, FlooredAtIrreducible is VIOLATED: a    *)
(* maintained composite HOA reaches substrate = 0 (ceiling residue zeroes the *)
(* effective dissolution), where B3 alone held substrate >= IrreducibleMin    *)
(* (HOAB3.tla, HOAB3_Floor.cfg HOLDS). The composite inherits the WEAKER      *)
(* (floorless) behaviour -- a genuine finding about the composition.         *)
(***************************************************************************)
FlooredAtIrreducible == HOAExistsExt => (substrate >= IrreducibleMin)   \* VIOLATED
=============================================================================
