------------------------ MODULE HOACompRefinement ------------------------
(***************************************************************************)
(* Refinement mapping HOAComp => HOAB3, checked with TLC.                  *)
(*                                                                          *)
(* Third refinement-mapping instance, and the ADJUDICATION the floor-loss   *)
(* finding (HOAComp_Floor.cfg) asked for: does the composite merely weaken  *)
(* the B3 mechanism, or genuinely break its contract? Refinement gives the  *)
(* question exact form: is the composite's dynamics a valid implementation  *)
(* of the B3 mechanism's spec, with ceiling residue folded into the         *)
(* abstract endowment?                                                      *)
(*                                                                          *)
(* intent: extends -- non-refinement expected; the deliverable is the      *)
(*   failure boundary + conservative core (behavioral edge register,        *)
(*   RefinementArchitecture.md). The adjudication verdict (contract broken) *)
(*   is a boundary finding under this intent, not a defect.                 *)
(*                                                                          *)
(* SCORE traceability:                                                      *)
(*   - vault : obsidian/SCORE/methodology/ModelCheckedDynamics.md           *)
(*             obsidian/SCORE/emergence/mechanism/Hysteresis.md (open q #2) *)
(*   - Lean  : formal/Formal/Score/HOAMaintenance.lean (§HM15-HM17; the     *)
(*             §HM17 preservation rule is still axiomatic)                  *)
(*                                                                          *)
(* Retrieve mapping (abstract = HOAB3):                                     *)
(*   abstract substrate  <- substrate                                       *)
(*   abstract endowment  <- endowment + residue                             *)
(*   abstract b3         <- b3                                              *)
(*   abstract L          <- 2 * L                                           *)
(* so abstract ExtWeight = composite ExtWeight, abstract EffDissolution =   *)
(* EffB; StepSub -> StepSub, StepEnd/StepRes -> StepEnd, StepB3 -> StepB3.  *)
(*                                                                          *)
(* The arithmetic heart: CompAdd = max(0, EffC + EffB - Dissolution) and    *)
(* EffC < Dissolution whenever residue > 0, so CompAdd < EffB there -- the  *)
(* composite's basin discipline is STRICTLY MORE PERMISSIVE than the B3     *)
(* mechanism's own. Expected results:                                       *)
(* (1) B3-DISCIPLINED composite -- HOLDS. Under the abstract mechanism's    *)
(*     own basin discipline (substrate >= EffB), the composite dynamics     *)
(*     (residue free to move) refine HOAB3's SpecMaint.                     *)
(* (2) FULL composite spec -- FAILS: the floor-loss states (substrate <     *)
(*     EffB, ceiling residue covering) violate the abstract                 *)
(*     FormalExtendedBasin obligation at init. Floor loss IS refinement     *)
(*     failure: the composite does not implement the B3 contract.           *)
(* (3) ESCAPE -- behavioral failure: from a B3-disciplined start, the step  *)
(*     that first spends residue's extra permissiveness (substrate below    *)
(*     EffB') violates the abstract action obligation.                      *)
(***************************************************************************)
EXTENDS HOAComp

Abs == INSTANCE HOAB3 WITH substrate      <- substrate,
                           endowment      <- endowment + residue,
                           b3             <- b3,
                           L              <- 2 * L,
                           Formation      <- Formation,
                           Dissolution    <- Dissolution,
                           IrreducibleMin <- IrreducibleMin

AbsSpecMaint == Abs!SpecMaint

(***************************************************************************)
(* B3-disciplined composite: the composite's dynamics under the B3         *)
(* mechanism's own basin discipline (substrate >= EffB throughout).        *)
(* CompAdd <= EffB always, so NextMaint's constraint is subsumed; residue  *)
(* still free to move -- over this discipline it buys nothing the abstract *)
(* spec can see.                                                            *)
(***************************************************************************)
InitMaintB3 == TypeOK /\ HOAExistsExt /\ (substrate >= EffB)
NextMaintB3 == NextMaint /\ (substrate' >= EffB')
SpecMaintB3 == InitMaintB3 /\ [][NextMaintB3]_vars

(***************************************************************************)
(* Escape spec: B3-disciplined start, full composite moves.                *)
(***************************************************************************)
SpecMaintEscape == InitMaintB3 /\ [][NextMaint]_vars
=============================================================================
