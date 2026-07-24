------------------------- MODULE HOAExtRefinement -------------------------
(***************************************************************************)
(* Refinement mapping HOAExt => HOA, checked with TLC.                     *)
(*                                                                          *)
(* FIRST REFINEMENT-MAPPING PILOT (2026-07-24): unlike every other model in *)
(* this layer, the property checked here is not an invariant but another    *)
(* SPEC -- TLC verifies Spec_concrete => Spec_abstract under a retrieve     *)
(* mapping. This is the behavioral face of Q2 SPECIALIZE                    *)
(* (RefinementArchitecture.md checks consistency, not simulation), executed *)
(* with the W&D data-refinement notion (retrieve relation + simulation)     *)
(* via TLA+'s native refinement idiom.                                      *)
(*                                                                          *)
(* SCORE traceability:                                                      *)
(*   - vault : obsidian/SCORE/methodology/ModelCheckedDynamics.md           *)
(*             obsidian/SCORE/methodology/RefinementArchitecture.md         *)
(*             obsidian/sources/Woodcock-Davies.md (the calculus source)    *)
(*   - Lean  : formal/Formal/Score/HOAMaintenance.lean                      *)
(*             (basin_implies_extendedBasin -- the static face of the       *)
(*              result checked dynamically here)                            *)
(*                                                                          *)
(* The retrieve mapping (W&D: the retrieve relation, here functional):      *)
(*   abstract substrate  <- substrate                                       *)
(*   abstract endowment  <- endowment + residue                             *)
(*   abstract L          <- 2 * L      (mapped endowment ranges to 2L)      *)
(* so abstract Weight = ExtWeight, abstract HOAExists = HOAExistsExt, and   *)
(* every concrete micro-step maps to an abstract micro-step (no stuttering: *)
(* StepSub -> StepSub; StepEnd, StepRes -> StepEnd).                        *)
(*                                                                          *)
(* Two results, the two faces of "HOAExt extends HOA":                      *)
(* (1) CONSERVATIVE EXTENSION -- HOLDS. Restricted to the FORMAL basin      *)
(*     (substrate >= Dissolution throughout), HOAExt's maintenance spec     *)
(*     refines HOA's SpecMaint. The residue may be present and vary; over   *)
(*     the formal basin it changes nothing the abstract spec can see.       *)
(*     `basin_implies_extendedBasin`, upgraded from a state-set inclusion   *)
(*     to a machine-checked simulation.                                     *)
(* (2) STRICT EXTENSION = REFINEMENT FAILURE -- VIOLATED, by design. The    *)
(*     full extended-basin spec does NOT refine HOA: TLC returns exactly a  *)
(*     below-the-formal-floor state (substrate < Dissolution, held up by    *)
(*     residue) as the failed obligation. The HOAExt_Strict.cfg headline    *)
(*     finding, re-derived as the refinement counterexample.                *)
(* (3) ESCAPE -- the failure is BEHAVIORAL, not just initial. Starting      *)
(*     inside the formal basin but moving under the full extended-basin     *)
(*     discipline, TLC returns a boundary-crossing STEP (substrate          *)
(*     Dissolution -> Dissolution-1 with residue covering) that violates    *)
(*     the abstract action obligation: the simulation itself breaks at the  *)
(*     moment the extension is exercised.                                   *)
(***************************************************************************)
EXTENDS HOAExt

Abs == INSTANCE HOA WITH substrate   <- substrate,
                         endowment   <- endowment + residue,
                         L           <- 2 * L,
                         Formation   <- Formation,
                         Dissolution <- Dissolution

AbsSpecMaint == Abs!SpecMaint

(***************************************************************************)
(* Restricted concrete spec: HOAExt maintenance confined to the FORMAL     *)
(* basin. NextMaint's extended-basin constraint is subsumed (EffDissolution *)
(* <= Dissolution always), so this is HOAExt's dynamics with HOA's basin    *)
(* discipline -- residue still free to move.                                *)
(***************************************************************************)
InitMaintFormal == TypeOK /\ HOAExistsExt /\ Basin
NextMaintFormal == NextMaint /\ (substrate' >= Dissolution)
SpecMaintFormal == InitMaintFormal /\ [][NextMaintFormal]_vars

(***************************************************************************)
(* Escape spec: formal-basin start, full extended-basin moves. Isolates    *)
(* the behavioral face of the refinement failure (case 3).                  *)
(***************************************************************************)
SpecMaintEscape == InitMaintFormal /\ [][NextMaint]_vars
=============================================================================
