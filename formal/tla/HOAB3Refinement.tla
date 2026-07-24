------------------------- MODULE HOAB3Refinement -------------------------
(***************************************************************************)
(* Refinement mapping HOAB3 => HOA, checked with TLC.                      *)
(*                                                                          *)
(* Second refinement-mapping instance (sibling of HOAExtRefinement.tla --   *)
(* see that module's header for the method: TLC verifies                    *)
(* Spec_concrete => Spec_abstract under a retrieve mapping; W&D data        *)
(* refinement via TLA+'s native idiom).                                     *)
(*                                                                          *)
(* SCORE traceability:                                                      *)
(*   - vault : obsidian/SCORE/methodology/ModelCheckedDynamics.md           *)
(*             obsidian/SCORE/methodology/RefinementArchitecture.md         *)
(*   - Lean  : formal/Formal/Score/HOAMaintenance.lean (§HM12-HM14)         *)
(*                                                                          *)
(* Retrieve mapping:                                                        *)
(*   abstract substrate  <- substrate                                       *)
(*   abstract endowment  <- endowment + b3                                  *)
(*   abstract L          <- 2 * L                                           *)
(* so abstract Weight = ExtWeight; StepSub -> StepSub, StepEnd/StepB3 ->    *)
(* StepEnd (no stuttering).                                                 *)
(*                                                                          *)
(* Expected results (mirroring HOAExtRefinement):                           *)
(* (1) CONSERVATIVE over the formal basin -- HOLDS.                         *)
(* (2) STRICT EXTENSION = REFINEMENT FAILURE -- the full formal-extended    *)
(*     spec does not refine HOA; witness below the formal floor (the        *)
(*     HOAB3_Strict witness, floored at IrreducibleMin but still below      *)
(*     Dissolution).                                                        *)
(* (3) ESCAPE -- behavioral failure at the boundary-crossing step.          *)
(***************************************************************************)
EXTENDS HOAB3

Abs == INSTANCE HOA WITH substrate   <- substrate,
                         endowment   <- endowment + b3,
                         L           <- 2 * L,
                         Formation   <- Formation,
                         Dissolution <- Dissolution

AbsSpecMaint == Abs!SpecMaint

(***************************************************************************)
(* Restricted concrete spec: HOAB3 maintenance confined to the FORMAL      *)
(* basin (EffDissolution <= Dissolution always, so NextMaint's constraint  *)
(* is subsumed); b3 still free to move.                                    *)
(***************************************************************************)
InitMaintFormal == TypeOK /\ HOAExistsExt /\ Basin
NextMaintFormal == NextMaint /\ (substrate' >= Dissolution)
SpecMaintFormal == InitMaintFormal /\ [][NextMaintFormal]_vars

(***************************************************************************)
(* Escape spec: formal-basin start, full formal-extended moves.            *)
(***************************************************************************)
SpecMaintEscape == InitMaintFormal /\ [][NextMaint]_vars
=============================================================================
