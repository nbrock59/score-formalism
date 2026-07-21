--------------------------- MODULE SigmaLifeCycle ---------------------------
(***************************************************************************)
(* Σ-actor life-cycle as a closure-driven state machine, model-checked.     *)
(*                                                                          *)
(* SCORE traceability:                                                       *)
(*   - Lean  : formal/Formal/Score/Sigma.lean §29 (`SigmaLifeCyclePhase`) —  *)
(*             the phase ENUM only; the transition dynamics are unformalized.*)
(*   - vault : obsidian/SCORE/emergence/mechanism/FormalInformalClosure.md   *)
(*             § "Lifecycle derivation"; SigmaActorArchitecture.md;          *)
(*             obsidian/SCORE/methodology/ModelCheckedDynamics.md            *)
(*                                                                          *)
(* The five phases (Formation → Maturity → Crossover → Death → Reinvention)  *)
(* are CLOSURE events over the dual layer: a `formal` layer (B₃-encoded:     *)
(* constitution, roles — slow, persists in documents) and an `informal`     *)
(* layer (B₂-encoded: trust networks — fast, dies with agents). Closure is   *)
(* their mutual maintenance. The STRATIFICATION constraint appears twice:    *)
(*   - co-inscription gate: the formal (higher) layer can only be built/kept *)
(*     when the informal (lower) layer is adequate ("a formal structure      *)
(*     rejected by all informal networks is paper without power"); and       *)
(*   - a live (Maturity) closure requires BOTH layers stable.                *)
(* Death has two pathways: informal collapse (formal shell PERSISTS) vs      *)
(* formal dissolution (informal survives). Reinvention needs the surviving   *)
(* formal shell (IBM-under-Gerstner).                                        *)
(***************************************************************************)
EXTENDS Integers

CONSTANTS L, Theta        \* substrate levels 0..L; Theta = closure viability threshold
ASSUME LC == (L \in Nat) /\ (Theta \in Nat) /\ (0 < Theta) /\ (Theta =< L)

Phases == {"Formation", "Maturity", "Crossover", "Death", "Reinvention"}
Lvl    == 0 .. L

VARIABLES phase, informal, formal      \* dual-layer closure state
vars == <<phase, informal, formal>>

Viable == informal >= Theta /\ formal >= Theta   \* stable closure: both layers healthy

TypeOK == phase \in Phases /\ informal \in Lvl /\ formal \in Lvl
Init   == phase = "Formation" /\ informal = 0 /\ formal = 0

(***************************************************************************)
(* Formation — informal networks form, then co-inscribe the formal layer.  *)
(* The co-inscription step is STRATIFICATION-GATED: formal rises only when   *)
(* informal >= Theta.                                                       *)
(***************************************************************************)
FormRiseInformal == phase = "Formation" /\ informal < L
    /\ informal' = informal + 1 /\ UNCHANGED formal /\ phase' = "Formation"
FormCoInscribe   == phase = "Formation" /\ informal >= Theta /\ formal < L
    /\ formal' = formal + 1 /\ UNCHANGED informal /\ phase' = "Formation"
FormAchieve      == phase = "Formation" /\ Viable
    /\ phase' = "Maturity" /\ UNCHANGED <<informal, formal>>

(***************************************************************************)
(* Maturity — stable closure; absorb turnover while staying Viable.        *)
(* Informal dropping below Theta is metabolic stress → Crossover.          *)
(***************************************************************************)
MatTurnoverUp   == phase = "Maturity" /\ informal < L
    /\ informal' = informal + 1 /\ UNCHANGED formal /\ phase' = "Maturity"
MatTurnoverDown == phase = "Maturity" /\ informal > Theta
    /\ informal' = informal - 1 /\ UNCHANGED formal /\ phase' = "Maturity"
MatStress       == phase = "Maturity" /\ informal = Theta
    /\ informal' = informal - 1 /\ UNCHANGED formal /\ phase' = "Crossover"

(***************************************************************************)
(* Crossover — recover to Maturity, or decline to Death by one of the two  *)
(* pathways.                                                                *)
(***************************************************************************)
CrossRecover == phase = "Crossover" /\ informal < L
    /\ informal' = informal + 1 /\ UNCHANGED formal
    /\ (IF informal + 1 >= Theta THEN phase' = "Maturity" ELSE phase' = "Crossover")
CrossInformalCollapse == phase = "Crossover"          \* pathway 1: formal shell PERSISTS
    /\ informal' = 0 /\ UNCHANGED formal /\ phase' = "Death"
CrossFormalDissolve   == phase = "Crossover"          \* pathway 2: external shock, informal survives
    /\ formal' = 0 /\ UNCHANGED informal /\ phase' = "Death"

(***************************************************************************)
(* Death — reinvent within a surviving formal shell, else fresh formation.  *)
(***************************************************************************)
DeathReinvent   == phase = "Death" /\ formal > 0 /\ informal < L   \* shell survived → Reinvention
    /\ informal' = informal + 1 /\ UNCHANGED formal /\ phase' = "Reinvention"
DeathFreshStart == phase = "Death" /\ formal = 0                   \* no shell → start over
    /\ phase' = "Formation" /\ UNCHANGED <<informal, formal>>

(***************************************************************************)
(* Reinvention — new informal networks re-establish closure in the shell,   *)
(* or fail (organizational immune response) back to Death.                 *)
(***************************************************************************)
ReinventRise       == phase = "Reinvention" /\ informal < L
    /\ informal' = informal + 1 /\ UNCHANGED formal /\ phase' = "Reinvention"
ReinventCoInscribe == phase = "Reinvention" /\ informal >= Theta /\ formal < L
    /\ formal' = formal + 1 /\ UNCHANGED informal /\ phase' = "Reinvention"
ReinventSucceed    == phase = "Reinvention" /\ Viable
    /\ phase' = "Maturity" /\ UNCHANGED <<informal, formal>>
ReinventFail       == phase = "Reinvention"
    /\ informal' = 0 /\ UNCHANGED formal /\ phase' = "Death"

Next ==
    \/ FormRiseInformal \/ FormCoInscribe \/ FormAchieve
    \/ MatTurnoverUp \/ MatTurnoverDown \/ MatStress
    \/ CrossRecover \/ CrossInformalCollapse \/ CrossFormalDissolve
    \/ DeathReinvent \/ DeathFreshStart
    \/ ReinventRise \/ ReinventCoInscribe \/ ReinventSucceed \/ ReinventFail

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Properties.                                                             *)
(***************************************************************************)

\* Stratification: a live (Maturity) closure requires BOTH layers stable --
\* the formal (higher stratum) is live only on a stable informal (lower) one.
Stratification == (phase = "Maturity") => Viable

\* Reinvention only within a surviving formal shell (never after formal
\* dissolution) -- IBM-under-Gerstner.
ReinventionNeedsShell == (phase = "Reinvention") => (formal > 0)

\* Reachability probe: negate to make TLC emit the full lifecycle trace
\* Formation → Maturity → Crossover → Death → Reinvention.
NeverReinvents == phase # "Reinvention"
=============================================================================
