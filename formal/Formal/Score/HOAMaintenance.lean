import Formal.Score.Core
import Formal.Score.SelfStabilization

set_option linter.unusedVariables false
set_option linter.style.whitespace false

/-!
# SCORE.HOAMaintenance

**Within-basin HOA maintenance — the SCORE-specific instance of the abstract
maintenance predicate `MaintainedWithin` (Score/SelfStabilization.lean).**

This is the (A) scaffolding of the within-basin theorem thread: infrastructure
for HOA state, hysteresis thresholds, and the maintenance property, with the
autocatalytic-maintenance rule stated as an axiom (the theoretical claim; the
(B) work will derive it from formalized weight dynamics).

**Correction of the initial Dijkstra-Edsger.md framing.** The source note first
promised convergence-from-anywhere in the hysteresis window — that is
inconsistent with the bistability that hysteresis is *for*. A state inside the
hysteresis window without an existing autocatalytic loop cannot spontaneously
form one; that would need to clear the (strictly higher) formation threshold.
What holds within-basin is *maintenance* of an existing HOA, not convergence
to one. This module states maintenance; the source note has been corrected.

See vault: `obsidian/SCORE/emergence/mechanism/HOA.md`,
`obsidian/SCORE/emergence/mechanism/Hysteresis.md`,
`obsidian/sources/Dijkstra-Edsger.md`.

OWL anchor: `score-core#WithinBasinMaintenance`
(sibling of `score-core#WithinBasinConvergence`).
-/

namespace SCORE

-- ════════════════════════════════════════════════════════════════
-- §HM1. HOA STATE — coupling-graph state as a first-class object
-- The existing `HOA` structure (Score/Core.lean §7) is a *witness* of
-- crystallization at a moment in time. For maintenance reasoning we need
-- a state type that evolves through moves; that is `HOAState`.
-- Parameterized by region so moves preserve region by construction.
-- ════════════════════════════════════════════════════════════════

/-- The joint coupling-graph state under HOA-maintenance analysis, over a
    fixed region `r`: the agents currently coupled in `r` and the current
    aggregate local coupling weight. Moves may adjust either. -/
structure HOAState (r : Region) where
  agents : List Agent
  weight : CouplingWeight

-- ════════════════════════════════════════════════════════════════
-- §HM2. HYSTERESIS THRESHOLDS (Hysteresis.md § "The claim")
-- `formation > dissolution` — the gap is what makes the region bistable.
-- Per-region rather than global (HOA.md § "Crystallization mechanism":
-- "the threshold is not fixed — it is a property of the manifold geometry").
-- ════════════════════════════════════════════════════════════════

/-- The formation (up-boundary) threshold. Aggregate local coupling weight
    must clear this for a cycle to close into a stable HOA. Per-region:
    manifold geometry differs across regions (HOA.md). -/
axiom formationThreshold : Region → CouplingWeight

/-- The dissolution (down-boundary) threshold. Once an HOA exists, its
    autocatalytic loop can maintain itself as long as weight stays at or
    above this. Below it, the loop cannot sustain — the HOA dissolves. -/
axiom dissolutionThreshold : Region → CouplingWeight

/-- The load-bearing hysteresis inequality: dissolution < formation.
    The gap is the bistable region (Hysteresis.md § "The claim"). -/
axiom hysteresis_gap :
  ∀ r : Region, (dissolutionThreshold r).val < (formationThreshold r).val

-- ════════════════════════════════════════════════════════════════
-- §HM3. HOA PREDICATES ON STATE
-- ════════════════════════════════════════════════════════════════

/-- **Crystallization predicate.** Aggregate local weight has cleared the
    formation threshold — the autocatalytic loop is (or was, in-basin)
    engaged. Corresponds to `HOA.md`'s `lean-planned: HOAExists`. -/
def HOAExists {r : Region} (s : HOAState r) : Prop :=
  (formationThreshold r).val ≤ s.weight.val

/-- **Basin predicate.** Aggregate local weight is at least the dissolution
    threshold — an existing HOA can maintain itself. Below this the HOA
    dissolves; Dijkstra 1974's global-convergence guarantee does not
    extend past the boundary in SCORE (that is the departure). -/
def Basin {r : Region} (s : HOAState r) : Prop :=
  (dissolutionThreshold r).val ≤ s.weight.val

/-- **Hysteresis window** (the strictly-bistable subregion): between the
    dissolution and formation thresholds. In this region, whether an HOA
    exists depends on history, not on current substrate conditions alone
    (Hysteresis.md § "The claim" — "the outcome depends on history"). -/
def HysteresisWindow {r : Region} (s : HOAState r) : Prop :=
  (dissolutionThreshold r).val ≤ s.weight.val ∧
  s.weight.val < (formationThreshold r).val

/-- `HOAExists` implies `Basin` (formation ≥ dissolution). -/
theorem HOAExists_implies_Basin {r : Region} (s : HOAState r)
    (h : HOAExists s) : Basin s := by
  unfold HOAExists Basin at *
  exact le_of_lt (lt_of_lt_of_le (hysteresis_gap r) h)

-- ════════════════════════════════════════════════════════════════
-- §HM4. HOA MOVE RELATION — abstract at (A)
-- Concrete dynamics (interaction weight-updates, decay, intervention,
-- autocatalytic feedback) are the (B) formalization target. Here the
-- move relation is an axiom over which the maintenance property is
-- parameterized. Per-region: moves preserve region by construction.
-- ════════════════════════════════════════════════════════════════

/-- An HOA state transition. Concrete SCORE peers instantiate this with
    peer-specific microdynamics. -/
axiom HOAMove {r : Region} : HOAState r → HOAState r → Prop

-- ════════════════════════════════════════════════════════════════
-- §HM5. WITHIN-BASIN MAINTENANCE (the (A) theorem)
-- Instance of `MaintainedWithin` (Score/SelfStabilization.lean) with
-- Basin := SCORE Basin and Property := HOAExists. Reads: from a state
-- that has an existing HOA and lies in basin, every move sequence whose
-- states all stay in basin preserves HOAExists at every step.
--
-- The load-bearing content is the autocatalytic-maintenance AXIOM
-- (§HM5.1); the maintenance THEOREM (§HM5.2) is a trivial induction on
-- top of it. This is deliberate: (A) is scaffolding — the (B) theorem
-- will replace the axiom with a derived result from weight dynamics.
-- ════════════════════════════════════════════════════════════════

/-- The HOA within-basin maintenance property (specialized `MaintainedWithin`).
    Reads: for any state where an HOA exists and the basin holds, every
    infinite move-sequence that keeps the state in basin preserves the
    existence of the HOA at every step. -/
def HOAMaintainedWithin {r : Region}
    (Moves : HOAState r → HOAState r → Prop) : Prop :=
  MaintainedWithin (@Basin r) (@HOAExists r) Moves

/-- **Autocatalytic-maintenance rule** (Hysteresis.md § "Aggregate-weight
    hysteresis"): "the cycle acts on the environment to make the environment
    more hospitable to the cycle's continued existence." Formalized here as
    an axiom — if the current state has an existing HOA and the next state
    lies in basin, then the next state also has an existing HOA. The (B)
    workstream is to derive this from formalized autocatalytic weight
    dynamics; at (A) it is the theoretical claim, stated. -/
axiom hoaPreservedByBasinMove {r : Region} :
  ∀ (s s' : HOAState r), HOAExists s → HOAMove s s' → Basin s' → HOAExists s'

/-- **The (A) maintenance theorem.** Under the autocatalytic-maintenance
    axiom, `HOAMove` maintains HOA existence within basin. Proof is a
    trivial induction on the trace index; the theorem's content lives in
    `hoaPreservedByBasinMove`. -/
theorem hoaMaintainedWithin {r : Region} :
    HOAMaintainedWithin (@HOAMove r) := by
  intro s hoa_s basin_s trace tr_0 tr_moves tr_basin i
  induction i with
  | zero =>
      rw [tr_0]; exact hoa_s
  | succ n ih =>
      exact hoaPreservedByBasinMove
        (trace n) (trace (n+1)) ih (tr_moves n) (tr_basin (n+1))

end SCORE
