import Formal.Score.Core
import Formal.Score.SelfStabilization

set_option linter.unusedVariables false
set_option linter.style.whitespace false

/-!
# SCORE.HOAMaintenance

**Within-basin HOA maintenance — the SCORE-specific instance of the abstract
maintenance predicate `MaintainedWithin` (Score/SelfStabilization.lean).**

Evolution: (A) established scaffolding with the maintenance property axiomatized.
(B') separated the "in basin" premise from the "feedback engaged" premise by
introducing an abstract `feedbackEngaged` axiom. **(B'') decomposes aggregate
weight into substrate + loop-endowment via an abstract combining operator
`AutocatalyticCombine`, discharging the (B') axiom
`hoaPreservedByBasinMove_ifFeedbackEngaged` from axiom to derived theorem.**

See vault: `obsidian/SCORE/emergence/mechanism/AutocatalyticFeedback.md`,
`HOA.md`, `Hysteresis.md`, `obsidian/sources/Dijkstra-Edsger.md`.

OWL anchors: `score-core#WithinBasinMaintenance`, `score-core#AutocatalyticFeedback`.

## (B'') semantic corrections to (A)/(B')

- **`HOAState`** now carries `substrate` and `loopEndowment` (not raw `weight`);
  aggregate weight is a derived def parametric over an `AutocatalyticCombine`.
- **`Basin`** is now a **substrate condition** (`substrate ≥ dissolution`),
  not a weight condition. (A) had it weight-based — that overreached, because
  loop endowment alone could satisfy a weight-based basin even with crashed
  substrate. Hysteresis.md § 3.1 is explicit that dissolution is a substrate
  crash, not a weight crash.
- **`HysteresisWindow`** likewise refactored to substrate-based.
- Aggregate weight is `ℝ`, not `CouplingWeight` — the [0,1] type discipline
  of `CouplingWeight` is a per-edge convention, not appropriate for aggregate
  sums. (This diverges from Core.lean's `aggregateLocalWeight` axiom, which
  is a modeling choice worth revisiting in a follow-up.)
-/

namespace SCORE

-- ════════════════════════════════════════════════════════════════
-- §HM1. HOA STATE — substrate + loop-endowment decomposition ((B''))
-- Substrate is the exogenous contribution; loop endowment is the endogenous
-- contribution the autocatalytic loop supplies when engaged. Aggregate
-- observable weight is derived via an `AutocatalyticCombine` (§HM3).
-- Parametric by region so moves preserve region by construction.
-- ════════════════════════════════════════════════════════════════

/-- The joint coupling-graph state under HOA-maintenance analysis, over a
    fixed region `r`: the agents currently coupled in `r`, the exogenous
    substrate weight, and the endogenous loop endowment. Moves may adjust
    any of the three. -/
structure HOAState (r : Region) where
  agents        : List Agent
  substrate     : CouplingWeight
  loopEndowment : CouplingWeight

-- ════════════════════════════════════════════════════════════════
-- §HM2. HYSTERESIS THRESHOLDS (Hysteresis.md § "The claim")
-- ════════════════════════════════════════════════════════════════

/-- The formation (up-boundary) threshold. Per-region. -/
axiom formationThreshold : Region → CouplingWeight

/-- The dissolution (down-boundary) threshold. Per-region. -/
axiom dissolutionThreshold : Region → CouplingWeight

/-- The load-bearing hysteresis inequality: dissolution < formation. -/
axiom hysteresis_gap :
  ∀ r : Region, (dissolutionThreshold r).val < (formationThreshold r).val

/-- Dissolution is strictly positive. Required by the multiplicative combine
    instance (which divides by dissolution); also theoretically required —
    a zero dissolution threshold would mean HOAs persist with zero substrate,
    a claim about the § 3.3 B₃-substrate mechanism, not the § 3.1 aggregate-
    weight mechanism this module formalizes. -/
axiom dissolutionThreshold_pos :
  ∀ r : Region, 0 < (dissolutionThreshold r).val

-- ════════════════════════════════════════════════════════════════
-- §HM3. AUTOCATALYTIC COMBINE — the abstract combining operator ((B''))
-- SCORE does not commit to a specific arithmetic form. The vault mechanism
-- (Hysteresis.md § 3.1 — "the cycle produces the interactions that maintain
-- its edge weights") is operator-neutral; committing to additive or
-- multiplicative here would be a new theoretical claim. Instead: abstract
-- operator satisfying three properties, with peer-selectable canonical
-- instances (§HM4).
--
-- The three properties suffice to derive the (B'') maintenance theorem.
-- See AutocatalyticFeedback.md § "The combining operator" for the theory
-- side.
-- ════════════════════════════════════════════════════════════════

/-- An abstract combining operator for autocatalytic weight aggregation.
    Bundles the combine function with the properties needed to close the
    hysteresis gap when the loop is engaged. -/
structure AutocatalyticCombine where
  /-- Combines substrate with loop endowment to yield aggregate observable
      weight (as ℝ; not `CouplingWeight` — see the docstring for §HM1). -/
  combine : CouplingWeight → CouplingWeight → ℝ
  /-- More substrate → not-less weight (all else equal). -/
  monotone_substrate :
    ∀ (s₁ s₂ e : CouplingWeight),
      s₁.val ≤ s₂.val → combine s₁ e ≤ combine s₂ e
  /-- More loop endowment → not-less weight (all else equal). -/
  monotone_endowment :
    ∀ (s e₁ e₂ : CouplingWeight),
      e₁.val ≤ e₂.val → combine s e₁ ≤ combine s e₂
  /-- The engagement threshold: how large the loop endowment must be, in
      this operator's arithmetic, for the loop to close the hysteresis
      gap. Operator-specific. -/
  engagementThreshold : Region → ℝ
  /-- **The load-bearing autocatalytic axiom**: if substrate is at least
      dissolution and endowment meets the engagement threshold, the
      combined weight is at least formation. Hysteresis.md § 3.1's
      "the cycle acts on the environment to make the environment more
      hospitable" formalized as arithmetic. -/
  closes_hysteresis_gap :
    ∀ (r : Region) (substrate endowment : CouplingWeight),
      (dissolutionThreshold r).val ≤ substrate.val →
      engagementThreshold r ≤ endowment.val →
      (formationThreshold r).val ≤ combine substrate endowment

/-- Aggregate weight of an HOA state under a chosen combining operator. -/
def HOAState.weight {r : Region} (c : AutocatalyticCombine)
    (s : HOAState r) : ℝ :=
  c.combine s.substrate s.loopEndowment

-- ════════════════════════════════════════════════════════════════
-- §HM4. TWO CANONICAL INSTANCES ((B''))
-- Both discharge the abstract shape; peers pick one (or supply their own).
-- POLARIS defaults to `combineAdditive` as the simpler-to-verify choice.
-- ════════════════════════════════════════════════════════════════

/-- **Additive** combine: `weight = substrate + loop_endowment`.
    Engagement threshold: `formation - dissolution`. Arithmetically cleanest;
    reads as "the loop adds weight." -/
noncomputable def combineAdditive : AutocatalyticCombine where
  combine s e := s.val + e.val
  monotone_substrate s₁ s₂ e h := by linarith
  monotone_endowment s e₁ e₂ h := by linarith
  engagementThreshold r := (formationThreshold r).val - (dissolutionThreshold r).val
  closes_hysteresis_gap r s e hs he := by linarith

/-- **Multiplicative** combine: `weight = substrate × (1 + loop_endowment)`.
    Engagement threshold: `(formation - dissolution) / dissolution`. Matches
    Kauffman-style autocatalytic dynamics (rate ∝ substrate × catalyst);
    reads as "the loop causes the substrate to yield more weight." -/
noncomputable def combineMultiplicative : AutocatalyticCombine where
  combine s e := s.val * (1 + e.val)
  monotone_substrate s₁ s₂ e h := by
    have : (0 : ℝ) ≤ 1 + e.val := by linarith [e.pos]
    exact mul_le_mul_of_nonneg_right h this
  monotone_endowment s e₁ e₂ h := by
    have hs : (0 : ℝ) ≤ s.val := s.pos
    have : (1 : ℝ) + e₁.val ≤ 1 + e₂.val := by linarith
    exact mul_le_mul_of_nonneg_left this hs
  engagementThreshold r :=
    ((formationThreshold r).val - (dissolutionThreshold r).val)
      / (dissolutionThreshold r).val
  closes_hysteresis_gap r s e hs he := by
    have h_pos : 0 < (dissolutionThreshold r).val := dissolutionThreshold_pos r
    have h_pos_ne : (dissolutionThreshold r).val ≠ 0 := ne_of_gt h_pos
    have h_e_pos : (0 : ℝ) ≤ e.val := e.pos
    -- from he : ((formation - dissolution) / dissolution) ≤ e.val, multiplying
    -- both sides by dissolution > 0 gives:
    --   formation - dissolution ≤ e.val * dissolution
    have key : (formationThreshold r).val - (dissolutionThreshold r).val
                ≤ e.val * (dissolutionThreshold r).val := by
      have h := mul_le_mul_of_nonneg_right he (le_of_lt h_pos)
      rwa [div_mul_cancel₀ _ h_pos_ne] at h
    -- s.val * e.val ≥ dissolution.val * e.val (since s ≥ dissolution and e ≥ 0)
    have hse : (dissolutionThreshold r).val * e.val ≤ s.val * e.val := by
      exact mul_le_mul_of_nonneg_right hs h_e_pos
    -- combine: s * (1 + e) = s + s*e ≥ dissolution + dissolution*e ≥ dissolution + (formation - dissolution) = formation
    have expand : s.val * (1 + e.val) = s.val + s.val * e.val := by ring
    rw [expand]
    have h_comm : (dissolutionThreshold r).val * e.val
                = e.val * (dissolutionThreshold r).val := by ring
    linarith

-- ════════════════════════════════════════════════════════════════
-- §HM5. HOA PREDICATES ON STATE
-- HOAExists is parametric on the combine (aggregate weight depends on it);
-- Basin and HysteresisWindow are substrate-only (independent of combine).
-- ════════════════════════════════════════════════════════════════

/-- **Crystallization predicate.** Aggregate weight (under the chosen
    combining operator) is at least the formation threshold — the
    autocatalytic loop is (or was, in-basin) engaged. -/
def HOAExists {r : Region} (c : AutocatalyticCombine)
    (s : HOAState r) : Prop :=
  (formationThreshold r).val ≤ HOAState.weight c s

/-- **Basin predicate** (substrate-based, per (B'') correction). An
    existing HOA can maintain itself as long as *substrate* stays at or
    above dissolution — dissolution is about substrate crashing, not
    weight crashing (Hysteresis.md § 3.1). -/
def Basin {r : Region} (s : HOAState r) : Prop :=
  (dissolutionThreshold r).val ≤ s.substrate.val

/-- **Hysteresis window** (substrate-based, the strictly-bistable
    subregion). In this substrate range, whether an HOA exists depends on
    history — the same substrate can host either an extant HOA (with loop
    engaged) or nothing (Hysteresis.md § "The claim"). -/
def HysteresisWindow {r : Region} (s : HOAState r) : Prop :=
  (dissolutionThreshold r).val ≤ s.substrate.val ∧
  s.substrate.val < (formationThreshold r).val

-- ════════════════════════════════════════════════════════════════
-- §HM6. HOA MOVE + FEEDBACK — abstract move; concrete feedback
-- `HOAMove` remains fully abstract at (B''). `feedbackEngaged` is now
-- a concrete predicate on state (loop endowment meets the engagement
-- threshold), no longer an axiom.
-- ════════════════════════════════════════════════════════════════

/-- An HOA state transition. Abstract; concrete SCORE peers instantiate
    with peer-specific microdynamics. -/
axiom HOAMove {r : Region} : HOAState r → HOAState r → Prop

/-- **Autocatalytic feedback is engaged** for the transition into `s'`:
    the loop endowment in `s'` meets the combining operator's engagement
    threshold. Was an abstract axiom at (B'); now a derived predicate on
    the substrate/loop-endowment decomposition. -/
def feedbackEngaged {r : Region} (c : AutocatalyticCombine)
    (s s' : HOAState r) : Prop :=
  c.engagementThreshold r ≤ s'.loopEndowment.val

-- ════════════════════════════════════════════════════════════════
-- §HM7. DERIVED PRESERVATION THEOREM ((B''))
-- Was axiomatized in (B'); now derived from `closes_hysteresis_gap`.
-- The (B') axiom's content — "engaged feedback + basin preserves HOA" —
-- is exactly the abstract-operator axiom, once one accepts the
-- substrate/loop-endowment decomposition of aggregate weight.
-- ════════════════════════════════════════════════════════════════

/-- **The autocatalytic-maintenance rule** — was axiom at (B'), theorem
    at (B''). If HOA exists, feedback is engaged for the move, and the
    next state is in basin, then the next state also has an existing HOA.
    Proof is `closes_hysteresis_gap` applied directly. -/
theorem hoaPreservedByBasinMove_ifFeedbackEngaged
    {r : Region} (c : AutocatalyticCombine) :
    ∀ (s s' : HOAState r),
      HOAExists c s → HOAMove s s' → feedbackEngaged c s s' →
      Basin s' → HOAExists c s' := by
  intro s s' _ _ h_fb h_basin
  unfold HOAExists HOAState.weight
  exact c.closes_hysteresis_gap r s'.substrate s'.loopEndowment h_basin h_fb

-- ════════════════════════════════════════════════════════════════
-- §HM8. WITHIN-BASIN MAINTENANCE (the (A)/(B')/(B'') theorem)
-- Instance of `MaintainedWithinIfPreserved` (Score/SelfStabilization.lean).
-- Theorem body unchanged from (B'); premises now parametric on the
-- combining operator.
-- ════════════════════════════════════════════════════════════════

/-- The HOA within-basin maintenance property, parametric on the chosen
    combining operator. Reads: for any state where an HOA exists (under `c`)
    and the substrate basin holds, every infinite move-sequence that keeps
    the state in basin AND has autocatalytic feedback engaged (under `c`)
    at every step preserves HOAExists at every step. -/
def HOAMaintainedWithin {r : Region} (c : AutocatalyticCombine)
    (Moves : HOAState r → HOAState r → Prop) : Prop :=
  MaintainedWithinIfPreserved (@Basin r) (HOAExists c) Moves (feedbackEngaged c)

/-- **The maintenance theorem.** Under the derived autocatalytic-
    maintenance rule (`hoaPreservedByBasinMove_ifFeedbackEngaged`),
    `HOAMove` maintains HOA existence within basin. Proof is a trivial
    induction on the trace index; the content lives in the theorem's
    (now-derived) premise. -/
theorem hoaMaintainedWithin {r : Region} (c : AutocatalyticCombine) :
    HOAMaintainedWithin c (@HOAMove r) := by
  intro s hoa_s basin_s trace tr_0 tr_moves tr_basin tr_feedback i
  induction i with
  | zero =>
      rw [tr_0]; exact hoa_s
  | succ n ih =>
      exact hoaPreservedByBasinMove_ifFeedbackEngaged c
        (trace n) (trace (n+1)) ih (tr_moves n) (tr_feedback n) (tr_basin (n+1))

end SCORE
