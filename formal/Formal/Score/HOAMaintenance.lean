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
    fixed region `r`: agents, exogenous substrate weight, endogenous loop
    endowment, accumulated ceiling residue (Path-A structural manifold-
    overlap deepening — used by the § 3.2 ceiling-residue extension,
    §HM9–HM11), and formal B₃ substrate (co-inscribed formal layer — used
    by the § 3.3 B₃-substrate prosthetic extension, §HM12–HM14). Moves may
    adjust any of the five; ceiling-residue and formal-B₃ fields are inert
    at the (B'') aggregate-weight tier. Note: `formalB3Substrate` is zero
    for A-actors (they don't have a formal B₃ layer); the § 3.3 mechanism
    is vacuous at zero substrate per its `boundary_at_zero` policy axiom. -/
structure HOAState (r : Region) where
  agents            : List Agent
  substrate         : CouplingWeight
  loopEndowment     : CouplingWeight
  ceilingResidue    : CouplingWeight
  formalB3Substrate : CouplingWeight

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

-- ════════════════════════════════════════════════════════════════
-- §HM9. CEILING RESIDUE POLICY — the basin-extension mechanism (Hysteresis
-- § 3.2). Path-A structural restructuring is a state quantity (the
-- ceilingResidue field) that reduces the EFFECTIVE dissolution threshold
-- — the loop can maintain the HOA at substrate below the (§ 3.1) formal
-- dissolution threshold.
--
-- SCORE does not commit to a specific dependence of effective dissolution
-- on residue — the abstract policy captures the shape (four axioms), with
-- two canonical instances (§HM10) shipped.
-- ════════════════════════════════════════════════════════════════

/-- Abstract ceiling-residue policy: bundles the effective-dissolution
    function with the four properties that suffice to state the extended
    maintenance theorem. See vault: `AutocatalyticFeedback.md` and
    `CeilingResidue.md`. -/
structure CeilingResiduePolicy where
  /-- Effective dissolution threshold as a function of ceiling residue.
      Reduces the substrate requirement for maintaining an existing HOA. -/
  effectiveDissolution : Region → CouplingWeight → ℝ
  /-- At zero residue, effective dissolution equals formal dissolution
      (no basin extension). -/
  boundary_at_zero :
    ∀ (r : Region),
      effectiveDissolution r ⟨0, le_refl 0, zero_le_one⟩ = (dissolutionThreshold r).val
  /-- More residue → not-more effective dissolution (basin only widens). -/
  monotone_residue :
    ∀ (r : Region) (res₁ res₂ : CouplingWeight),
      res₁.val ≤ res₂.val →
      effectiveDissolution r res₂ ≤ effectiveDissolution r res₁
  /-- Bounded above by formal dissolution (residue never *raises* the
      substrate requirement). -/
  bounded :
    ∀ (r : Region) (res : CouplingWeight),
      effectiveDissolution r res ≤ (dissolutionThreshold r).val
  /-- Non-negative (a substrate of exactly zero always dissolves — §HM
      preserves the "cut off exogenous inputs entirely → dissolve"
      boundary from Hysteresis.md § 3.1). -/
  nonneg :
    ∀ (r : Region) (res : CouplingWeight),
      0 ≤ effectiveDissolution r res

-- ════════════════════════════════════════════════════════════════
-- §HM10. TWO CANONICAL INSTANCES
-- ════════════════════════════════════════════════════════════════

/-- **Linear** ceiling-residue policy: `effective = max(0, formal - residue)`.
    Ceiling residue reduces the substrate requirement one-for-one, clamped
    at zero. -/
noncomputable def linearCeilingResidue : CeilingResiduePolicy where
  effectiveDissolution r res := max 0 ((dissolutionThreshold r).val - res.val)
  boundary_at_zero r := by
    simp
    exact le_of_lt (dissolutionThreshold_pos r)
  monotone_residue r res₁ res₂ h := by
    have : (dissolutionThreshold r).val - res₂.val ≤ (dissolutionThreshold r).val - res₁.val := by
      linarith
    exact max_le_max (le_refl 0) this
  bounded r res := by
    have h_res_nn : 0 ≤ res.val := res.pos
    have : (dissolutionThreshold r).val - res.val ≤ (dissolutionThreshold r).val := by linarith
    have h_d_nn : 0 ≤ (dissolutionThreshold r).val := le_of_lt (dissolutionThreshold_pos r)
    exact max_le h_d_nn this
  nonneg r res := le_max_left _ _

/-- **Multiplicative** ceiling-residue policy:
    `effective = formal * (1 - residue)`. Ceiling residue scales the
    substrate requirement multiplicatively. Matches biology-flavored
    efficiency-scaling. -/
noncomputable def multiplicativeCeilingResidue : CeilingResiduePolicy where
  effectiveDissolution r res := (dissolutionThreshold r).val * (1 - res.val)
  boundary_at_zero r := by simp
  monotone_residue r res₁ res₂ h := by
    have h_d_nn : 0 ≤ (dissolutionThreshold r).val := le_of_lt (dissolutionThreshold_pos r)
    have : (1 : ℝ) - res₂.val ≤ 1 - res₁.val := by linarith
    exact mul_le_mul_of_nonneg_left this h_d_nn
  bounded r res := by
    have h_d_nn : 0 ≤ (dissolutionThreshold r).val := le_of_lt (dissolutionThreshold_pos r)
    have h_res_nn : 0 ≤ res.val := res.pos
    have : (dissolutionThreshold r).val * (1 - res.val) ≤ (dissolutionThreshold r).val * 1 := by
      exact mul_le_mul_of_nonneg_left (by linarith) h_d_nn
    linarith
  nonneg r res := by
    have h_d_nn : 0 ≤ (dissolutionThreshold r).val := le_of_lt (dissolutionThreshold_pos r)
    have h_res_le1 : res.val ≤ 1 := res.le1
    exact mul_nonneg h_d_nn (by linarith)

-- ════════════════════════════════════════════════════════════════
-- §HM11. EXTENDED BASIN + EXTENDED MAINTENANCE
-- ExtendedBasin is a strictly weaker premise than Basin (extends the
-- maintenance basin downward by the ceiling-residue mechanism).
-- ════════════════════════════════════════════════════════════════

/-- **Extended basin** under a ceiling-residue policy: substrate is at
    least the *effective* dissolution threshold (which is ≤ formal
    dissolution, and ≥ 0). Strictly weaker than `Basin` — see
    `basin_implies_extendedBasin`. -/
def ExtendedBasin (policy : CeilingResiduePolicy) {r : Region}
    (s : HOAState r) : Prop :=
  policy.effectiveDissolution r s.ceilingResidue ≤ s.substrate.val

/-- Any state satisfying formal `Basin` also satisfies `ExtendedBasin`
    under any policy — ExtendedBasin strictly extends the (B'') basin. -/
theorem basin_implies_extendedBasin (policy : CeilingResiduePolicy)
    {r : Region} (s : HOAState r) : Basin s → ExtendedBasin policy s := by
  intro h_basin
  unfold Basin ExtendedBasin at *
  have := policy.bounded r s.ceilingResidue
  linarith

/-- **Extended autocatalytic-maintenance rule** — the load-bearing axiom
    for ceiling residue, analogous to how `hoaPreservedByBasinMove_ifFeedbackEngaged`
    was an axiom at (B') before (B'') discharged it. Says: if HOA exists,
    feedback is engaged, and the next state satisfies ExtendedBasin
    (substrate at or above the effective dissolution set by ceiling
    residue), then the next state also has an existing HOA.

    Discharging this axiom to a theorem requires formalizing the Path-A
    structural-restructuring mechanism (how ceiling residue makes the loop
    more efficient per substrate unit) — a future formalization pass
    analogous to (B'')'s discharge of the aggregate-weight axiom via
    `AutocatalyticCombine`. -/
axiom hoaPreservedByExtendedBasinMove_ifFeedbackEngaged
    (policy : CeilingResiduePolicy) {r : Region} (c : AutocatalyticCombine) :
    ∀ (s s' : HOAState r),
      HOAExists c s → HOAMove s s' → feedbackEngaged c s s' →
      ExtendedBasin policy s' → HOAExists c s'

/-- The HOA extended-maintenance property, parametric on both the
    combining operator AND the ceiling-residue policy. Reads: for any
    state with existing HOA and extended-basin, every move-sequence with
    engaged feedback that stays in extended-basin preserves HOAExists. -/
def HOAMaintainedExtended {r : Region} (c : AutocatalyticCombine)
    (policy : CeilingResiduePolicy)
    (Moves : HOAState r → HOAState r → Prop) : Prop :=
  MaintainedWithinIfPreserved (ExtendedBasin policy) (HOAExists c) Moves
    (feedbackEngaged c)

/-- **The extended maintenance theorem.** Under the extended
    autocatalytic-maintenance rule (axiomatic here), `HOAMove` maintains
    HOA existence under `ExtendedBasin`. Strictly stronger than
    `hoaMaintainedWithin` (broader basin). Proof: trivial induction. -/
theorem hoaMaintainedExtended {r : Region} (c : AutocatalyticCombine)
    (policy : CeilingResiduePolicy) :
    HOAMaintainedExtended c policy (@HOAMove r) := by
  intro s hoa_s ext_basin_s trace tr_0 tr_moves tr_ext_basin tr_feedback i
  induction i with
  | zero =>
      rw [tr_0]; exact hoa_s
  | succ n ih =>
      exact hoaPreservedByExtendedBasinMove_ifFeedbackEngaged policy c
        (trace n) (trace (n+1)) ih (tr_moves n) (tr_feedback n)
        (tr_ext_basin (n+1))

-- ════════════════════════════════════════════════════════════════
-- §HM12. B₃-SUBSTRATE PROSTHETIC POLICY — widest-window basin extension
-- (Hysteresis § 3.3). Formal B₃ layer (constitution, bylaws, roles)
-- reduces the informal substrate requirement — but not below an
-- irreducible minimum (a formal structure "rejected by all informal
-- networks is paper without power"). Σ-actor-only mechanism, handled
-- implicitly: for A-actors, formalB3Substrate = 0 makes the mechanism
-- vacuous via boundary_at_zero.
--
-- Distinguishing structural feature vs §HM9 CeilingResiduePolicy: the
-- 5th and 6th axioms (irreducibleMinimum_pos and bounded_below_by_
-- irreducible) — ceiling residue policies can reach zero effective
-- dissolution; B₃-substrate policies cannot. This is the "not infinite"
-- claim of Hysteresis.md § 3.3 formalized.
-- ════════════════════════════════════════════════════════════════

/-- Abstract B₃-substrate prosthetic policy. Extends the four
    `CeilingResiduePolicy` axioms with an irreducible minimum: no matter
    how developed the formal layer, there is always some informal
    substrate below which the prosthetic cannot save the cycle.
    See vault: `B3SubstrateProsthetic.md`. -/
structure B3SubstratePolicy where
  /-- Effective dissolution threshold as a function of formal B₃ substrate. -/
  effectiveDissolution : Region → CouplingWeight → ℝ
  /-- The irreducible minimum informal substrate (the "not infinite"
      constraint — Hysteresis.md § 3.3: "a formal structure rejected by
      all informal networks is paper without power"). -/
  irreducibleMinimum : Region → ℝ
  /-- The irreducible minimum is strictly positive. -/
  irreducibleMinimum_pos :
    ∀ (r : Region), 0 < irreducibleMinimum r
  /-- The irreducible minimum is at most the formal dissolution threshold. -/
  irreducibleMinimum_below_dissolution :
    ∀ (r : Region), irreducibleMinimum r ≤ (dissolutionThreshold r).val
  /-- At zero formal B₃ substrate, effective dissolution equals formal
      dissolution (mechanism vacuous; specifically vacuous for A-actors). -/
  boundary_at_zero :
    ∀ (r : Region),
      effectiveDissolution r ⟨0, le_refl 0, zero_le_one⟩ = (dissolutionThreshold r).val
  /-- More formal substrate → not-more effective dissolution. -/
  monotone_b3 :
    ∀ (r : Region) (res₁ res₂ : CouplingWeight),
      res₁.val ≤ res₂.val →
      effectiveDissolution r res₂ ≤ effectiveDissolution r res₁
  /-- Bounded above by formal dissolution. -/
  bounded_above :
    ∀ (r : Region) (res : CouplingWeight),
      effectiveDissolution r res ≤ (dissolutionThreshold r).val
  /-- **The § 3.3 distinguishing constraint**: bounded below by the
      irreducible minimum. § 3.2's CeilingResiduePolicy has no analog. -/
  bounded_below_by_irreducible :
    ∀ (r : Region) (res : CouplingWeight),
      irreducibleMinimum r ≤ effectiveDissolution r res

-- ════════════════════════════════════════════════════════════════
-- §HM13. TWO CANONICAL INSTANCES — parametric over irreducibleMinimum
-- Instances take an irreducibleMinimum axiom as input, so peer-specific
-- calibration remains open.
-- ════════════════════════════════════════════════════════════════

/-- **Linear-floored** B₃-substrate policy:
    `effective = max(irreducibleMinimum, formal - formalB3Substrate)`.
    Formal B₃ substrate reduces the informal requirement one-for-one,
    floored at the irreducible minimum. -/
noncomputable def linearFlooredB3Substrate
    (irrMin : Region → ℝ)
    (irrMin_pos : ∀ r, 0 < irrMin r)
    (irrMin_below : ∀ r, irrMin r ≤ (dissolutionThreshold r).val)
    : B3SubstratePolicy where
  effectiveDissolution r res := max (irrMin r) ((dissolutionThreshold r).val - res.val)
  irreducibleMinimum := irrMin
  irreducibleMinimum_pos := irrMin_pos
  irreducibleMinimum_below_dissolution := irrMin_below
  boundary_at_zero r := by
    simp
    exact irrMin_below r
  monotone_b3 r res₁ res₂ h := by
    have : (dissolutionThreshold r).val - res₂.val ≤ (dissolutionThreshold r).val - res₁.val := by
      linarith
    exact max_le_max (le_refl (irrMin r)) this
  bounded_above r res := by
    have h_res_nn : 0 ≤ res.val := res.pos
    have h1 : (dissolutionThreshold r).val - res.val ≤ (dissolutionThreshold r).val := by linarith
    exact max_le (irrMin_below r) h1
  bounded_below_by_irreducible r res := le_max_left _ _

/-- **Multiplicative-floored** B₃-substrate policy:
    `effective = max(irreducibleMinimum, formal * (1 - formalB3Substrate))`.
    Formal B₃ substrate scales down the informal requirement
    multiplicatively, floored at the irreducible minimum. Reads as "the
    formal layer proportionally substitutes for informal coordination." -/
noncomputable def multiplicativeFlooredB3Substrate
    (irrMin : Region → ℝ)
    (irrMin_pos : ∀ r, 0 < irrMin r)
    (irrMin_below : ∀ r, irrMin r ≤ (dissolutionThreshold r).val)
    : B3SubstratePolicy where
  effectiveDissolution r res := max (irrMin r) ((dissolutionThreshold r).val * (1 - res.val))
  irreducibleMinimum := irrMin
  irreducibleMinimum_pos := irrMin_pos
  irreducibleMinimum_below_dissolution := irrMin_below
  boundary_at_zero r := by
    simp
    exact irrMin_below r
  monotone_b3 r res₁ res₂ h := by
    have h_d_nn : 0 ≤ (dissolutionThreshold r).val := le_of_lt (dissolutionThreshold_pos r)
    have : (1 : ℝ) - res₂.val ≤ 1 - res₁.val := by linarith
    have : (dissolutionThreshold r).val * (1 - res₂.val) ≤ (dissolutionThreshold r).val * (1 - res₁.val) :=
      mul_le_mul_of_nonneg_left this h_d_nn
    exact max_le_max (le_refl (irrMin r)) this
  bounded_above r res := by
    have h_d_nn : 0 ≤ (dissolutionThreshold r).val := le_of_lt (dissolutionThreshold_pos r)
    have h_res_nn : 0 ≤ res.val := res.pos
    have h_1_sub : (1 : ℝ) - res.val ≤ 1 := by linarith
    have h_mul : (dissolutionThreshold r).val * (1 - res.val) ≤ (dissolutionThreshold r).val * 1 :=
      mul_le_mul_of_nonneg_left h_1_sub h_d_nn
    have h_prod : (dissolutionThreshold r).val * (1 - res.val) ≤ (dissolutionThreshold r).val := by
      linarith
    exact max_le (irrMin_below r) h_prod
  bounded_below_by_irreducible r res := le_max_left _ _

-- ════════════════════════════════════════════════════════════════
-- §HM14. FORMAL-EXTENDED BASIN + EXTENDED MAINTENANCE (Σ-actor tier)
-- Parallel structure to §HM11 ceiling-residue extension.
-- ════════════════════════════════════════════════════════════════

/-- **Formal-extended basin** under a B₃-substrate prosthetic policy:
    substrate is at least the effective dissolution set by the formal
    layer (which is between the policy's `irreducibleMinimum` and formal
    dissolution). Applies to Σ-actor HOAs (A-actors have
    `formalB3Substrate = 0`, so `boundary_at_zero` makes `FormalExtendedBasin`
    reduce to `Basin`). -/
def FormalExtendedBasin (policy : B3SubstratePolicy) {r : Region}
    (s : HOAState r) : Prop :=
  policy.effectiveDissolution r s.formalB3Substrate ≤ s.substrate.val

/-- **Extended autocatalytic-maintenance rule for the B₃-substrate
    mechanism** — the load-bearing axiom for § 3.3, analogous to
    `hoaPreservedByExtendedBasinMove_ifFeedbackEngaged` (§ 3.2) and
    `hoaPreservedByBasinMove_ifFeedbackEngaged` (§ 3.1 before (B'')
    discharged it). Discharging requires formalizing co-inscription
    dynamics and the crossover event — future work. -/
axiom hoaPreservedByFormalExtendedBasinMove_ifFeedbackEngaged
    (policy : B3SubstratePolicy) {r : Region} (c : AutocatalyticCombine) :
    ∀ (s s' : HOAState r),
      HOAExists c s → HOAMove s s' → feedbackEngaged c s s' →
      FormalExtendedBasin policy s' → HOAExists c s'

/-- The HOA formal-extended-maintenance property, parametric on both the
    combining operator AND the B₃-substrate policy. -/
def HOAMaintainedFormalExtended {r : Region} (c : AutocatalyticCombine)
    (policy : B3SubstratePolicy)
    (Moves : HOAState r → HOAState r → Prop) : Prop :=
  MaintainedWithinIfPreserved (FormalExtendedBasin policy) (HOAExists c) Moves
    (feedbackEngaged c)

/-- **The formal-extended maintenance theorem** (§ 3.3 basin extension).
    Under the (axiomatic) `hoaPreservedByFormalExtendedBasinMove_ifFeedbackEngaged`,
    `HOAMove` maintains HOA existence under `FormalExtendedBasin`. Proof:
    trivial induction. -/
theorem hoaMaintainedFormalExtended {r : Region} (c : AutocatalyticCombine)
    (policy : B3SubstratePolicy) :
    HOAMaintainedFormalExtended c policy (@HOAMove r) := by
  intro s hoa_s fmt_basin_s trace tr_0 tr_moves tr_fmt_basin tr_feedback i
  induction i with
  | zero =>
      rw [tr_0]; exact hoa_s
  | succ n ih =>
      exact hoaPreservedByFormalExtendedBasinMove_ifFeedbackEngaged policy c
        (trace n) (trace (n+1)) ih (tr_moves n) (tr_feedback n)
        (tr_fmt_basin (n+1))

-- ════════════════════════════════════════════════════════════════
-- §HM15. COMPOSITE BASIN-EXTENSION POLICY — composing § 3.2 with § 3.3
-- Hysteresis.md open question #2: when a state has BOTH ceiling residue
-- AND formal B₃ substrate, what is the joint effective dissolution?
-- The vault answer is OPEN — this formalization ships scaffolding
-- (abstract policy + three candidate instances) without settling which
-- composition is theoretically correct.
--
-- Three axioms: bounded_above_by_min (sanity — composite is at least as
-- permissive as either individual mechanism), monotone_in_ceiling_residue,
-- monotone_in_b3_substrate. Deliberately NO floor axiom — each instance
-- handles floors as it sees fit.
-- ════════════════════════════════════════════════════════════════

/-- Abstract composition of a `CeilingResiduePolicy` (§ 3.2) and a
    `B3SubstratePolicy` (§ 3.3) into a joint effective dissolution. SCORE
    does not commit to which composition is theoretically correct — the
    abstract structure captures the SHAPE (three monotonicity axioms)
    with peer-selectable canonical instances (§HM16). See vault:
    `HysteresisComposition.md`. -/
structure CompositeBasinExtensionPolicy where
  /-- Joint effective dissolution as a function of both policies and their
      state inputs. -/
  compose : CeilingResiduePolicy → B3SubstratePolicy → Region →
            CouplingWeight → CouplingWeight → ℝ
  /-- **Sanity constraint**: the composite is at most the minimum of the
      two individual effective dissolutions — i.e., at least as permissive
      as either mechanism alone. Rules out compositions that make things
      worse. -/
  bounded_above_by_min :
    ∀ (p_r : CeilingResiduePolicy) (p_b : B3SubstratePolicy) (r : Region)
      (res_r res_b : CouplingWeight),
      compose p_r p_b r res_r res_b ≤
        min (p_r.effectiveDissolution r res_r) (p_b.effectiveDissolution r res_b)
  /-- More ceiling residue → not-more composite (§ 3.2's monotonicity
      carries through the composition). -/
  monotone_in_ceiling_residue :
    ∀ (p_r : CeilingResiduePolicy) (p_b : B3SubstratePolicy) (r : Region)
      (res_r₁ res_r₂ res_b : CouplingWeight),
      res_r₁.val ≤ res_r₂.val →
      compose p_r p_b r res_r₂ res_b ≤ compose p_r p_b r res_r₁ res_b
  /-- More formal B₃ substrate → not-more composite (§ 3.3's monotonicity
      carries through). -/
  monotone_in_b3_substrate :
    ∀ (p_r : CeilingResiduePolicy) (p_b : B3SubstratePolicy) (r : Region)
      (res_r res_b₁ res_b₂ : CouplingWeight),
      res_b₁.val ≤ res_b₂.val →
      compose p_r p_b r res_r res_b₂ ≤ compose p_r p_b r res_r res_b₁

-- ════════════════════════════════════════════════════════════════
-- §HM16. THREE CANONICAL INSTANCES — peer-selectable, not SCORE
-- theoretical commitments. Each corresponds to one of the three candidate
-- composition shapes documented in HysteresisComposition.md.
-- ════════════════════════════════════════════════════════════════

/-- **Min / most-permissive composition** — `compose = min(d_r, d_b)`.
    The vault-friendliest reading (fallback hierarchy). All three abstract
    axioms trivial. -/
noncomputable def compositeMin : CompositeBasinExtensionPolicy where
  compose p_r p_b r res_r res_b :=
    min (p_r.effectiveDissolution r res_r) (p_b.effectiveDissolution r res_b)
  bounded_above_by_min p_r p_b r res_r res_b := le_refl _
  monotone_in_ceiling_residue p_r p_b r res_r₁ res_r₂ res_b h := by
    have h_r : p_r.effectiveDissolution r res_r₂ ≤ p_r.effectiveDissolution r res_r₁ :=
      p_r.monotone_residue r res_r₁ res_r₂ h
    exact min_le_min h_r (le_refl _)
  monotone_in_b3_substrate p_r p_b r res_r res_b₁ res_b₂ h := by
    have h_b : p_b.effectiveDissolution r res_b₂ ≤ p_b.effectiveDissolution r res_b₁ :=
      p_b.monotone_b3 r res_b₁ res_b₂ h
    exact min_le_min (le_refl _) h_b

/-- **Additive-reductions composition** — `compose = max(0, d_r + d_b − d_f)`.
    Reductions from formal dissolution sum, floored at zero. Reads as
    "mechanisms contribute independently to substrate reduction." -/
noncomputable def compositeAdditiveReductions : CompositeBasinExtensionPolicy where
  compose p_r p_b r res_r res_b :=
    max 0 (p_r.effectiveDissolution r res_r + p_b.effectiveDissolution r res_b
           - (dissolutionThreshold r).val)
  bounded_above_by_min p_r p_b r res_r res_b := by
    have h_r_bound : p_r.effectiveDissolution r res_r ≤ (dissolutionThreshold r).val :=
      p_r.bounded r res_r
    have h_b_bound : p_b.effectiveDissolution r res_b ≤ (dissolutionThreshold r).val :=
      p_b.bounded_above r res_b
    have h_r_nn : 0 ≤ p_r.effectiveDissolution r res_r := p_r.nonneg r res_r
    have h_b_nn_of_irr : 0 < p_b.irreducibleMinimum r := p_b.irreducibleMinimum_pos r
    have h_b_nn : 0 ≤ p_b.effectiveDissolution r res_b :=
      le_trans (le_of_lt h_b_nn_of_irr) (p_b.bounded_below_by_irreducible r res_b)
    -- max(0, r_eff + b_eff - formal) ≤ min(r_eff, b_eff)
    -- Case (r_eff + b_eff - formal ≤ 0): max = 0 ≤ min (since both non-negative)
    -- Case (r_eff + b_eff - formal ≥ 0): max = that, ≤ r_eff (since b_eff ≤ formal), ≤ b_eff similarly
    have h_le_r : p_r.effectiveDissolution r res_r + p_b.effectiveDissolution r res_b
                    - (dissolutionThreshold r).val ≤ p_r.effectiveDissolution r res_r := by linarith
    have h_le_b : p_r.effectiveDissolution r res_r + p_b.effectiveDissolution r res_b
                    - (dissolutionThreshold r).val ≤ p_b.effectiveDissolution r res_b := by linarith
    have h_0_le_r : (0 : ℝ) ≤ p_r.effectiveDissolution r res_r := h_r_nn
    have h_0_le_b : (0 : ℝ) ≤ p_b.effectiveDissolution r res_b := h_b_nn
    exact max_le
      (le_min h_0_le_r h_0_le_b)
      (le_min h_le_r h_le_b)
  monotone_in_ceiling_residue p_r p_b r res_r₁ res_r₂ res_b h := by
    have h_r : p_r.effectiveDissolution r res_r₂ ≤ p_r.effectiveDissolution r res_r₁ :=
      p_r.monotone_residue r res_r₁ res_r₂ h
    have h_sum : p_r.effectiveDissolution r res_r₂ + p_b.effectiveDissolution r res_b
                 - (dissolutionThreshold r).val
                 ≤ p_r.effectiveDissolution r res_r₁ + p_b.effectiveDissolution r res_b
                 - (dissolutionThreshold r).val := by linarith
    exact max_le_max (le_refl 0) h_sum
  monotone_in_b3_substrate p_r p_b r res_r res_b₁ res_b₂ h := by
    have h_b : p_b.effectiveDissolution r res_b₂ ≤ p_b.effectiveDissolution r res_b₁ :=
      p_b.monotone_b3 r res_b₁ res_b₂ h
    have h_sum : p_r.effectiveDissolution r res_r + p_b.effectiveDissolution r res_b₂
                 - (dissolutionThreshold r).val
                 ≤ p_r.effectiveDissolution r res_r + p_b.effectiveDissolution r res_b₁
                 - (dissolutionThreshold r).val := by linarith
    exact max_le_max (le_refl 0) h_sum

/-- **Multiplicative-factors composition** — `compose = d_r × d_b / d_f`.
    Reduction factors multiply. Uses `dissolutionThreshold_pos` for the
    division. Non-negative and ≤ min trivially. -/
noncomputable def compositeMultiplicativeFactors : CompositeBasinExtensionPolicy where
  compose p_r p_b r res_r res_b :=
    p_r.effectiveDissolution r res_r * p_b.effectiveDissolution r res_b
      / (dissolutionThreshold r).val
  bounded_above_by_min p_r p_b r res_r res_b := by
    have h_d_pos : 0 < (dissolutionThreshold r).val := dissolutionThreshold_pos r
    have h_r_bound : p_r.effectiveDissolution r res_r ≤ (dissolutionThreshold r).val :=
      p_r.bounded r res_r
    have h_b_bound : p_b.effectiveDissolution r res_b ≤ (dissolutionThreshold r).val :=
      p_b.bounded_above r res_b
    have h_r_nn : 0 ≤ p_r.effectiveDissolution r res_r := p_r.nonneg r res_r
    have h_b_nn : 0 ≤ p_b.effectiveDissolution r res_b :=
      le_trans (le_of_lt (p_b.irreducibleMinimum_pos r))
               (p_b.bounded_below_by_irreducible r res_b)
    -- Goal: r_eff * b_eff / formal ≤ min(r_eff, b_eff)
    -- ≤ r_eff since (b_eff / formal ≤ 1) and r_eff ≥ 0
    have h_bf_le_1 : p_b.effectiveDissolution r res_b / (dissolutionThreshold r).val ≤ 1 :=
      (div_le_one h_d_pos).mpr h_b_bound
    have h_le_r : p_r.effectiveDissolution r res_r * p_b.effectiveDissolution r res_b
                    / (dissolutionThreshold r).val ≤ p_r.effectiveDissolution r res_r := by
      rw [mul_div_assoc]
      calc p_r.effectiveDissolution r res_r *
              (p_b.effectiveDissolution r res_b / (dissolutionThreshold r).val)
            ≤ p_r.effectiveDissolution r res_r * 1 := by
              exact mul_le_mul_of_nonneg_left h_bf_le_1 h_r_nn
        _ = p_r.effectiveDissolution r res_r := by ring
    have h_rf_le_1 : p_r.effectiveDissolution r res_r / (dissolutionThreshold r).val ≤ 1 :=
      (div_le_one h_d_pos).mpr h_r_bound
    have h_le_b : p_r.effectiveDissolution r res_r * p_b.effectiveDissolution r res_b
                    / (dissolutionThreshold r).val ≤ p_b.effectiveDissolution r res_b := by
      have h_swap : p_r.effectiveDissolution r res_r * p_b.effectiveDissolution r res_b
                     = p_b.effectiveDissolution r res_b * p_r.effectiveDissolution r res_r := by ring
      rw [h_swap, mul_div_assoc]
      calc p_b.effectiveDissolution r res_b *
              (p_r.effectiveDissolution r res_r / (dissolutionThreshold r).val)
            ≤ p_b.effectiveDissolution r res_b * 1 := by
              exact mul_le_mul_of_nonneg_left h_rf_le_1 h_b_nn
        _ = p_b.effectiveDissolution r res_b := by ring
    exact le_min h_le_r h_le_b
  monotone_in_ceiling_residue p_r p_b r res_r₁ res_r₂ res_b h := by
    have h_d_pos : 0 < (dissolutionThreshold r).val := dissolutionThreshold_pos r
    have h_r : p_r.effectiveDissolution r res_r₂ ≤ p_r.effectiveDissolution r res_r₁ :=
      p_r.monotone_residue r res_r₁ res_r₂ h
    have h_b_nn : 0 ≤ p_b.effectiveDissolution r res_b :=
      le_trans (le_of_lt (p_b.irreducibleMinimum_pos r))
               (p_b.bounded_below_by_irreducible r res_b)
    have h_num : p_r.effectiveDissolution r res_r₂ * p_b.effectiveDissolution r res_b
                  ≤ p_r.effectiveDissolution r res_r₁ * p_b.effectiveDissolution r res_b :=
      mul_le_mul_of_nonneg_right h_r h_b_nn
    exact div_le_div_of_nonneg_right h_num (le_of_lt h_d_pos)
  monotone_in_b3_substrate p_r p_b r res_r res_b₁ res_b₂ h := by
    have h_d_pos : 0 < (dissolutionThreshold r).val := dissolutionThreshold_pos r
    have h_b : p_b.effectiveDissolution r res_b₂ ≤ p_b.effectiveDissolution r res_b₁ :=
      p_b.monotone_b3 r res_b₁ res_b₂ h
    have h_r_nn : 0 ≤ p_r.effectiveDissolution r res_r := p_r.nonneg r res_r
    have h_num : p_r.effectiveDissolution r res_r * p_b.effectiveDissolution r res_b₂
                  ≤ p_r.effectiveDissolution r res_r * p_b.effectiveDissolution r res_b₁ :=
      mul_le_mul_of_nonneg_left h_b h_r_nn
    exact div_le_div_of_nonneg_right h_num (le_of_lt h_d_pos)

-- ════════════════════════════════════════════════════════════════
-- §HM17. COMPOSITELY-EXTENDED BASIN + COMPOSITE MAINTENANCE
-- Parallel structure to §HM11 (§ 3.2) and §HM14 (§ 3.3).
-- ════════════════════════════════════════════════════════════════

/-- **Compositely-extended basin** under a composition operator + both
    individual policies: substrate is at least the composite effective
    dissolution. At least as permissive as either individual extended
    basin (by `bounded_above_by_min`). -/
def CompositelyExtendedBasin (comp : CompositeBasinExtensionPolicy)
    (p_r : CeilingResiduePolicy) (p_b : B3SubstratePolicy)
    {r : Region} (s : HOAState r) : Prop :=
  comp.compose p_r p_b r s.ceilingResidue s.formalB3Substrate ≤ s.substrate.val

/-- Any state satisfying `ExtendedBasin p_r` (§ 3.2) also satisfies
    `CompositelyExtendedBasin` under any composition — the composite is at
    least as permissive as § 3.2 alone. -/
theorem extendedBasin_implies_compositelyExtendedBasin
    (comp : CompositeBasinExtensionPolicy)
    (p_r : CeilingResiduePolicy) (p_b : B3SubstratePolicy)
    {r : Region} (s : HOAState r) :
    ExtendedBasin p_r s → CompositelyExtendedBasin comp p_r p_b s := by
  intro h_ext
  unfold ExtendedBasin CompositelyExtendedBasin at *
  have h_min := comp.bounded_above_by_min p_r p_b r s.ceilingResidue s.formalB3Substrate
  have h_min_le_r : min (p_r.effectiveDissolution r s.ceilingResidue)
                        (p_b.effectiveDissolution r s.formalB3Substrate)
                    ≤ p_r.effectiveDissolution r s.ceilingResidue := min_le_left _ _
  linarith

/-- Any state satisfying `FormalExtendedBasin p_b` (§ 3.3) also satisfies
    `CompositelyExtendedBasin` under any composition — the composite is at
    least as permissive as § 3.3 alone. -/
theorem formalExtendedBasin_implies_compositelyExtendedBasin
    (comp : CompositeBasinExtensionPolicy)
    (p_r : CeilingResiduePolicy) (p_b : B3SubstratePolicy)
    {r : Region} (s : HOAState r) :
    FormalExtendedBasin p_b s → CompositelyExtendedBasin comp p_r p_b s := by
  intro h_fmt
  unfold FormalExtendedBasin CompositelyExtendedBasin at *
  have h_min := comp.bounded_above_by_min p_r p_b r s.ceilingResidue s.formalB3Substrate
  have h_min_le_b : min (p_r.effectiveDissolution r s.ceilingResidue)
                        (p_b.effectiveDissolution r s.formalB3Substrate)
                    ≤ p_b.effectiveDissolution r s.formalB3Substrate := min_le_right _ _
  linarith

/-- **Composite autocatalytic-maintenance rule** — the load-bearing axiom
    for the composed mechanisms. Analogous to §HM11 and §HM14's axioms.
    Discharge would require the composition rule to be *settled*
    (Hysteresis.md open question #2) — currently peer-selected. -/
axiom hoaPreservedByCompositelyExtendedBasinMove_ifFeedbackEngaged
    (comp : CompositeBasinExtensionPolicy)
    (p_r : CeilingResiduePolicy) (p_b : B3SubstratePolicy)
    {r : Region} (c : AutocatalyticCombine) :
    ∀ (s s' : HOAState r),
      HOAExists c s → HOAMove s s' → feedbackEngaged c s s' →
      CompositelyExtendedBasin comp p_r p_b s' → HOAExists c s'

/-- The HOA composite-maintenance property. Parametric on the combining
    operator, the composition policy, and both individual policies. -/
def HOAMaintainedCompositelyExtended {r : Region} (c : AutocatalyticCombine)
    (comp : CompositeBasinExtensionPolicy)
    (p_r : CeilingResiduePolicy) (p_b : B3SubstratePolicy)
    (Moves : HOAState r → HOAState r → Prop) : Prop :=
  MaintainedWithinIfPreserved (CompositelyExtendedBasin comp p_r p_b)
    (HOAExists c) Moves (feedbackEngaged c)

/-- **The composite maintenance theorem.** Under the (axiomatic)
    composite preservation rule, `HOAMove` maintains HOA existence under
    `CompositelyExtendedBasin`. Strictly stronger than either
    `hoaMaintainedExtended` (§ 3.2) or `hoaMaintainedFormalExtended`
    (§ 3.3) alone. Proof: trivial induction. -/
theorem hoaMaintainedCompositelyExtended {r : Region} (c : AutocatalyticCombine)
    (comp : CompositeBasinExtensionPolicy)
    (p_r : CeilingResiduePolicy) (p_b : B3SubstratePolicy) :
    HOAMaintainedCompositelyExtended c comp p_r p_b (@HOAMove r) := by
  intro s hoa_s comp_basin_s trace tr_0 tr_moves tr_comp_basin tr_feedback i
  induction i with
  | zero =>
      rw [tr_0]; exact hoa_s
  | succ n ih =>
      exact hoaPreservedByCompositelyExtendedBasinMove_ifFeedbackEngaged comp p_r p_b c
        (trace n) (trace (n+1)) ih (tr_moves n) (tr_feedback n)
        (tr_comp_basin (n+1))

-- ════════════════════════════════════════════════════════════════
-- §HM18. DISCHARGE MACHINERY — § 3.2 ceiling residue, canonical
-- (combineAdditive × linearCeilingResidue) pair
--
-- Discharges `hoaPreservedByExtendedBasinMove_ifFeedbackEngaged` from
-- axiom to derived theorem — for the additive × linear canonical pair.
-- Parallels (B'')'s discharge of § 3.1's axiom via AutocatalyticCombine.
--
-- The load-bearing content moves from the maintenance-level axiom to a
-- compatibility-axiom on a `ResidueAugmentedCombine` — an "extended
-- combining operator" that takes ceilingResidue as an additional input.
-- For concrete (combine, policy) pairs, the compatibility axiom is
-- provable arithmetic.
--
-- Scope: only the (combineAdditive, linearCeilingResidue) pair is
-- discharged here. Other pairs (multiplicative × multiplicative etc.)
-- remain axiomatic pending their own discharge PRs. The universal axiom
-- `hoaPreservedByExtendedBasinMove_ifFeedbackEngaged` (§HM11) is kept
-- for arbitrary (c, p) — the discharged pair simply has a derived
-- theorem that doesn't depend on it.
-- ════════════════════════════════════════════════════════════════

/-- Extended combining operator that takes ceiling residue as a third
    input. Parametric over a base `AutocatalyticCombine` (`c`) and a
    `CeilingResiduePolicy` (`p`). At zero residue, agrees with the base
    combine (`boundary_at_zero`); the load-bearing property is
    `closes_extended_gap`, which strengthens the base's
    `closes_hysteresis_gap` to work at substrate as low as
    `p.effectiveDissolution r residue`. For concrete (c, p) pairs, the
    two properties are provable arithmetic. -/
structure ResidueAugmentedCombine
    (c : AutocatalyticCombine) (p : CeilingResiduePolicy) where
  /-- Extended combine: takes region, substrate, endowment, AND ceiling
      residue. The `Region` parameter allows the extended combine to
      reference per-region thresholds (needed for multiplicative × multiplicative
      discharge, which references `formationThreshold r`). Additive
      instances ignore the region. Reduces to `c.combine` at zero residue. -/
  extendedCombine : Region → CouplingWeight → CouplingWeight → CouplingWeight → ℝ
  /-- At zero residue, `extendedCombine` equals the base `c.combine`. -/
  boundary_at_zero :
    ∀ (r : Region) (s e : CouplingWeight),
      extendedCombine r s e ⟨0, le_refl 0, zero_le_one⟩ = c.combine s e
  /-- **Load-bearing compatibility axiom.** With ceiling residue in play,
      the extended combine reaches formation at substrate as low as the
      policy's `effectiveDissolution` — provided endowment meets the base
      combine's `engagementThreshold`. This is the atomic property that
      derives the § 3.2 maintenance theorem. Provable arithmetic for
      canonical (c, p) pairs. -/
  closes_extended_gap :
    ∀ (r : Region) (substrate endowment residue : CouplingWeight),
      p.effectiveDissolution r residue ≤ substrate.val →
      c.engagementThreshold r ≤ endowment.val →
      (formationThreshold r).val ≤ extendedCombine r substrate endowment residue

/-- **Extended crystallization predicate.** Weight is at least formation
    under the extended combining operator (which accounts for ceiling
    residue). Distinct from base `HOAExists` — the two coincide only at
    zero residue (see `hoaExistsExtended_agrees_at_zero_residue`). -/
def HOAExistsExtended {r : Region}
    {c : AutocatalyticCombine} {p : CeilingResiduePolicy}
    (aug : ResidueAugmentedCombine c p) (s : HOAState r) : Prop :=
  (formationThreshold r).val ≤
    aug.extendedCombine r s.substrate s.loopEndowment s.ceilingResidue

/-- **Consistency lemma.** At zero ceiling residue, `HOAExistsExtended`
    agrees with base `HOAExists` — the extended predicate is a proper
    generalization, not a redefinition. -/
theorem hoaExistsExtended_agrees_at_zero_residue
    {r : Region} {c : AutocatalyticCombine} {p : CeilingResiduePolicy}
    (aug : ResidueAugmentedCombine c p) (s : HOAState r)
    (h_zero : s.ceilingResidue = ⟨0, le_refl 0, zero_le_one⟩) :
    HOAExistsExtended aug s ↔ HOAExists c s := by
  unfold HOAExistsExtended HOAExists HOAState.weight
  rw [h_zero, aug.boundary_at_zero]

/-- **Derived § 3.2 maintenance theorem** — no reliance on the
    `hoaPreservedByExtendedBasinMove_ifFeedbackEngaged` axiom. Given a
    `ResidueAugmentedCombine` instance, the maintenance property follows
    from `closes_extended_gap` by trivial induction. -/
theorem hoaMaintainedExtendedDerived
    {r : Region} {c : AutocatalyticCombine} {p : CeilingResiduePolicy}
    (aug : ResidueAugmentedCombine c p) :
    ∀ (s : HOAState r), HOAExistsExtended aug s → Basin s →
      ∀ trace : ℕ → HOAState r,
        trace 0 = s →
        (∀ i, HOAMove (trace i) (trace (i+1))) →
        (∀ i, ExtendedBasin p (trace i)) →
        (∀ i, feedbackEngaged c (trace i) (trace (i+1))) →
        ∀ i, HOAExistsExtended aug (trace i) := by
  intro s hoa_s _ trace tr_0 _ tr_ext_basin tr_feedback i
  induction i with
  | zero =>
      rw [tr_0]; exact hoa_s
  | succ n ih =>
      unfold HOAExistsExtended
      exact aug.closes_extended_gap r
        (trace (n+1)).substrate (trace (n+1)).loopEndowment
        (trace (n+1)).ceilingResidue
        (tr_ext_basin (n+1)) (tr_feedback n)

-- ════════════════════════════════════════════════════════════════
-- §HM19. CANONICAL DISCHARGED INSTANCE — additive × linear
-- Concrete `ResidueAugmentedCombine combineAdditive linearCeilingResidue`
-- with all axioms proven from arithmetic. This is a REAL DISCHARGE:
-- combined with `hoaMaintainedExtendedDerived`, gives a full maintenance
-- theorem for this pair with no residual axiom.
-- ════════════════════════════════════════════════════════════════

/-- **The canonical additive × linear residue-augmented combine.** For
    the (`combineAdditive`, `linearCeilingResidue`) pair: extended weight
    is simply `substrate + endowment + residue` (residue adds directly to
    aggregate weight). Both `boundary_at_zero` and `closes_extended_gap`
    are provable arithmetic. -/
noncomputable def additiveLinearResidueAugmented :
    ResidueAugmentedCombine combineAdditive linearCeilingResidue where
  extendedCombine _ s e res := s.val + e.val + res.val  -- region-independent
  boundary_at_zero _ s e := by
    show s.val + e.val + (0 : ℝ) = s.val + e.val
    ring
  closes_extended_gap r substrate endowment residue h_basin h_feedback := by
    -- Unfold instance-specific defs
    have h_eff : linearCeilingResidue.effectiveDissolution r residue =
                 max 0 ((dissolutionThreshold r).val - residue.val) := rfl
    have h_eng : combineAdditive.engagementThreshold r =
                 (formationThreshold r).val - (dissolutionThreshold r).val := rfl
    rw [h_eff] at h_basin
    rw [h_eng] at h_feedback
    -- max_right gives: dissolution - residue ≤ max 0 (dissolution - residue) ≤ substrate
    have h_dr_le_substrate : (dissolutionThreshold r).val - residue.val ≤ substrate.val :=
      le_trans (le_max_right 0 _) h_basin
    -- endowment ≥ formation - dissolution; substrate + residue ≥ dissolution;
    -- so substrate + endowment + residue ≥ formation
    show (formationThreshold r).val ≤ substrate.val + endowment.val + residue.val
    linarith

/-- **The multiplicative × multiplicative residue-augmented combine.** For
    the (`combineMultiplicative`, `multiplicativeCeilingResidue`) pair.
    `extendedCombine r s e res := s × (1+e) + formation r × res` — the
    loop's multiplicative interactions on substrate PLUS an additive
    contribution from ceiling residue proportional to formation. The
    non-uniform arithmetic (multiplicative in substrate/endowment,
    additive in residue) is what makes region-dependence necessary in the
    extended combine — the region-independent shapes (`s × (1+e+res)`,
    `s × (1+e) × (1+res)`) do NOT close the gap.
    Interpretively: at maximum residue, the loop contributes `formation`
    weight directly (independent of substrate) — the strongest reading of
    "manifold overlap sets the ceiling." -/
noncomputable def multiplicativeMultiplicativeResidueAugmented :
    ResidueAugmentedCombine combineMultiplicative multiplicativeCeilingResidue where
  extendedCombine r s e res := s.val * (1 + e.val) + (formationThreshold r).val * res.val
  boundary_at_zero r s e := by
    show s.val * (1 + e.val) + (formationThreshold r).val * (0 : ℝ) = s.val * (1 + e.val)
    ring
  closes_extended_gap r substrate endowment res h_basin h_feedback := by
    have h_d_pos : 0 < (dissolutionThreshold r).val := dissolutionThreshold_pos r
    have h_d_nn : 0 ≤ (dissolutionThreshold r).val := le_of_lt h_d_pos
    have h_e_nn : 0 ≤ endowment.val := endowment.pos
    have h_1e_nn : (0 : ℝ) ≤ 1 + endowment.val := by linarith
    have h_res_nn : 0 ≤ res.val := res.pos
    have h_res_le1 : res.val ≤ 1 := res.le1
    have h_1_sub_res_nn : (0 : ℝ) ≤ 1 - res.val := by linarith
    -- Unfold instance-specific defs
    have h_eff : multiplicativeCeilingResidue.effectiveDissolution r res =
                 (dissolutionThreshold r).val * (1 - res.val) := rfl
    have h_eng : combineMultiplicative.engagementThreshold r =
                 ((formationThreshold r).val - (dissolutionThreshold r).val)
                   / (dissolutionThreshold r).val := rfl
    rw [h_eff] at h_basin
    rw [h_eng] at h_feedback
    -- Step 1: dissolution * (1 + endowment) ≥ formation
    -- From h_feedback: (f-d)/d ≤ e; multiply by d>0 to get f-d ≤ e*d
    have h_ed : (formationThreshold r).val - (dissolutionThreshold r).val
                ≤ endowment.val * (dissolutionThreshold r).val := by
      have h_mul := mul_le_mul_of_nonneg_right h_feedback h_d_nn
      rwa [div_mul_cancel₀ _ (ne_of_gt h_d_pos)] at h_mul
    have h_step1 : (formationThreshold r).val ≤
                    (dissolutionThreshold r).val * (1 + endowment.val) := by
      have : (dissolutionThreshold r).val * (1 + endowment.val)
             = (dissolutionThreshold r).val + endowment.val * (dissolutionThreshold r).val := by ring
      linarith
    -- Step 2: substrate * (1+e) ≥ formation * (1 - res)
    have h_step2 : (formationThreshold r).val * (1 - res.val)
                    ≤ substrate.val * (1 + endowment.val) := by
      have h_s_mul : (dissolutionThreshold r).val * (1 - res.val) * (1 + endowment.val)
                     ≤ substrate.val * (1 + endowment.val) :=
        mul_le_mul_of_nonneg_right h_basin h_1e_nn
      have h_reorder : (dissolutionThreshold r).val * (1 - res.val) * (1 + endowment.val)
                       = (dissolutionThreshold r).val * (1 + endowment.val) * (1 - res.val) := by ring
      have h_step1_mul : (formationThreshold r).val * (1 - res.val)
                         ≤ (dissolutionThreshold r).val * (1 + endowment.val) * (1 - res.val) :=
        mul_le_mul_of_nonneg_right h_step1 h_1_sub_res_nn
      linarith [h_reorder ▸ h_s_mul, h_step1_mul]
    -- Step 3: add formation * res to both sides
    show (formationThreshold r).val ≤
         substrate.val * (1 + endowment.val) + (formationThreshold r).val * res.val
    have h_algebra : (formationThreshold r).val * (1 - res.val)
                     + (formationThreshold r).val * res.val = (formationThreshold r).val := by ring
    linarith

/-- **§ 3.2 mixed pair: additive × multiplicative.** For the
    (`combineAdditive`, `multiplicativeCeilingResidue`) pair. Same additive
    extended combine `s + e + res` as the additive × linear discharge —
    additive-combine discharges use the same shape regardless of policy;
    only the arithmetic in `closes_extended_gap` differs. Proof uses
    `dissolution ≤ 1` (CouplingWeight bound) to close the gap. -/
noncomputable def additiveMultiplicativeResidueAugmented :
    ResidueAugmentedCombine combineAdditive multiplicativeCeilingResidue where
  extendedCombine _ s e res := s.val + e.val + res.val
  boundary_at_zero _ s e := by
    show s.val + e.val + (0 : ℝ) = s.val + e.val
    ring
  closes_extended_gap r substrate endowment res h_basin h_feedback := by
    have h_eff : multiplicativeCeilingResidue.effectiveDissolution r res =
                 (dissolutionThreshold r).val * (1 - res.val) := rfl
    have h_eng : combineAdditive.engagementThreshold r =
                 (formationThreshold r).val - (dissolutionThreshold r).val := rfl
    rw [h_eff] at h_basin
    rw [h_eng] at h_feedback
    have h_d_le_1 : (dissolutionThreshold r).val ≤ 1 := (dissolutionThreshold r).le1
    have h_res_nn : (0 : ℝ) ≤ res.val := res.pos
    -- s + e ≥ d*(1-res) + (f-d) = f - d*res; add res: ≥ f + res*(1-d) ≥ f  (since d ≤ 1)
    show (formationThreshold r).val ≤ substrate.val + endowment.val + res.val
    nlinarith

/-- **§ 3.2 mixed pair: multiplicative × linear.** For the
    (`combineMultiplicative`, `linearCeilingResidue`) pair. Divisive
    extended combine: `s × (1+e) + formation × res / dissolution`. Case
    analysis on whether `res ≤ dissolution` (Case A) or `res > dissolution`
    (Case B — substrate lower bound trivializes to 0 via the linear
    policy's `max 0` floor). Both cases close the gap. -/
noncomputable def multiplicativeLinearResidueAugmented :
    ResidueAugmentedCombine combineMultiplicative linearCeilingResidue where
  extendedCombine r s e res :=
    s.val * (1 + e.val) + (formationThreshold r).val * res.val / (dissolutionThreshold r).val
  boundary_at_zero r s e := by
    show s.val * (1 + e.val) + (formationThreshold r).val * (0 : ℝ) / (dissolutionThreshold r).val
         = s.val * (1 + e.val)
    ring
  closes_extended_gap r substrate endowment res h_basin h_feedback := by
    have h_d_pos : 0 < (dissolutionThreshold r).val := dissolutionThreshold_pos r
    have h_d_nn : 0 ≤ (dissolutionThreshold r).val := le_of_lt h_d_pos
    have h_e_nn : 0 ≤ endowment.val := endowment.pos
    have h_1e_nn : (0 : ℝ) ≤ 1 + endowment.val := by linarith
    have h_res_nn : 0 ≤ res.val := res.pos
    have h_s_nn : 0 ≤ substrate.val := substrate.pos
    have h_gap : (dissolutionThreshold r).val < (formationThreshold r).val := hysteresis_gap r
    have h_f_nn : 0 ≤ (formationThreshold r).val := le_of_lt (lt_trans h_d_pos h_gap)
    have h_eff : linearCeilingResidue.effectiveDissolution r res =
                 max 0 ((dissolutionThreshold r).val - res.val) := rfl
    have h_eng : combineMultiplicative.engagementThreshold r =
                 ((formationThreshold r).val - (dissolutionThreshold r).val)
                   / (dissolutionThreshold r).val := rfl
    rw [h_eff] at h_basin
    rw [h_eng] at h_feedback
    have h_1e_ge_fd : (formationThreshold r).val / (dissolutionThreshold r).val
                      ≤ 1 + endowment.val := by
      rw [div_le_iff₀ h_d_pos]
      have h_mul := mul_le_mul_of_nonneg_right h_feedback h_d_nn
      rw [div_mul_cancel₀ _ (ne_of_gt h_d_pos)] at h_mul
      linarith
    have h_fd_nn : 0 ≤ (formationThreshold r).val / (dissolutionThreshold r).val :=
      div_nonneg h_f_nn h_d_nn
    show (formationThreshold r).val ≤
         substrate.val * (1 + endowment.val)
           + (formationThreshold r).val * res.val / (dissolutionThreshold r).val
    by_cases h_case : (dissolutionThreshold r).val ≤ res.val
    · -- Case B: res ≥ d → f * res / d ≥ f
      have h_ratio : 1 ≤ res.val / (dissolutionThreshold r).val := by
        rw [le_div_iff₀ h_d_pos]; linarith
      have h_ge : (formationThreshold r).val
                  ≤ (formationThreshold r).val * res.val / (dissolutionThreshold r).val := by
        have h_rw : (formationThreshold r).val * res.val / (dissolutionThreshold r).val
                    = (formationThreshold r).val * (res.val / (dissolutionThreshold r).val) := by ring
        rw [h_rw]; nlinarith
      have h_ext_nn : 0 ≤ substrate.val * (1 + endowment.val) := mul_nonneg h_s_nn h_1e_nn
      linarith
    · -- Case A: res < d → max = d - res, product bound closes
      push_neg at h_case
      have h_dr_nn : (0 : ℝ) ≤ (dissolutionThreshold r).val - res.val := by linarith
      have h_max_eq : max 0 ((dissolutionThreshold r).val - res.val)
                      = (dissolutionThreshold r).val - res.val := max_eq_right h_dr_nn
      rw [h_max_eq] at h_basin
      have h_prod : ((dissolutionThreshold r).val - res.val)
                    * ((formationThreshold r).val / (dissolutionThreshold r).val)
                    ≤ substrate.val * (1 + endowment.val) :=
        mul_le_mul h_basin h_1e_ge_fd h_fd_nn h_s_nn
      have h_simp : ((dissolutionThreshold r).val - res.val)
                    * ((formationThreshold r).val / (dissolutionThreshold r).val)
                    = (formationThreshold r).val
                      - (formationThreshold r).val * res.val / (dissolutionThreshold r).val := by
        field_simp
      linarith [h_prod, h_simp]

-- ════════════════════════════════════════════════════════════════
-- §HM20. DISCHARGE MACHINERY — § 3.3 B₃-substrate prosthetic,
-- canonical (combineAdditive × linearFlooredB3Substrate) pair
--
-- Parallel to §HM18-19's discharge of § 3.2. Discharges
-- `hoaPreservedByFormalExtendedBasinMove_ifFeedbackEngaged` (§HM14)
-- from axiom to derived theorem — for the additive × linear-floored
-- canonical pair.
--
-- The load-bearing content moves from the maintenance-level axiom to a
-- compatibility axiom on a `B3AugmentedCombine` — an "extended
-- combining operator" that takes formalB3Substrate as an additional
-- input. For concrete (combine, policy) pairs, the compatibility axiom
-- is provable arithmetic.
--
-- Scope: only the (combineAdditive, linearFlooredB3Substrate) pair is
-- discharged here. Other pairs remain axiomatic. The universal §HM14
-- axiom is kept.
-- ════════════════════════════════════════════════════════════════

/-- Extended combining operator that takes formal B₃ substrate as a third
    input. Parametric over a base `AutocatalyticCombine` (`c`) and a
    `B3SubstratePolicy` (`p`). At zero B₃ substrate, agrees with the base
    combine (`boundary_at_zero`); the load-bearing property is
    `closes_extended_gap_b3`, which strengthens the base's
    `closes_hysteresis_gap` to work at substrate as low as
    `p.effectiveDissolution r formalB3`. For concrete (c, p) pairs, the
    two properties are provable arithmetic. -/
structure B3AugmentedCombine
    (c : AutocatalyticCombine) (p : B3SubstratePolicy) where
  /-- Extended combine: takes region, substrate, endowment, AND formal
      B₃ substrate. Region parameter allows referencing per-region
      thresholds (mirrors `ResidueAugmentedCombine`'s region-aware
      design). Additive instances ignore the region. Reduces to
      `c.combine` at zero formalB3. -/
  extendedCombine : Region → CouplingWeight → CouplingWeight → CouplingWeight → ℝ
  /-- At zero formal B₃ substrate, `extendedCombine` equals the base
      `c.combine`. -/
  boundary_at_zero :
    ∀ (r : Region) (s e : CouplingWeight),
      extendedCombine r s e ⟨0, le_refl 0, zero_le_one⟩ = c.combine s e
  /-- **Load-bearing compatibility axiom.** With formal B₃ substrate in
      play, the extended combine reaches formation at substrate as low as
      the B₃-policy's `effectiveDissolution` — provided endowment meets
      the base combine's `engagementThreshold`. Discharges the § 3.3
      maintenance axiom for concrete pairs. -/
  closes_extended_gap_b3 :
    ∀ (r : Region) (substrate endowment formalB3 : CouplingWeight),
      p.effectiveDissolution r formalB3 ≤ substrate.val →
      c.engagementThreshold r ≤ endowment.val →
      (formationThreshold r).val ≤ extendedCombine r substrate endowment formalB3

/-- **Formal-extended crystallization predicate.** Weight is at least
    formation under the extended combining operator (which accounts for
    formal B₃ substrate). Distinct from base `HOAExists` — the two
    coincide only at zero formalB3 (see
    `hoaExistsFormalExtended_agrees_at_zero_b3`). -/
def HOAExistsFormalExtended {r : Region}
    {c : AutocatalyticCombine} {p : B3SubstratePolicy}
    (aug : B3AugmentedCombine c p) (s : HOAState r) : Prop :=
  (formationThreshold r).val ≤
    aug.extendedCombine r s.substrate s.loopEndowment s.formalB3Substrate

/-- **Consistency lemma.** At zero formal B₃ substrate,
    `HOAExistsFormalExtended` agrees with base `HOAExists`. For A-actors
    (which always have `formalB3Substrate = 0`) the extended predicate
    reduces to the base. -/
theorem hoaExistsFormalExtended_agrees_at_zero_b3
    {r : Region} {c : AutocatalyticCombine} {p : B3SubstratePolicy}
    (aug : B3AugmentedCombine c p) (s : HOAState r)
    (h_zero : s.formalB3Substrate = ⟨0, le_refl 0, zero_le_one⟩) :
    HOAExistsFormalExtended aug s ↔ HOAExists c s := by
  unfold HOAExistsFormalExtended HOAExists HOAState.weight
  rw [h_zero, aug.boundary_at_zero]

/-- **Derived § 3.3 maintenance theorem** — no reliance on the
    `hoaPreservedByFormalExtendedBasinMove_ifFeedbackEngaged` axiom.
    Given a `B3AugmentedCombine` instance, the maintenance property
    follows from `closes_extended_gap_b3` by trivial induction. -/
theorem hoaMaintainedFormalExtendedDerived
    {r : Region} {c : AutocatalyticCombine} {p : B3SubstratePolicy}
    (aug : B3AugmentedCombine c p) :
    ∀ (s : HOAState r), HOAExistsFormalExtended aug s → Basin s →
      ∀ trace : ℕ → HOAState r,
        trace 0 = s →
        (∀ i, HOAMove (trace i) (trace (i+1))) →
        (∀ i, FormalExtendedBasin p (trace i)) →
        (∀ i, feedbackEngaged c (trace i) (trace (i+1))) →
        ∀ i, HOAExistsFormalExtended aug (trace i) := by
  intro s hoa_s _ trace tr_0 _ tr_fmt_basin tr_feedback i
  induction i with
  | zero =>
      rw [tr_0]; exact hoa_s
  | succ n ih =>
      unfold HOAExistsFormalExtended
      exact aug.closes_extended_gap_b3 r
        (trace (n+1)).substrate (trace (n+1)).loopEndowment
        (trace (n+1)).formalB3Substrate
        (tr_fmt_basin (n+1)) (tr_feedback n)

-- ════════════════════════════════════════════════════════════════
-- §HM21. CANONICAL DISCHARGED INSTANCE — additive × linear-floored
-- Concrete `B3AugmentedCombine combineAdditive (linearFlooredB3Substrate ...)`
-- with all axioms proven from arithmetic. This is a REAL DISCHARGE:
-- combined with `hoaMaintainedFormalExtendedDerived`, gives a full § 3.3
-- maintenance theorem for this pair with no residual axiom.
-- Parametric on the peer-supplied `irrMin` (inherited from
-- `linearFlooredB3Substrate`'s parametricity).
-- ════════════════════════════════════════════════════════════════

/-- **The canonical additive × linear-floored B₃-augmented combine.** For
    the (`combineAdditive`, `linearFlooredB3Substrate irrMin ...`) pair:
    extended weight is simply `substrate + endowment + formalB3` (formal
    B₃ substrate adds directly to aggregate weight, mirroring the § 3.2
    additive × linear discharge). Both `boundary_at_zero` and
    `closes_extended_gap_b3` are provable arithmetic. Parametric on the
    peer-supplied `irrMin` axioms of `linearFlooredB3Substrate`. -/
noncomputable def additiveLinearFlooredB3Augmented
    (irrMin : Region → ℝ)
    (irrMin_pos : ∀ r, 0 < irrMin r)
    (irrMin_below : ∀ r, irrMin r ≤ (dissolutionThreshold r).val) :
    B3AugmentedCombine combineAdditive
      (linearFlooredB3Substrate irrMin irrMin_pos irrMin_below) where
  extendedCombine _ s e b3 := s.val + e.val + b3.val  -- region-independent
  boundary_at_zero _ s e := by
    show s.val + e.val + (0 : ℝ) = s.val + e.val
    ring
  closes_extended_gap_b3 r substrate endowment b3 h_basin h_feedback := by
    -- Unfold instance-specific defs
    have h_eff : (linearFlooredB3Substrate irrMin irrMin_pos irrMin_below).effectiveDissolution r b3
                 = max (irrMin r) ((dissolutionThreshold r).val - b3.val) := rfl
    have h_eng : combineAdditive.engagementThreshold r =
                 (formationThreshold r).val - (dissolutionThreshold r).val := rfl
    rw [h_eff] at h_basin
    rw [h_eng] at h_feedback
    -- le_max_right gives: dissolution - b3 ≤ max (irrMin r) (dissolution - b3) ≤ substrate
    have h_db_le_substrate : (dissolutionThreshold r).val - b3.val ≤ substrate.val :=
      le_trans (le_max_right _ _) h_basin
    -- endowment ≥ formation - dissolution; substrate + b3 ≥ dissolution;
    -- so substrate + endowment + b3 ≥ formation
    show (formationThreshold r).val ≤ substrate.val + endowment.val + b3.val
    linarith

/-- **The multiplicative × multiplicative-floored B₃-augmented combine.**
    For the (`combineMultiplicative`, `multiplicativeFlooredB3Substrate`)
    pair. Same shape as `multiplicativeMultiplicativeResidueAugmented`
    (§ 3.2): `extendedCombine r s e b3 := s × (1+e) + formation r × b3`.
    Parametric on the peer-supplied `irrMin` axioms. The `irrMin` floor
    is preserved through the policy's `effectiveDissolution` (not the
    extended combine), consistent with the § 3.3 additive × linear
    discharge's floor-handling approach. -/
noncomputable def multiplicativeMultiplicativeFlooredB3Augmented
    (irrMin : Region → ℝ)
    (irrMin_pos : ∀ r, 0 < irrMin r)
    (irrMin_below : ∀ r, irrMin r ≤ (dissolutionThreshold r).val) :
    B3AugmentedCombine combineMultiplicative
      (multiplicativeFlooredB3Substrate irrMin irrMin_pos irrMin_below) where
  extendedCombine r s e b3 := s.val * (1 + e.val) + (formationThreshold r).val * b3.val
  boundary_at_zero r s e := by
    show s.val * (1 + e.val) + (formationThreshold r).val * (0 : ℝ) = s.val * (1 + e.val)
    ring
  closes_extended_gap_b3 r substrate endowment b3 h_basin h_feedback := by
    have h_d_pos : 0 < (dissolutionThreshold r).val := dissolutionThreshold_pos r
    have h_d_nn : 0 ≤ (dissolutionThreshold r).val := le_of_lt h_d_pos
    have h_e_nn : 0 ≤ endowment.val := endowment.pos
    have h_1e_nn : (0 : ℝ) ≤ 1 + endowment.val := by linarith
    have h_b3_nn : 0 ≤ b3.val := b3.pos
    have h_b3_le1 : b3.val ≤ 1 := b3.le1
    have h_1_sub_b3_nn : (0 : ℝ) ≤ 1 - b3.val := by linarith
    -- Unfold instance-specific defs
    have h_eff : (multiplicativeFlooredB3Substrate irrMin irrMin_pos irrMin_below).effectiveDissolution
                    r b3
                 = max (irrMin r) ((dissolutionThreshold r).val * (1 - b3.val)) := rfl
    have h_eng : combineMultiplicative.engagementThreshold r =
                 ((formationThreshold r).val - (dissolutionThreshold r).val)
                   / (dissolutionThreshold r).val := rfl
    rw [h_eff] at h_basin
    rw [h_eng] at h_feedback
    -- max_right: d*(1-b3) ≤ max(irrMin, d*(1-b3)) ≤ substrate
    have h_db_le_substrate : (dissolutionThreshold r).val * (1 - b3.val) ≤ substrate.val :=
      le_trans (le_max_right _ _) h_basin
    -- dissolution * (1 + endowment) ≥ formation (from feedback)
    have h_ed : (formationThreshold r).val - (dissolutionThreshold r).val
                ≤ endowment.val * (dissolutionThreshold r).val := by
      have h_mul := mul_le_mul_of_nonneg_right h_feedback h_d_nn
      rwa [div_mul_cancel₀ _ (ne_of_gt h_d_pos)] at h_mul
    have h_step1 : (formationThreshold r).val ≤
                    (dissolutionThreshold r).val * (1 + endowment.val) := by
      have : (dissolutionThreshold r).val * (1 + endowment.val)
             = (dissolutionThreshold r).val + endowment.val * (dissolutionThreshold r).val := by ring
      linarith
    -- substrate * (1+e) ≥ formation * (1 - b3)
    have h_step2 : (formationThreshold r).val * (1 - b3.val)
                    ≤ substrate.val * (1 + endowment.val) := by
      have h_s_mul : (dissolutionThreshold r).val * (1 - b3.val) * (1 + endowment.val)
                     ≤ substrate.val * (1 + endowment.val) :=
        mul_le_mul_of_nonneg_right h_db_le_substrate h_1e_nn
      have h_reorder : (dissolutionThreshold r).val * (1 - b3.val) * (1 + endowment.val)
                       = (dissolutionThreshold r).val * (1 + endowment.val) * (1 - b3.val) := by ring
      have h_step1_mul : (formationThreshold r).val * (1 - b3.val)
                         ≤ (dissolutionThreshold r).val * (1 + endowment.val) * (1 - b3.val) :=
        mul_le_mul_of_nonneg_right h_step1 h_1_sub_b3_nn
      linarith [h_reorder ▸ h_s_mul, h_step1_mul]
    show (formationThreshold r).val ≤
         substrate.val * (1 + endowment.val) + (formationThreshold r).val * b3.val
    have h_algebra : (formationThreshold r).val * (1 - b3.val)
                     + (formationThreshold r).val * b3.val = (formationThreshold r).val := by ring
    linarith

/-- **§ 3.3 mixed pair: additive × multiplicative-floored.** For the
    (`combineAdditive`, `multiplicativeFlooredB3Substrate irrMin ...`) pair.
    Same additive shape as other additive-combine discharges: `s + e + b3`.
    Proof identical to additive × multiplicative for § 3.2, extracting
    `d × (1-b3) ≤ substrate` from the max via `le_max_right` (the `irrMin`
    floor is subsumed since substrate is at least both operands of the max). -/
noncomputable def additiveMultiplicativeFlooredB3Augmented
    (irrMin : Region → ℝ)
    (irrMin_pos : ∀ r, 0 < irrMin r)
    (irrMin_below : ∀ r, irrMin r ≤ (dissolutionThreshold r).val) :
    B3AugmentedCombine combineAdditive
      (multiplicativeFlooredB3Substrate irrMin irrMin_pos irrMin_below) where
  extendedCombine _ s e b3 := s.val + e.val + b3.val
  boundary_at_zero _ s e := by
    show s.val + e.val + (0 : ℝ) = s.val + e.val
    ring
  closes_extended_gap_b3 r substrate endowment b3 h_basin h_feedback := by
    have h_eff : (multiplicativeFlooredB3Substrate irrMin irrMin_pos irrMin_below).effectiveDissolution
                    r b3
                 = max (irrMin r) ((dissolutionThreshold r).val * (1 - b3.val)) := rfl
    have h_eng : combineAdditive.engagementThreshold r =
                 (formationThreshold r).val - (dissolutionThreshold r).val := rfl
    rw [h_eff] at h_basin
    rw [h_eng] at h_feedback
    have h_d_le_1 : (dissolutionThreshold r).val ≤ 1 := (dissolutionThreshold r).le1
    have h_b3_nn : (0 : ℝ) ≤ b3.val := b3.pos
    have h_db3_le_substrate : (dissolutionThreshold r).val * (1 - b3.val) ≤ substrate.val :=
      le_trans (le_max_right _ _) h_basin
    show (formationThreshold r).val ≤ substrate.val + endowment.val + b3.val
    nlinarith

/-- **§ 3.3 mixed pair: multiplicative × linear-floored.** For the
    (`combineMultiplicative`, `linearFlooredB3Substrate irrMin ...`) pair.
    Divisive extended combine `s × (1+e) + formation × b3 / dissolution` —
    identical to § 3.2 mult × linear. Case analysis: Case A (b3 ≤ d) uses
    product bound; Case B (b3 > d) uses that in the linear floor, `max
    (irrMin r) (d - b3) = irrMin r > 0 > d - b3` but the argument through
    `substrate + b3 ≥ d` still holds via the max ≥ (d - b3) inequality.
    Uses `le_max_right`, so the `irrMin` floor is only implicit. -/
noncomputable def multiplicativeLinearFlooredB3Augmented
    (irrMin : Region → ℝ)
    (irrMin_pos : ∀ r, 0 < irrMin r)
    (irrMin_below : ∀ r, irrMin r ≤ (dissolutionThreshold r).val) :
    B3AugmentedCombine combineMultiplicative
      (linearFlooredB3Substrate irrMin irrMin_pos irrMin_below) where
  extendedCombine r s e b3 :=
    s.val * (1 + e.val) + (formationThreshold r).val * b3.val / (dissolutionThreshold r).val
  boundary_at_zero r s e := by
    show s.val * (1 + e.val) + (formationThreshold r).val * (0 : ℝ) / (dissolutionThreshold r).val
         = s.val * (1 + e.val)
    ring
  closes_extended_gap_b3 r substrate endowment b3 h_basin h_feedback := by
    have h_d_pos : 0 < (dissolutionThreshold r).val := dissolutionThreshold_pos r
    have h_d_nn : 0 ≤ (dissolutionThreshold r).val := le_of_lt h_d_pos
    have h_e_nn : 0 ≤ endowment.val := endowment.pos
    have h_1e_nn : (0 : ℝ) ≤ 1 + endowment.val := by linarith
    have h_b3_nn : 0 ≤ b3.val := b3.pos
    have h_s_nn : 0 ≤ substrate.val := substrate.pos
    have h_gap : (dissolutionThreshold r).val < (formationThreshold r).val := hysteresis_gap r
    have h_f_nn : 0 ≤ (formationThreshold r).val := le_of_lt (lt_trans h_d_pos h_gap)
    have h_eff : (linearFlooredB3Substrate irrMin irrMin_pos irrMin_below).effectiveDissolution
                    r b3
                 = max (irrMin r) ((dissolutionThreshold r).val - b3.val) := rfl
    have h_eng : combineMultiplicative.engagementThreshold r =
                 ((formationThreshold r).val - (dissolutionThreshold r).val)
                   / (dissolutionThreshold r).val := rfl
    rw [h_eff] at h_basin
    rw [h_eng] at h_feedback
    have h_1e_ge_fd : (formationThreshold r).val / (dissolutionThreshold r).val
                      ≤ 1 + endowment.val := by
      rw [div_le_iff₀ h_d_pos]
      have h_mul := mul_le_mul_of_nonneg_right h_feedback h_d_nn
      rw [div_mul_cancel₀ _ (ne_of_gt h_d_pos)] at h_mul
      linarith
    have h_fd_nn : 0 ≤ (formationThreshold r).val / (dissolutionThreshold r).val :=
      div_nonneg h_f_nn h_d_nn
    show (formationThreshold r).val ≤
         substrate.val * (1 + endowment.val)
           + (formationThreshold r).val * b3.val / (dissolutionThreshold r).val
    by_cases h_case : (dissolutionThreshold r).val ≤ b3.val
    · -- Case B: b3 ≥ d → f * b3 / d ≥ f
      have h_ratio : 1 ≤ b3.val / (dissolutionThreshold r).val := by
        rw [le_div_iff₀ h_d_pos]; linarith
      have h_ge : (formationThreshold r).val
                  ≤ (formationThreshold r).val * b3.val / (dissolutionThreshold r).val := by
        have h_rw : (formationThreshold r).val * b3.val / (dissolutionThreshold r).val
                    = (formationThreshold r).val * (b3.val / (dissolutionThreshold r).val) := by ring
        rw [h_rw]; nlinarith
      have h_ext_nn : 0 ≤ substrate.val * (1 + endowment.val) := mul_nonneg h_s_nn h_1e_nn
      linarith
    · -- Case A: b3 < d → max = ? (either irrMin or d - b3, whichever is larger)
      push_neg at h_case
      have h_dr_nn : (0 : ℝ) ≤ (dissolutionThreshold r).val - b3.val := by linarith
      -- substrate ≥ max(irrMin, d - b3) ≥ d - b3
      have h_s_ge : (dissolutionThreshold r).val - b3.val ≤ substrate.val :=
        le_trans (le_max_right _ _) h_basin
      have h_prod : ((dissolutionThreshold r).val - b3.val)
                    * ((formationThreshold r).val / (dissolutionThreshold r).val)
                    ≤ substrate.val * (1 + endowment.val) :=
        mul_le_mul h_s_ge h_1e_ge_fd h_fd_nn h_s_nn
      have h_simp : ((dissolutionThreshold r).val - b3.val)
                    * ((formationThreshold r).val / (dissolutionThreshold r).val)
                    = (formationThreshold r).val
                      - (formationThreshold r).val * b3.val / (dissolutionThreshold r).val := by
        field_simp
      linarith [h_prod, h_simp]

-- ════════════════════════════════════════════════════════════════
-- §HM22. HOOK 3 NEGATIVE THEOREM — homogeneous populations cannot
-- support persistent HOA maintenance (`hoaFragilityHomogeneous`)
--
-- The SCORE analog of Dijkstra 1974's crucial finding that identical
-- machines cannot self-stabilize. Agent heterogeneity along the
-- CouplingWeightVector axis is the SCORE symmetry-breaker that makes
-- the autocatalytic loop's differentiated cycle-member reinforcement
-- possible; a fully coupling-homogeneous population cannot engage
-- feedback, so no maintenance theorem's premise is satisfiable.
--
-- Scope thin: only CouplingWeightVector homogeneity is formalized.
-- LifeCyclePhase and ManifoldShape variants are separate future work.
-- Load-bearing content is axiomatized (`homogeneous_no_feedback`) —
-- direct derivation from population-level manifold-overlap dynamics
-- is analogous scope to (B''), not attempted here.
-- ════════════════════════════════════════════════════════════════

/-- **Agent-to-CouplingWeightVector association** (Hook 3 prerequisite).
    Each agent has a coupling weight vector characterizing its position
    on the five network dimensions (`Core.lean` §5). Axiomatic here —
    a peer implementation would supply this from its own agent
    representation. -/
axiom agentCouplingWeightVector : Agent → CouplingWeightVector

/-- **Population coupling-homogeneous**: all agents in the state have
    the same coupling weight vector. The SCORE analog of Dijkstra 1974's
    "identical machines" precondition. -/
def PopulationCouplingHomogeneous {r : Region} (s : HOAState r) : Prop :=
  ∀ a₁ ∈ s.agents, ∀ a₂ ∈ s.agents,
    agentCouplingWeightVector a₁ = agentCouplingWeightVector a₂

/-- **Hook 3 core axiom** (the load-bearing theoretical claim from
    Dijkstra 1974's identical-machines-cannot-stabilize finding,
    translated to SCORE): coupling-homogeneous populations cannot have
    engaged autocatalytic feedback. The intuition: identical coupling
    weight vectors mean all agents have identical manifold-overlap
    profiles, so cycle members cannot reinforce differentiated edges —
    the autocatalytic loop cannot engage. Discharging this axiom to a
    theorem requires formalizing population-level manifold-overlap
    dynamics (analogous scope to (B'')); at this tier the axiom encodes
    the theoretical claim, and peer implementations that show HOAs
    persisting in coupling-homogeneous populations would falsify it. -/
axiom homogeneous_no_feedback
    {r : Region} (c : AutocatalyticCombine) (s s' : HOAState r) :
  PopulationCouplingHomogeneous s → ¬ feedbackEngaged c s s'

/-- **Hook 3 preservation axiom** (needed to lift the fragility through
    move-sequences). HOA moves at the fast-timescale (interaction,
    substrate/loop-endowment updates) preserve the agent population's
    coupling structure — agents don't change their coupling weight
    vectors on this timescale. Long-timescale life-cycle transitions or
    member turnover would break this; those are separate future work. -/
axiom hoaMove_preserves_homogeneity {r : Region} (s s' : HOAState r) :
  HOAMove s s' → PopulationCouplingHomogeneous s → PopulationCouplingHomogeneous s'

/-- **The Hook 3 negative theorem** (`hoaFragilityHomogeneous`). For a
    coupling-homogeneous initial population, feedback never engages
    anywhere in the move-sequence — so the premise of every maintenance
    theorem (`hoaMaintainedWithin`, `hoaMaintainedExtended`,
    `hoaMaintainedFormalExtended`, `hoaMaintainedCompositelyExtended`)
    is unsatisfiable and no maintenance guarantee applies. Proof:
    trivial induction using `hoaMove_preserves_homogeneity` (homogeneity
    lifts through the trace) and `homogeneous_no_feedback` (homogeneity
    forbids feedback at each step). -/
theorem hoaFragilityHomogeneous {r : Region} (c : AutocatalyticCombine) :
    ∀ (s : HOAState r), PopulationCouplingHomogeneous s →
      ∀ trace : ℕ → HOAState r,
        trace 0 = s →
        (∀ i, HOAMove (trace i) (trace (i+1))) →
        ∀ i, ¬ feedbackEngaged c (trace i) (trace (i+1)) := by
  intro s h_hom trace tr_0 tr_moves i
  have h_hom_i : PopulationCouplingHomogeneous (trace i) := by
    induction i with
    | zero => rw [tr_0]; exact h_hom
    | succ n ih => exact hoaMove_preserves_homogeneity _ _ (tr_moves n) ih
  exact homogeneous_no_feedback c (trace i) (trace (i+1)) h_hom_i

-- ════════════════════════════════════════════════════════════════
-- §HM23. HOOK 3 SIBLING — LifeCyclePhase homogeneity fragility
-- Parallel to §HM22 with the LifeCyclePhase axis instead of
-- CouplingWeightVector. Same shape; same load-bearing-axiom pattern.
--
-- Distinct from §HM22: coupling-weight-vector homogeneity means all
-- agents have identical NETWORK POSITIONS; lifecycle-phase homogeneity
-- means all agents are at the same LIFE-CYCLE STAGE (all Childhood,
-- all Retirement, etc.). Both are heterogeneity-loss modes. The vault
-- flags LifeCyclePhase as one of the three symmetry-breaking axes
-- named in Hook 3.
-- ════════════════════════════════════════════════════════════════

/-- **Agent-to-LifeCyclePhase association** (Hook 3 sibling prerequisite).
    Free-standing axiom parallel to `agentCouplingWeightVector`.
    Distinct from the `agentPhase` field of `SCOREImplementation`
    (Core.lean § 11) — that requires a concrete implementation record;
    this is a Lean-level global for the abstract mechanism analysis. -/
axiom agentLifeCyclePhase : Agent → LifeCyclePhase

/-- **Population LifeCyclePhase-homogeneous**: all agents at the same
    life-cycle stage. -/
def PopulationLifeCyclePhaseHomogeneous {r : Region} (s : HOAState r) : Prop :=
  ∀ a₁ ∈ s.agents, ∀ a₂ ∈ s.agents,
    agentLifeCyclePhase a₁ = agentLifeCyclePhase a₂

/-- **Hook 3 sibling core axiom** for LifeCyclePhase. A population all at
    the same life-cycle stage cannot engage the autocatalytic loop.
    Intuition: healthy HOA maintenance requires agents at different
    life-cycle phases (children being socialized by householders,
    householders being renewed by retirees passing knowledge); a
    one-phase population loses the cross-phase reinforcement that
    generates edge-weight differentiation. Discharging to a theorem
    requires formalizing cross-phase interaction dynamics. -/
axiom lifeCyclePhaseHomogeneous_no_feedback
    {r : Region} (c : AutocatalyticCombine) (s s' : HOAState r) :
  PopulationLifeCyclePhaseHomogeneous s → ¬ feedbackEngaged c s s'

/-- Fast-timescale HOA moves preserve population LifeCyclePhase
    structure. Long-timescale phase transitions (Childhood → Student
    etc.) are NOT fast-timescale moves and are separate future work. -/
axiom hoaMove_preserves_lifeCyclePhaseHomogeneity {r : Region} (s s' : HOAState r) :
  HOAMove s s' → PopulationLifeCyclePhaseHomogeneous s →
    PopulationLifeCyclePhaseHomogeneous s'

/-- **The Hook 3 sibling theorem for LifeCyclePhase.** Same shape as
    `hoaFragilityHomogeneous`: LifeCyclePhase-homogeneous populations
    cannot engage feedback anywhere in the trace, so no maintenance
    theorem's premise is satisfiable. -/
theorem hoaFragilityLifeCyclePhaseHomogeneous {r : Region} (c : AutocatalyticCombine) :
    ∀ (s : HOAState r), PopulationLifeCyclePhaseHomogeneous s →
      ∀ trace : ℕ → HOAState r,
        trace 0 = s →
        (∀ i, HOAMove (trace i) (trace (i+1))) →
        ∀ i, ¬ feedbackEngaged c (trace i) (trace (i+1)) := by
  intro s h_hom trace tr_0 tr_moves i
  have h_hom_i : PopulationLifeCyclePhaseHomogeneous (trace i) := by
    induction i with
    | zero => rw [tr_0]; exact h_hom
    | succ n ih =>
        exact hoaMove_preserves_lifeCyclePhaseHomogeneity _ _ (tr_moves n) ih
  exact lifeCyclePhaseHomogeneous_no_feedback c (trace i) (trace (i+1)) h_hom_i

-- ════════════════════════════════════════════════════════════════
-- §HM24. HOOK 3 SIBLING — ManifoldShape homogeneity fragility
-- Parallel to §HM22 and §HM23 with the ManifoldShape axis. Introduces
-- `ManifoldShape : Type` as a fresh opaque type (analogous to Region
-- and Agent in Core.lean) — the vault flags it as a heterogeneity
-- axis but Core.lean does not currently have a formal ManifoldShape
-- type.
-- ════════════════════════════════════════════════════════════════

/-- The shape/typology of an agent's B₂ manifold (see vault:
    `obsidian/SCORE/agents/ManifoldShapes.md`). Abstract opaque type;
    concrete peers may parameterize by a specific typology (e.g.
    Lefebvre-style dyadic vs triadic reflexive structures). -/
axiom ManifoldShape : Type

/-- **Agent-to-ManifoldShape association** (Hook 3 sibling prerequisite). -/
axiom agentManifoldShape : Agent → ManifoldShape

/-- **Population ManifoldShape-homogeneous**: all agents have the same
    B₂ manifold shape. -/
def PopulationManifoldShapeHomogeneous {r : Region} (s : HOAState r) : Prop :=
  ∀ a₁ ∈ s.agents, ∀ a₂ ∈ s.agents,
    agentManifoldShape a₁ = agentManifoldShape a₂

/-- **Hook 3 sibling core axiom** for ManifoldShape. A monoshape
    population cannot engage the autocatalytic loop. Intuition: healthy
    HOA maintenance requires diverse manifold-shape perspectives so
    that interactions actually reinforce differentiated overlap
    regions; monoshape populations reinforce only the shape's own
    eigenmodes, not novel cross-shape edges. Discharging to a theorem
    requires formalizing shape-differentiated interaction dynamics. -/
axiom manifoldShapeHomogeneous_no_feedback
    {r : Region} (c : AutocatalyticCombine) (s s' : HOAState r) :
  PopulationManifoldShapeHomogeneous s → ¬ feedbackEngaged c s s'

/-- Fast-timescale HOA moves preserve population ManifoldShape
    structure. Manifold-shape restructuring (Path-A events) is NOT a
    fast-timescale move; the shape-persistence assumption here mirrors
    §HM22/HM23. -/
axiom hoaMove_preserves_manifoldShapeHomogeneity {r : Region} (s s' : HOAState r) :
  HOAMove s s' → PopulationManifoldShapeHomogeneous s →
    PopulationManifoldShapeHomogeneous s'

/-- **The Hook 3 sibling theorem for ManifoldShape.** Same shape as
    the other two Hook 3 theorems: monoshape populations cannot engage
    feedback anywhere in the trace. -/
theorem hoaFragilityManifoldShapeHomogeneous {r : Region} (c : AutocatalyticCombine) :
    ∀ (s : HOAState r), PopulationManifoldShapeHomogeneous s →
      ∀ trace : ℕ → HOAState r,
        trace 0 = s →
        (∀ i, HOAMove (trace i) (trace (i+1))) →
        ∀ i, ¬ feedbackEngaged c (trace i) (trace (i+1)) := by
  intro s h_hom trace tr_0 tr_moves i
  have h_hom_i : PopulationManifoldShapeHomogeneous (trace i) := by
    induction i with
    | zero => rw [tr_0]; exact h_hom
    | succ n ih =>
        exact hoaMove_preserves_manifoldShapeHomogeneity _ _ (tr_moves n) ih
  exact manifoldShapeHomogeneous_no_feedback c (trace i) (trace (i+1)) h_hom_i

-- ════════════════════════════════════════════════════════════════
-- §HM25. LONG-TIMESCALE DYNAMICS (L1) — MemberTurnoverMove
-- (Hysteresis § 3.2 flag: ceiling residue does NOT survive member
-- turnover; § 3.3 flag: formal B₃ substrate DOES.)
--
-- Design (C) — disjoint slow-move type. `MemberTurnoverMove` is a
-- separate transition type from `HOAMove`; the fast-timescale
-- maintenance/fragility axioms don't apply. Slow-timescale reasoning
-- gets its own analysis: erosion of ceiling residue, preservation of
-- formal B₃ substrate. Composing fast and slow reasoning is future
-- work (see LongTimescaleDynamics.md).
--
-- Scope thin: only L1 (member turnover) at this tier. L2 generational
-- renewal, L3 Path-A accumulation, L4 co-inscription/crossover, and
-- cross-mechanism composition are separate future PRs.
-- ════════════════════════════════════════════════════════════════

/-- **Member turnover** — a slow-timescale transition where the agent
    population is replaced (in whole or part). Disjoint from `HOAMove`
    (fast-timescale interaction/decay/intervention); the fast-timescale
    preservation axioms (`hoaMove_preserves_*Homogeneity`) do not apply
    to `MemberTurnoverMove`. -/
axiom MemberTurnoverMove {r : Region} : HOAState r → HOAState r → Prop

/-- **Turnover decay factor** — abstract constant characterizing the
    worst-case ceiling-residue attrition per member-turnover event.
    Peer implementations calibrate. -/
axiom turnoverDecayFactor : ℝ

/-- The decay factor is non-negative. -/
axiom turnoverDecayFactor_pos : 0 ≤ turnoverDecayFactor

/-- The decay factor is strictly less than 1 — every turnover strictly
    erodes ceiling residue (in the worst case). This is what makes the
    geometric-decay theorem below reach zero in the limit. -/
axiom turnoverDecayFactor_lt_one : turnoverDecayFactor < 1

/-- **Erosion axiom** (Hysteresis.md § 3.2). Each member-turnover event
    multiplies ceiling residue by at most `turnoverDecayFactor`. Formalizes
    "does NOT survive member turnover — new members arrive with
    un-restructured manifolds and lower the collective ceiling unless
    successfully inscribed." The inscription condition (L2 generational
    renewal) is not yet formalized; at this tier, all turnover events
    are treated as un-inscribed / worst-case. -/
axiom memberTurnoverMove_erodes_ceiling
    {r : Region} (s s' : HOAState r) :
  MemberTurnoverMove s s' →
    s'.ceilingResidue.val ≤ turnoverDecayFactor * s.ceilingResidue.val

/-- **Preservation axiom** (Hysteresis.md § 3.3). Formal B₃ substrate
    survives member turnover — the distinguishing claim of § 3.3 vs
    § 3.2. Formal roles outlive individual role-holders. -/
axiom memberTurnoverMove_preserves_formalB3
    {r : Region} (s s' : HOAState r) :
  MemberTurnoverMove s s' → s'.formalB3Substrate = s.formalB3Substrate

/-- **Ceiling-residue erodes under turnover.** After `i` turnovers,
    ceiling residue is at most `turnoverDecayFactor^i` times its
    initial value. Since `turnoverDecayFactor < 1`, this decays
    geometrically to zero in the limit — formalizing "ceiling residue
    does not survive turnover" as a rate-of-decay claim. -/
theorem ceilingResidue_erodes_under_turnover
    {r : Region} (trace : ℕ → HOAState r)
    (h_turnover : ∀ i, MemberTurnoverMove (trace i) (trace (i+1))) :
    ∀ i, (trace i).ceilingResidue.val ≤
         turnoverDecayFactor^i * (trace 0).ceilingResidue.val := by
  intro i
  induction i with
  | zero => simp
  | succ n ih =>
      have h_step := memberTurnoverMove_erodes_ceiling
                       (trace n) (trace (n+1)) (h_turnover n)
      have h_decay_nn : 0 ≤ turnoverDecayFactor := turnoverDecayFactor_pos
      calc (trace (n+1)).ceilingResidue.val
          ≤ turnoverDecayFactor * (trace n).ceilingResidue.val := h_step
        _ ≤ turnoverDecayFactor
              * (turnoverDecayFactor^n * (trace 0).ceilingResidue.val) :=
              mul_le_mul_of_nonneg_left ih h_decay_nn
        _ = turnoverDecayFactor^(n+1) * (trace 0).ceilingResidue.val := by ring

/-- **Formal B₃ preserved under turnover.** After any sequence of
    member-turnover events, formal B₃ substrate is unchanged.
    Formalizes the § 3.3 mechanism's distinguishing property. -/
theorem formalB3_preserved_under_turnover
    {r : Region} (trace : ℕ → HOAState r)
    (h_turnover : ∀ i, MemberTurnoverMove (trace i) (trace (i+1))) :
    ∀ i, (trace i).formalB3Substrate = (trace 0).formalB3Substrate := by
  intro i
  induction i with
  | zero => rfl
  | succ n ih =>
      rw [← ih,
          memberTurnoverMove_preserves_formalB3 (trace n) (trace (n+1))
                                                (h_turnover n)]

-- ════════════════════════════════════════════════════════════════
-- §HM26. LONG-TIMESCALE DYNAMICS (L2) — GenerationalRenewalMove
-- (Hysteresis § 3.2: generational transmission fraction renews the
-- ceiling residue each generation; fail to inscribe children → the
-- ceiling residue doesn't get re-laid → HOA dissolves within one
-- generation.)
--
-- L2 is the counter-mechanism to L1 (§HM25). Where L1 axiomatizes pure
-- turnover as strictly erosive (decay by turnoverDecayFactor < 1), L2
-- axiomatizes turnover-with-successful-inscription as preservative
-- (ceiling residue at least maintained). Both are disjoint slow-move
-- types; a peer implementation models each generational transition as
-- either L1 (no inscription) or L2 (successful inscription).
--
-- Scope thin: only the "successful renewal preserves ceiling" claim is
-- formalized. Partial-inscription (some fraction of new agents
-- successfully inscribed) is future work; a peer might model it by
-- interleaving L1 and L2 moves in a ratio matching the transmission
-- fraction.
-- ════════════════════════════════════════════════════════════════

/-- **Generational renewal** — a slow-timescale move in which
    incoming-Childhood agents enter the HOA and inscription of the
    ceiling-residue-relevant manifold structure succeeds. Disjoint from
    `HOAMove` (fast-timescale) and `MemberTurnoverMove` (turnover
    without inscription); the peer implementation decides which slow
    move applies at each generational transition. -/
axiom GenerationalRenewalMove {r : Region} : HOAState r → HOAState r → Prop

/-- **Renewal maintains ceiling** (Hysteresis.md § 3.2, counter to L1
    erosion). Successful generational inscription transfers the
    ceiling-residue-relevant manifold structure to new agents; ceiling
    residue does not decrease. Peer implementations may strengthen this
    to strict INCREASE (folding in new agents' contributions); the
    baseline claim is preservation. -/
axiom generationalRenewalMove_maintains_ceiling
    {r : Region} (s s' : HOAState r) :
  GenerationalRenewalMove s s' →
    s.ceilingResidue.val ≤ s'.ceilingResidue.val

/-- Formal B₃ substrate survives generational renewal — same claim
    shape as for L1 turnover. -/
axiom generationalRenewalMove_preserves_formalB3
    {r : Region} (s s' : HOAState r) :
  GenerationalRenewalMove s s' → s'.formalB3Substrate = s.formalB3Substrate

/-- **Ceiling residue is preserved under repeated generational renewal.**
    Direct contrast with L1: after `i` turnovers ceiling ≤ `decay^i × initial`
    (geometric decay); after `i` renewals ceiling ≥ initial (preservation
    or growth). This is the L2 counter-claim to L1's erosion, formalizing
    the § 3.2 renewal mechanism. -/
theorem ceilingResidue_preserved_under_renewal
    {r : Region} (trace : ℕ → HOAState r)
    (h_renewal : ∀ i, GenerationalRenewalMove (trace i) (trace (i+1))) :
    ∀ i, (trace 0).ceilingResidue.val ≤ (trace i).ceilingResidue.val := by
  intro i
  induction i with
  | zero => exact le_refl _
  | succ n ih =>
      have h_step := generationalRenewalMove_maintains_ceiling
                       (trace n) (trace (n+1)) (h_renewal n)
      linarith

/-- **Formal B₃ preserved under repeated generational renewal.** Same
    structure as `formalB3_preserved_under_turnover` — both slow moves
    preserve the formal layer that § 3.3 stakes its distinguishing
    persistence claim on. -/
theorem formalB3_preserved_under_renewal
    {r : Region} (trace : ℕ → HOAState r)
    (h_renewal : ∀ i, GenerationalRenewalMove (trace i) (trace (i+1))) :
    ∀ i, (trace i).formalB3Substrate = (trace 0).formalB3Substrate := by
  intro i
  induction i with
  | zero => rfl
  | succ n ih =>
      rw [← ih,
          generationalRenewalMove_preserves_formalB3 (trace n) (trace (n+1))
                                                     (h_renewal n)]

-- ════════════════════════════════════════════════════════════════
-- §HM27. LONG-TIMESCALE DYNAMICS (L3) — PathAMove residue accretion
-- (CeilingResidue.md § "What is NOT formalized": how ceiling residue
-- actually rises — the Path-A structural restructuring mechanism the
-- § 3.2 discharge axiomatized.)
--
-- L3 is the ACCRETION side of the ceiling-residue dynamics, comple-
-- menting L1 (erosion) and L2 (preservation-under-renewal). Where L2's
-- non-decrease comes from inheriting existing ceiling through
-- inscription, L3's non-decrease comes from Path-A contradiction events
-- INSIDE the running autocatalytic loop actively deepening manifold
-- overlap. Both share the same baseline non-decrease axiom shape; the
-- physical differentiation is in the mechanism story (see
-- LongTimescaleDynamics.md § "(L3) Path-A residue accumulation"). L3
-- adds a peer-supplied strict-accrual rate axiom below saturation.
--
-- Scope thin: baseline non-decrease axiom + strict-accrual rate (below
-- saturation) as a separate additional axiom. Derived theorem is just
-- the monotone claim; the linear-growth-below-saturation theorem is
-- future work (requires trace-wide saturation checking).
-- ════════════════════════════════════════════════════════════════

/-- **Path-A accretion move** — a slow-timescale event where a Path-A
    contradiction inside the running autocatalytic loop deepens cycle
    members' manifold overlap, raising the edge-weight ceiling. Disjoint
    from `HOAMove` (fast-timescale), `MemberTurnoverMove` (L1 erosion),
    and `GenerationalRenewalMove` (L2 preservation). The vault's
    mechanism story requires the loop to be engaged for Path-A events
    to happen; that requirement is captured in prose (see
    LongTimescaleDynamics.md), not enforced by an explicit precondition. -/
axiom PathAMove {r : Region} : HOAState r → HOAState r → Prop

/-- **Peer-supplied strict-accrual increment** — the minimum ceiling-
    residue increment per Path-A event, below saturation. Peer
    implementations calibrate; the associated axiom is separate from
    the baseline monotonicity axiom, so peers that want to work with
    just monotonicity can ignore this. -/
axiom pathAAccrualIncrement : ℝ

/-- The accrual increment is strictly positive — Path-A events are
    structurally productive; a zero increment would collapse L3 to L2's
    baseline preservation. -/
axiom pathAAccrualIncrement_pos : 0 < pathAAccrualIncrement

/-- **Path-A accretes ceiling** (baseline monotonicity). Each Path-A
    event does not decrease ceiling residue. Baseline claim; the
    strict-accrual axiom below strengthens it below saturation. -/
axiom pathAMove_accretes_ceiling
    {r : Region} (s s' : HOAState r) :
  PathAMove s s' →
    s.ceilingResidue.val ≤ s'.ceilingResidue.val

/-- **Path-A strict-accrual below saturation.** When the accumulated
    ceiling plus the accrual increment is still ≤ 1 (not yet saturated
    at the CouplingWeight upper bound), each Path-A event increases
    ceiling by at least the accrual increment. Saturation is an
    implicit upper bound from the `CouplingWeight` type discipline
    (val ≤ 1); once ceiling reaches 1, Path-A cannot accrete further
    within this model. A peer that models beyond-1 ceilings would
    refactor `HOAState.ceilingResidue` to a wider type. -/
axiom pathAMove_strict_accrual_below_saturation
    {r : Region} (s s' : HOAState r) :
  PathAMove s s' →
    s.ceilingResidue.val + pathAAccrualIncrement ≤ 1 →
    s.ceilingResidue.val + pathAAccrualIncrement ≤ s'.ceilingResidue.val

/-- Formal B₃ substrate survives Path-A restructuring. Same claim
    shape as L1/L2. Path-A operates on the manifold layer, not the
    formal layer. -/
axiom pathAMove_preserves_formalB3
    {r : Region} (s s' : HOAState r) :
  PathAMove s s' → s'.formalB3Substrate = s.formalB3Substrate

/-- **Ceiling residue accretes under repeated Path-A events.** After
    `i` Path-A events, `(trace 0).ceiling ≤ (trace i).ceiling`. Parallel
    to `ceilingResidue_preserved_under_renewal` in axiom shape — both
    say "ceiling doesn't decrease over the trace" — but the mechanism
    is different: L2 renews from inheritance, L3 accretes from Path-A
    restructuring. A separate `pathAAccrualIncrement`-based linear-
    growth theorem (below saturation) is future work. -/
theorem ceilingResidue_accretes_under_pathA
    {r : Region} (trace : ℕ → HOAState r)
    (h_pathA : ∀ i, PathAMove (trace i) (trace (i+1))) :
    ∀ i, (trace 0).ceilingResidue.val ≤ (trace i).ceilingResidue.val := by
  intro i
  induction i with
  | zero => exact le_refl _
  | succ n ih =>
      have h_step := pathAMove_accretes_ceiling
                       (trace n) (trace (n+1)) (h_pathA n)
      linarith

/-- **Formal B₃ preserved under repeated Path-A events.** Path-A
    operates on the manifold layer, not the formal layer; formal B₃
    substrate stays constant across all Path-A events. -/
theorem formalB3_preserved_under_pathA
    {r : Region} (trace : ℕ → HOAState r)
    (h_pathA : ∀ i, PathAMove (trace i) (trace (i+1))) :
    ∀ i, (trace i).formalB3Substrate = (trace 0).formalB3Substrate := by
  intro i
  induction i with
  | zero => rfl
  | succ n ih =>
      rw [← ih,
          pathAMove_preserves_formalB3 (trace n) (trace (n+1))
                                       (h_pathA n)]

end SCORE
