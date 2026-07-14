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

end SCORE
