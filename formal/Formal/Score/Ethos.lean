import Formal.Score.Core
import Formal.Score.HOAMaintenance

set_option linter.unusedVariables false
set_option linter.style.whitespace false

/-!
# SCORE.Ethos

ETHOS peer: the capture-monotonicity lemma (SS13) and the citation-network
binding of the SS14 region machinery (SS15).
-/

namespace SCORE

-- ── ETHOS: capture can only decrease information health ──
-- (ETHOS-InformationHealth.md Phase B; OWL ethos:AmplificationFilteredIncorporation ⊑
-- core:Incorporation, ethos:CaptureDiscriminant ⊑ core:AdjacentPossibleMeasure.)

/-- Information health under a capture attenuation factor κ. Telos-aligned NS has
    κ = 1 (no discount); captured (LossFunction) amplification has κ < 1. -/
def capturedHealth (κ H : ℝ) : ℝ := κ * H

/-- **ETHOS monotonicity.** A capture factor κ ≤ 1 cannot increase information health:
    decoupling amplification from content quality can only discount it. -/
theorem capture_cannot_increase_information_health
    {κ H : ℝ} (hκ : κ ≤ 1) (hH : 0 ≤ H) :
    capturedHealth κ H ≤ H := by
  unfold capturedHealth
  calc κ * H ≤ 1 * H := mul_le_mul_of_nonneg_right hκ hH
    _ = H := one_mul H


-- ════════════════════════════════════════════════════════════════
-- §15. ETHOS — CITATION NETWORK BOUND TO §14 (first specializing peer)
-- ETHOS is the first peer to instantiate the §14 region machinery (first-binding
-- decision 2026-06-21; obsidian/SCORE/domains/B3RegionGeometry.md § "First binding"):
-- an epistemic community's corpus R(C) is a graded down-set of the citation /
-- derivation DAG ETHOS already builds for its quality measure Q
-- (obsidian/SCORE/emergence/applications/ETHOS-InformationHealth.md). This is a
-- *toy witness* — a 4-claim DAG across strata — proving the structure is inhabited
-- and the §14 theorems fire on a concrete ETHOS instance. Together with NEXUS (§16)
-- this is the ETHOS ∩ NEXUS overlap that promoted §14 to core. Real citation/
-- retraction networks are Q4 BIND (data, Phase F), not Lean.
-- ════════════════════════════════════════════════════════════════

/-- A toy ETHOS epistemic inscription. Each stands for a B₃ inscription (`ethosAsB3`);
    kept as its own type so the citation edges and grades are pattern-matchable. -/
inductive EClaim
  | datum      -- a raw finding / dataset
  | method     -- an established method
  | theory     -- a theory built on data + method
  | paradigm   -- a generative framework built on theory
deriving DecidableEq, Repr

/-- Every ETHOS claim is realized as a B₃ inscription (documents the domain tie —
    `EClaim` is a refinement of `InscriptionContent`; not used in the proofs). -/
axiom ethosAsB3 : EClaim → InscriptionContent

/-- Citation / derivation as a `Bool` relation (decidable, so the witnesses below
    compute): `ethosCites x y = true` ⇔ y cites / builds on x (x is y's substrate). -/
def ethosCites : EClaim → EClaim → Bool
  | .datum,  .theory   => true
  | .method, .theory   => true
  | .theory, .paradigm => true
  | _,       _         => false

/-- The epistemic grading: where each claim sits in the B₃ idea-hierarchy —
    datum/method are written-inscription/institution substrate, theory a meta-idea,
    paradigm a generative framework. -/
def ethosGrade : EClaim → B3Level
  | .datum    => ⟨2, by omega⟩   -- written inscription
  | .method   => ⟨3, by omega⟩   -- institution
  | .theory   => ⟨4, by omega⟩   -- meta-idea
  | .paradigm => ⟨5, by omega⟩   -- generative framework

/-- The grading is monotone along every citation edge — the §14 `grade_mono` law,
    checked exhaustively on the finite ETHOS DAG. -/
theorem ethosCites_graded : ∀ {x y : EClaim},
    ethosCites x y = true → ethosGrade x ≤ ethosGrade y := by
  intro x y h
  cases x <;> cases y <;> first | exact absurd h (by decide) | decide

/-- ETHOS's citation network as a §14 `DoctrinalNetwork`. -/
def ethosNetwork : DoctrinalNetwork EClaim where
  composesFrom x y := ethosCites x y = true
  grade := ethosGrade
  grade_mono := ethosCites_graded

/-- An epistemic community's corpus = the down-closure of its research frontier.
    A region for free (§14 `downClosure_isRegion`): substrate-closed, so holding a
    frontier result entails holding everything it cites. -/
def ethosCorpus (frontier : Set EClaim) : Set EClaim :=
  ethosNetwork.downClosure frontier

theorem ethosCorpus_isRegion (frontier : Set EClaim) :
    ethosNetwork.IsRegion (ethosCorpus frontier) :=
  ethosNetwork.downClosure_isRegion frontier

/-- **Store the frontier, derive the corpus (worked witness).** A paradigm-led
    discipline (frontier `{paradigm}`) holds its full cited substrate down to the raw
    datum — the corpus is recovered from the single stored frontier node by
    reachability (datum → theory → paradigm). -/
example : EClaim.datum ∈ ethosCorpus {EClaim.paradigm} := by
  refine ⟨EClaim.paradigm, rfl, ?_⟩
  have hdt : ethosNetwork.composesFrom EClaim.datum EClaim.theory := rfl
  have htp : ethosNetwork.composesFrom EClaim.theory EClaim.paradigm := rfl
  exact (Relation.ReflTransGen.single hdt).tail htp

/-- **Shared canon is a corpus (ETHOS instance of `region_inter`).** Two disciplines'
    shared literature is itself a substrate-closed corpus — the common ground whose
    size is the anchor's `overlap`, and whose lowest absent stratum is the divergence
    floor (Kuhnian incommensurability when that floor is deep). -/
theorem ethos_shared_canon_isRegion {R S : Set EClaim}
    (hR : ethosNetwork.IsRegion R) (hS : ethosNetwork.IsRegion S) :
    ethosNetwork.IsRegion (R ∩ S) :=
  ethosNetwork.region_inter hR hS


/-- **ETHOS Infosphere spectral EWS** as the n = 3 instance of the generic `spectralEWS`:
    `w` the three nonnegative signature weights, `s` the three normalized critical-slowing-down
    signatures over the produced-quality trajectory Phi_quality(t). The second filler of
    core:SpectralEarlyWarningIndicator (alongside `polarisSEWI`), method-commensurable with it;
    the concrete signatures/weights are Q4 BIND (src/ethos, M4-4). ET-G-13; E6 §3A. -/
def ethosSpectralEWS (w s : Fin 3 → ℝ) : ℝ := spectralEWS w s

/-- **ETHOS spectral-EWS monotonicity** — the n = 3 instance of `spectral_ews_monotone`:
    nondecreasing in each of its three signatures with nonnegative weights. Mirrors
    `polarisSEWI_monotone`; the shared law that makes the two fillers commensurable. -/
theorem ethosSpectralEWS_monotone (w : Fin 3 → ℝ) (hw : ∀ i, 0 ≤ w i)
    (s s' : Fin 3 → ℝ) (hss : ∀ i, s i ≤ s' i) :
    ethosSpectralEWS w s ≤ ethosSpectralEWS w s' :=
  spectral_ews_monotone w hw s s' hss


-- ════════════════════════════════════════════════════════════════
-- §RV. ETHOS BRANCH R — OR-REDUNDANT VERIFICATION LAYER (2026-07-07)
-- The H re-model (ETHOS-InformationHealth.md § Decision fork / § Re-model; polaris#383,
-- git tag ethos-h-flat-baseline). Truthfulness assurance T is a PARALLEL system of
-- independent checks V_j, not the flat scalar t of Branch F:
--     T = 1 - Π_j (1 - c_j)      [an error is caught if ANY independent check catches it]
-- This Lean carries the numeric structure function DL cannot express; the OWL
-- (ethos:VerificationLayer, ethos:RedundantVerificationLayer ⊑ assuredBy min 2
-- IndependentVerificationMechanism) carries the qualitative redundancy structure.
-- The theorem below mechanizes "capture = de-redundancy": capture collapses the
-- independent V_j into one effective check, dropping T from 1-Π(1-c_j) down toward a
-- single c_i — and the redundant layer always dominates that single check.
-- ════════════════════════════════════════════════════════════════

/-- Redundant verification assurance: the probability at least one of `k` independent
    checks catches an error, `c j` = check j's catch-probability. `T = 1 - Π_j (1 - c_j)`.
    The Branch-R replacement for the flat scalar truthfulness `t`. -/
def verificationAssurance {k : ℕ} (c : Fin k → ℝ) : ℝ :=
  1 - ∏ j, (1 - c j)

/-- **Redundancy dominates any single check (capture = de-redundancy, mechanized).**
    For catch-probabilities in [0,1], the parallel verification layer is at least as strong
    as any one of its mechanisms. Capture correlates the ostensibly-independent checks and
    collapses the layer toward a single surviving check `c i`; this theorem is the exact
    cost of that collapse — the redundant layer sits `≥ c i`, so driving `κ → 1`
    (`T → c i`) can only lose the redundancy premium, never gain. -/
theorem redundancy_dominates_single {k : ℕ} (c : Fin k → ℝ)
    (h0 : ∀ j, 0 ≤ c j) (h1 : ∀ j, c j ≤ 1) (i : Fin k) :
    c i ≤ verificationAssurance c := by
  unfold verificationAssurance
  have hsplit : ∏ j, (1 - c j)
      = (1 - c i) * ∏ j ∈ Finset.univ.erase i, (1 - c j) :=
    (Finset.mul_prod_erase Finset.univ (fun j => 1 - c j) (Finset.mem_univ i)).symm
  have hle1 : ∏ j ∈ Finset.univ.erase i, (1 - c j) ≤ 1 :=
    Finset.prod_le_one (fun j _ => by linarith [h1 j]) (fun j _ => by linarith [h0 j])
  have hnn : (0 : ℝ) ≤ 1 - c i := by linarith [h1 i]
  have hprod : ∏ j, (1 - c j) ≤ 1 - c i := by
    rw [hsplit]
    calc (1 - c i) * ∏ j ∈ Finset.univ.erase i, (1 - c j)
        ≤ (1 - c i) * 1 := mul_le_mul_of_nonneg_left hle1 hnn
      _ = 1 - c i := mul_one _
  linarith

/-- **Verification assurance is monotone in each check.** Strengthening (or adding) an
    independent check cannot lower the layer — the redundancy that flat `t` erased. -/
theorem verificationAssurance_mono {k : ℕ} (c c' : Fin k → ℝ)
    (h1' : ∀ j, c' j ≤ 1) (hcc : ∀ j, c j ≤ c' j) :
    verificationAssurance c ≤ verificationAssurance c' := by
  unfold verificationAssurance
  have hprod : ∏ j, (1 - c' j) ≤ ∏ j, (1 - c j) :=
    Finset.prod_le_prod (fun j _ => by linarith [h1' j]) (fun j _ => by linarith [hcc j])
  linarith


-- ════════════════════════════════════════════════════════════════
-- §RV-D. BRANCH R DEPENDENCE --- the pairwise capacity layer.
--
-- §RV above formalizes the verification layer at the INDEPENDENT limit only. The
-- Option-1 re-specification (governance/SCORE_ETHOS_RQ1b_Choquet_Respecification.md
-- §§3, 3a) replaces the stipulated κ-interpolation with a fitted 2-additive Choquet
-- capacity, whose operative statistic is the pairwise redundancy-collapse Δ. That
-- statistic had no formal statement anywhere: the pre-lock audit §3.3 found κ appears
-- in §RV solely in a prose docstring, and issue #640 recorded the same gap from the
-- other side (Choquet absent from both Lean and OWL while implemented in Python).
--
-- This section closes it, and does so with **no new axioms**: every claim §3a makes
-- about the reference, the direction of capture, and the truncation is elementary real
-- arithmetic and is proved here. The Python plug-in estimator
-- (`src/ethos/measurement/dependence_parameter.py`) is checked against these statements
-- rather than against a generator written alongside it.
--
-- Scope: the PAIR level, which is what a 2-additive capacity fits and what Δ is
-- defined on. Nothing here formalizes the *estimator* (§6 freezes that at lock), the
-- confidence intervals, or the identifiability-on-interior claim -- that last is a
-- genuine mathematical claim about capacities and is the one place an axiom or a
-- literature discharge would be required. Not attempted here.
-- ════════════════════════════════════════════════════════════════

/-- Independent-OR assurance on a pair: `μ_indep({j,k}) = 1 - (1-c_j)(1-c_k)`, written
    in expanded form. The two-mechanism case of `verificationAssurance`. -/
def pairAssuranceIndep (cj ck : ℝ) : ℝ := cj + ck - cj * ck

/-- The pair's Möbius interaction index, given the pair's assurance `mu`:
    `m({j,k}) = μ({j,k}) - μ({j}) - μ({k})`, with singletons `μ({j}) = c_j`. -/
def pairMobius (cj ck mu : ℝ) : ℝ := mu - cj - ck

/-- The §3a **independence reference** --- the Möbius index the independent-OR capacity
    itself carries. This is the null, and it is not zero. -/
def pairMobiusIndep (cj ck : ℝ) : ℝ := pairMobius cj ck (pairAssuranceIndep cj ck)

/-- **The independence reference is `-c_j c_k`** (re-specification §3a). -/
theorem pairMobiusIndep_eq (cj ck : ℝ) : pairMobiusIndep cj ck = -(cj * ck) := by
  unfold pairMobiusIndep pairMobius pairAssuranceIndep; ring

/-- **Zero interaction is the wrong null for a redundancy layer.** For an OR layer even
    *independent* mechanisms interact in the capacity sense: the reference is strictly
    negative, i.e. already sub-additive. A test against zero would therefore be testing
    against a mis-specified null, which is the error §3a exists to prevent. -/
theorem pairMobiusIndep_neg {cj ck : ℝ} (hj : 0 < cj) (hk : 0 < ck) :
    pairMobiusIndep cj ck < 0 := by
  rw [pairMobiusIndep_eq]
  have : 0 < cj * ck := mul_pos hj hk
  linarith

/-- **The additive capacity is not a valid assurance capacity**, while the
    independent-OR one is: `μ_indep ≤ 1` always, whereas the zero-interaction capacity
    assigns `c_j + c_k`, which exceeds 1 whenever the marginals are large. -/
theorem pairAssuranceIndep_le_one {cj ck : ℝ} (h1j : cj ≤ 1) (h1k : ck ≤ 1)
    (h0j : 0 ≤ cj) (h0k : 0 ≤ ck) : pairAssuranceIndep cj ck ≤ 1 := by
  unfold pairAssuranceIndep; nlinarith

/-- **Redundancy collapse** `Δ_{jk} = m_indep({j,k}) - m_fit({j,k})` --- the departure of
    the fitted pair interaction *below* its independence reference (§3a). -/
def redundancyCollapse (cj ck mu : ℝ) : ℝ := pairMobiusIndep cj ck - pairMobius cj ck mu

/-- **Δ is the observed catch-set overlap above what independent marginals predict.**
    Writing the pair's assurance by inclusion–exclusion, `μ({j,k}) = c_j + c_k - joint`,
    the Möbius form and the overlap form coincide. This identity is what licenses the
    Python estimator to read Δ off catch-set overlaps rather than off a fitted capacity. -/
theorem redundancyCollapse_eq_overlap_excess (cj ck joint : ℝ) :
    redundancyCollapse cj ck (cj + ck - joint) = joint - cj * ck := by
  unfold redundancyCollapse pairMobiusIndep pairMobius pairAssuranceIndep; ring

/-- **Δ is monotone in the joint catch rate.** More co-catching, at fixed marginals, is
    more measured dependence --- the direction the capture reading requires. -/
theorem redundancyCollapse_mono_in_joint {cj ck j1 j2 : ℝ} (h : j1 ≤ j2) :
    redundancyCollapse cj ck (cj + ck - j1) ≤ redundancyCollapse cj ck (cj + ck - j2) := by
  rw [redundancyCollapse_eq_overlap_excess, redundancyCollapse_eq_overlap_excess]
  linarith

/-- **Independent mechanisms give exactly zero collapse.** The falsifier for P-1b'-i:
    a corpus of genuinely independent `V_j` --- the state ETHOS's theory says a *healthy*
    infosphere is in --- returns `Δ = 0`. -/
theorem redundancyCollapse_indep (cj ck : ℝ) :
    redundancyCollapse cj ck (pairAssuranceIndep cj ck) = 0 := by
  unfold redundancyCollapse pairMobiusIndep pairMobius pairAssuranceIndep; ring

/-- **Full capture drives the interaction strictly below independence.** When the two
    mechanisms catch the *same* items (`c_j = c_k = c`, so the OR of identical catch-sets
    is either one alone, `μ({j,k}) = c`), the collapse is `c - c²`, which is strictly
    positive on `(0,1)`. This is §3a's `-c < -c²` argument, mechanized: capture is not
    merely detectable but signed. -/
theorem captured_pair_collapse (c : ℝ) : redundancyCollapse c c c = c - c * c := by
  unfold redundancyCollapse pairMobiusIndep pairMobius pairAssuranceIndep; ring

theorem captured_pair_collapse_pos {c : ℝ} (h0 : 0 < c) (h1 : c < 1) :
    0 < redundancyCollapse c c c := by
  rw [captured_pair_collapse]; nlinarith

/-- Independent-OR assurance on a triple, for the truncation caveat below. -/
def tripleAssuranceIndep (a b c : ℝ) : ℝ := 1 - (1 - a) * (1 - b) * (1 - c)

/-- Third-order Möbius mass of the independent-OR capacity,
    `m({j,k,l}) = μ(jkl) - μ(jk) - μ(jl) - μ(kl) + μ(j) + μ(k) + μ(l)`. -/
def tripleMobiusIndep (a b c : ℝ) : ℝ :=
  tripleAssuranceIndep a b c
    - pairAssuranceIndep a b - pairAssuranceIndep a c - pairAssuranceIndep b c
    + a + b + c

/-- **The mass a 2-additive fit drops is `+abc`, not `-abc`.**
    The re-specification §3a's truncation caveat states the dropped triple term as
    `- c_j c_k c_l`. The sign is wrong: the Möbius transform of the noisy-OR capacity
    alternates as `(-1)^{|S|+1} ∏_{j ∈ S} c_j`, so singletons are `+c`, pairs are
    `-c_j c_k`, and triples are `+c_j c_k c_l`. The magnitude claim the caveat rests on
    --- third order in `c`, hence small --- is unaffected, and the pair-level test is
    unaffected because it is run against the pairwise reference. Recorded because a
    stated sign that is wrong is the kind of thing a reader will propagate. -/
theorem tripleMobiusIndep_eq (a b c : ℝ) : tripleMobiusIndep a b c = a * b * c := by
  unfold tripleMobiusIndep tripleAssuranceIndep pairAssuranceIndep; ring


-- ════════════════════════════════════════════════════════════════
-- §RV-F. FRÉCHET--HOEFFDING BOUNDS on the pair joint, and on Δ.
--
-- The split G-anchor gate (PR-EX-1 §6.3, amended 2026-07-27) rests on these: the
-- ceiling/floor clause was demoted from a drop rule to a *precision* statement, and the
-- precision is exactly the width of the interval Δ can occupy at given marginals. The D1
-- nature-run generator then rejects an `anchor_density` above `min(1, c_a + c_b)` on the
-- same grounds.
--
-- Both were carrying a citation to Fréchet (1935) / Hoeffding (1940) that no one in this
-- project had checked. They do not need one: the bounds follow from monotonicity of a
-- measure and `P(Ω) = 1`, and are proved here from mathlib. **No axiom, and no appeal to
-- an unverified source** --- which is the point, since a load-bearing gate resting on a
-- citation nobody read is the defect this whole layer exists to remove.
--
-- Two encodings. The measure-theoretic statements are the theorem; the real-valued ones
-- mirror `dependence_parameter.frechet_bounds` so the Python has something to be checked
-- against. `frechet_of_probability` is the bridge that stops them from drifting apart.
-- ════════════════════════════════════════════════════════════════

open MeasureTheory in
/-- **Fréchet upper bound.** A joint cannot exceed either marginal. -/
theorem measure_inter_le_min {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (s t : Set Ω) : μ (s ∩ t) ≤ min (μ s) (μ t) :=
  le_min (measure_mono Set.inter_subset_left) (measure_mono Set.inter_subset_right)

open MeasureTheory in
/-- **Fréchet lower bound**, in additive form so no truncated `ENNReal` subtraction appears:
    `P(A) + P(B) ≤ 1 + P(A ∩ B)`, equivalently `P(A ∩ B) ≥ P(A) + P(B) - 1`. -/
theorem measure_add_le_one_add_inter {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {s : Set Ω} (hs : MeasurableSet s) (t : Set Ω) :
    μ s + μ t ≤ 1 + μ (s ∩ t) := by
  have h : μ s + μ t = μ (s ∪ t) + μ (s ∩ t) := (measure_union_add_inter' hs t).symm
  have hone : μ (s ∪ t) ≤ 1 := prob_le_one
  rw [h]
  exact add_le_add hone le_rfl

-- --- the real-valued layer the Python mirrors ------------------------------------------

/-- Lower Fréchet bound on the joint rate. -/
def frechetJointLo (p q : ℝ) : ℝ := max 0 (p + q - 1)

/-- Upper Fréchet bound on the joint rate. -/
def frechetJointHi (p q : ℝ) : ℝ := min p q

/-- Lower Fréchet bound on `Δ`, i.e. on the joint shifted by the independence reference.
    Python: `dependence_parameter.frechet_bounds`, first component. -/
def frechetCollapseLo (p q : ℝ) : ℝ := frechetJointLo p q - p * q

/-- Upper Fréchet bound on `Δ`. Python: `frechet_bounds`, second component. -/
def frechetCollapseHi (p q : ℝ) : ℝ := frechetJointHi p q - p * q

/-- **A joint rate inside its Fréchet bounds puts `Δ` inside the collapse bounds.** This is
    what licenses reporting the interval as the precision of the estimate. -/
theorem collapse_mem_frechet {p q j : ℝ}
    (hlo : frechetJointLo p q ≤ j) (hhi : j ≤ frechetJointHi p q) :
    frechetCollapseLo p q ≤ j - p * q ∧ j - p * q ≤ frechetCollapseHi p q := by
  unfold frechetCollapseLo frechetCollapseHi
  constructor <;> linarith

/-- **Independence is always attainable**, so the collapse interval always contains zero ---
    the reason `Δ = 0` is a coherent null at any marginals (the P-1b'-i falsifier). -/
theorem frechet_collapse_contains_zero {p q : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    frechetCollapseLo p q ≤ 0 ∧ 0 ≤ frechetCollapseHi p q := by
  constructor
  · unfold frechetCollapseLo frechetJointLo
    rcases max_cases (0 : ℝ) (p + q - 1) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> nlinarith
  · unfold frechetCollapseHi frechetJointHi
    rcases min_cases p q with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> nlinarith

/-- **The width of the attainable `Δ` interval** depends only on the marginals. This is the
    quantity the split gate reports in place of the retired ceiling/floor drop rule. -/
theorem frechet_collapse_width (p q : ℝ) :
    frechetCollapseHi p q - frechetCollapseLo p q = min p q - max 0 (p + q - 1) := by
  unfold frechetCollapseHi frechetCollapseLo frechetJointHi frechetJointLo; ring

/-- **At equal marginals `c` with `2c ≤ 1` the width is exactly `c`.** So a pair whose
    mechanisms each fire on 2% of items can never show a collapse above 0.02, however
    captured the infosphere is: identified, but with no room to be large. -/
theorem frechet_collapse_width_equal {c : ℝ} (h0 : 0 ≤ c) (h : 2 * c ≤ 1) :
    frechetCollapseHi c c - frechetCollapseLo c c = c := by
  rw [frechet_collapse_width]
  have hmax : max 0 (c + c - 1) = 0 := max_eq_left (by linarith)
  rw [hmax, min_self]; ring

open MeasureTheory in
/-- **The bridge.** For real events under a probability measure, the joint rate does satisfy
    the hypotheses the real-valued layer assumes --- so the arithmetic above is a statement
    about probabilities, not a definition dressed as one. -/
theorem frechet_of_probability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {s : Set Ω} (hs : MeasurableSet s) (t : Set Ω) :
    (μ (s ∩ t)).toReal ≤ frechetJointHi (μ s).toReal (μ t).toReal ∧
    frechetJointLo (μ s).toReal (μ t).toReal ≤ (μ (s ∩ t)).toReal := by
  have hfin : ∀ u : Set Ω, μ u ≠ ⊤ := fun u => measure_ne_top μ u
  constructor
  · unfold frechetJointHi
    refine le_min ?_ ?_ <;>
      exact ENNReal.toReal_mono (hfin _) (measure_mono (by simp [Set.inter_subset_left,
        Set.inter_subset_right]))
  · unfold frechetJointLo
    refine max_le ?_ ?_
    · exact ENNReal.toReal_nonneg
    · have h := measure_add_le_one_add_inter μ hs t
      have h' : (μ s).toReal + (μ t).toReal ≤ 1 + (μ (s ∩ t)).toReal := by
        have := ENNReal.toReal_mono (by simp [hfin]) h
        simpa [ENNReal.toReal_add, hfin] using this
      linarith


-- ════════════════════════════════════════════════════════════════
-- §RV-G. THE ONE IMPORTED RESULT --- Gaussian-copula monotonicity.
--
-- Everything else in §RV-D/§RV-F is proved. This is not, and it is stated as an axiom so
-- `#print axioms` separates SCORE's own results from the imported one --- the discipline
-- `Score/CouplingKernel.lean` uses for BJR.
--
-- The OSSE nature-run generator (`src/ethos/osse/nature_run.py`) parameterises dependence
-- as a latent-Gaussian copula correlation and then *claims* that raising the correlation
-- raises the measured co-catch. Nothing in this repo established that; it was checked by
-- sampling the generator, which is the circularity this layer exists to remove.
--
-- **Attribution, corrected 2026-07-27 after the literature pass.** An earlier draft credited
-- Slepian (1962). That is the wrong instrument for n = 2. The governing result is the
-- bivariate identity `dPhi2(a,b;rho)/drho = phi2(a,b;rho)`, standardly **Plackett's identity**
-- (Plackett 1954) --- monotonicity is then immediate from positivity of a density. Slepian's
-- own n-dimensional recursion (his eq. 36) is credited by Slepian to **Schlafli**, not
-- Plackett; and at n = 2 Slepian's machinery collapses to differentiating an arcsine. Mathlib
-- carries none of it --- no orthant probability, no bivariate normal CDF, not even `erf`.
--
-- Discharge, with criticisms and the limits of the statement:
-- `obsidian/SCORE/methodology/CopulaMonotonicityDischarge.md`.
--
-- **The first draft of this section committed BJRDischarge's error, and the literature pass
-- caught it.** It declared `Monotone` over *all* of `ℝ`, including `|rho| > 1` where the
-- intended object does not exist, and it tied `bivariateOrthant` to nothing --- so a constant
-- function satisfied both axioms and the pair asserted almost nothing. Exactly the failure the
-- comment above it was citing. Repaired: monotonicity is now `MonotoneOn` the closed
-- correlation interval, and two characterizing axioms pin the interpretation at the two
-- points where it is known in closed form. `collapse_at_comonotone` then *derives* the §RV-F
-- Fréchet upper bound from them, which is the check that they describe the right object.
--
-- Still deliberately NOT asserted: any claim that the Gaussian copula is the right dependence
-- family. It is not implied by anything about verification mechanisms, and the family silently
-- fixes the higher-order structure that §RV-D's 2-additive truncation drops.
-- ════════════════════════════════════════════════════════════════

/-- Opaque: the standard normal CDF. Mathlib has no `erf` and no Gaussian CDF, so this
    cannot currently be defined here (checked against the pinned mathlib and master). -/
axiom stdNormalCDF : ℝ → ℝ

/-- Opaque: the standard bivariate normal orthant probability `P(Z₁ ≤ a, Z₂ ≤ b)` at
    correlation `ρ`, as the generator's copula induces it. -/
axiom bivariateOrthant : ℝ → ℝ → ℝ → ℝ

/-- **Characterizing axiom 1 --- independence at `ρ = 0`.** Without this the symbol is
    unconstrained and the monotonicity axiom below says nothing about a joint distribution. -/
axiom bivariateOrthant_indep (a b : ℝ) :
    bivariateOrthant a b 0 = stdNormalCDF a * stdNormalCDF b

/-- **Characterizing axiom 2 --- the comonotone endpoint.** At `ρ = 1` the orthant probability
    attains the Fréchet upper bound `min` of the marginals. -/
axiom bivariateOrthant_comonotone (a b : ℝ) :
    bivariateOrthant a b 1 = min (stdNormalCDF a) (stdNormalCDF b)

/-- **Monotonicity in the correlation (imported, not proved).** On the closed correlation
    interval --- and only there; outside it the object is undefined. This is the assumption that
    makes the generator's `latent_correlation` a *dependence knob* rather than an arbitrary
    parameter. Route: Plackett's identity gives `∂Φ₂/∂ρ = φ₂ > 0` on `|ρ| < 1`, with the
    endpoints by continuity. -/
axiom bivariateOrthant_monotoneOn (a b : ℝ) :
    MonotoneOn (fun ρ : ℝ => bivariateOrthant a b ρ) (Set.Icc (-1 : ℝ) 1)

/-- **The generator's declared knob moves the measured statistic the right way.** Composing
    the import with §RV-D's arithmetic: at fixed marginals, raising the copula correlation
    across the admissible interval cannot lower the redundancy-collapse `Δ`. This is the
    property D1 relies on and previously only sampled. -/
theorem collapse_mono_in_corr (zj zk cj ck : ℝ) :
    MonotoneOn (fun ρ : ℝ => bivariateOrthant zj zk ρ - cj * ck) (Set.Icc (-1 : ℝ) 1) :=
  fun _ ha _ hb h => sub_le_sub_right (bivariateOrthant_monotoneOn zj zk ha hb h) _

/-- **Consistency check: the comonotone limit is exactly §RV-F's Fréchet upper bound on `Δ`.**
    Derived from the characterizing axioms plus the proved `frechetCollapseHi`, so the imported
    symbol is pinned to an object the rest of the layer already describes. An axiom that could
    not do this would be describing something else. -/
theorem collapse_at_comonotone (a b : ℝ) :
    bivariateOrthant a b 1 - stdNormalCDF a * stdNormalCDF b
      = frechetCollapseHi (stdNormalCDF a) (stdNormalCDF b) := by
  rw [bivariateOrthant_comonotone]
  unfold frechetCollapseHi frechetJointHi
  ring


-- ════════════════════════════════════════════════════════════════
-- §RV-H. DENIAL CLOSURE --- the formal layer under issue #640's D3.
--
-- D3 asks for "one run per carrier pair with its anchor absent", classified fatal /
-- demote / survivable against PR-EX-1 §6.3's fail-to-a-finding rule. The split gate
-- (§6.3 as amended 2026-07-27) makes that request not quite expressible as stated, and
-- the reason is combinatorial rather than empirical --- so it is settled here rather
-- than reported out of a script.
--
-- **The hard identifiability clause is mechanism-level, not pair-level.** A pair is
-- unidentified when one of its mechanisms never fires; and a dormant mechanism takes out
-- *every* pair containing it at once. So "deny this pair" is not a realizable corpus
-- condition --- what a corpus can actually withhold is a mechanism.
--
-- Two consequences, both proved below by `decide` over the F0-11 §3b frozen pair set:
--   * every carrier pair touches V4 or V5 (the two carrier axes), so
--   * dormancy of **both** carriers empties the carrier set --- which is exactly §6.3's
--     void condition, "if no carrier pair clears, the RQ-1b re-specification is void".
--
-- The pair set is data, so it is encoded here and the counts are decided, not asserted.
-- `src/ethos/osse/denial.py` is checked against these statements.
-- ════════════════════════════════════════════════════════════════

/-- The F0-11 §3b frozen fitted set (FROZEN 2026-07-23). -/
inductive VMech | V2 | V4 | V6a | V6b | V5 | V8
  deriving DecidableEq, Repr

/-- The 10 permitted interaction pairs: the 9 V4/V5 carrier pairs plus the V2xV8
    validation pair (PI-ratified 2026-07-23). -/
def permittedPairs : List (VMech × VMech) :=
  [(.V2, .V4), (.V4, .V5), (.V4, .V6a), (.V4, .V6b), (.V4, .V8),
   (.V2, .V5), (.V5, .V6a), (.V5, .V6b), (.V5, .V8),
   (.V2, .V8)]

/-- The one pair with an existing external anchor seed; it checks survivor-independence
    and is *not* a carrier pair. -/
def seededPair : VMech × VMech := (.V2, .V8)

/-- The 9 carrier pairs --- those the G-anchor gate ranges over. -/
def carrierPairs : List (VMech × VMech) := permittedPairs.filter (· ≠ seededPair)

/-- Does `m` occur in the pair? -/
def touches (m : VMech) (p : VMech × VMech) : Bool := p.1 = m || p.2 = m

/-- The pairs a dormant mechanism takes out --- **all** of them at once. -/
def dormancyRemoves (m : VMech) : List (VMech × VMech) :=
  permittedPairs.filter (touches m)

/-- Carrier pairs still standing after a set of mechanisms goes dormant. -/
def survivingCarriers (dormant : List VMech) : List (VMech × VMech) :=
  carrierPairs.filter (fun p => !dormant.any (fun m => touches m p))

theorem carrierPairs_length : carrierPairs.length = 9 := by decide

/-- **Every carrier pair touches a carrier axis.** The F0-11 §3b restriction, as a fact
    about the frozen set rather than a description of it. -/
theorem carrier_touches_axis :
    ∀ p ∈ carrierPairs, touches .V4 p = true ∨ touches .V5 p = true := by decide

/-- **Dormancy is not pair-separable.** One dormant carrier removes five permitted pairs,
    so no corpus condition denies a single carrier pair in isolation. -/
theorem dormancy_V4_removes_five : (dormancyRemoves .V4).length = 5 := by decide
theorem dormancy_V5_removes_five : (dormancyRemoves .V5).length = 5 := by decide

theorem surviving_after_V4 : (survivingCarriers [.V4]).length = 4 := by decide
theorem surviving_after_V5 : (survivingCarriers [.V5]).length = 4 := by decide

/-- **Both carriers dormant empties the carrier set.** This is PR-EX-1 §6.3's void
    condition reached constructively: it is not that the corpus disappoints, it is that
    the carrier-axis restriction leaves nothing once both axes go. -/
theorem surviving_after_both_carriers : survivingCarriers [.V4, .V5] = [] := by decide

/-- A non-carrier dormancy leaves carrier pairs standing --- the seeded pair's own
    mechanisms are not load-bearing for RQ-1b's carrier set on their own. -/
theorem surviving_after_V6a : (survivingCarriers [.V6a]).length = 7 := by decide

/-- The §6.3 fail-to-a-finding verdicts. -/
inductive DenialVerdict | survivable | demote | void
  deriving DecidableEq, Repr

/-- The classification D3 reports, as a decision procedure over the frozen set:
    void when no carrier pair clears, demote when some but not all do, survivable when
    the carrier set is untouched. -/
def classifyDormancy (dormant : List VMech) : DenialVerdict :=
  if survivingCarriers dormant = [] then .void
  else if (survivingCarriers dormant).length < carrierPairs.length then .demote
  else .survivable

/-- **The void verdict is reached exactly when no carrier pair clears** --- the wording of
    §6.3, mechanized, so the classification cannot drift from the rule it implements. -/
theorem classify_void_iff (dormant : List VMech) :
    classifyDormancy dormant = .void ↔ survivingCarriers dormant = [] := by
  unfold classifyDormancy
  split
  · simp_all
  · split <;> simp_all

theorem classify_both_carriers : classifyDormancy [.V4, .V5] = .void := by decide
theorem classify_one_carrier : classifyDormancy [.V4] = .demote := by decide
theorem classify_none : classifyDormancy [] = .survivable := by decide

/-- **A dormant mechanism makes `Δ` degenerate, not merely small.** With `c_j = 0` the
    joint is 0 and the independence reference is 0, so `Δ_jk = 0` identically whatever
    `c_k` is --- the statistic returns the value it would return under independence while
    carrying no information at all. This is why the estimator must report `unidentified`
    rather than `0.0`: the number is indistinguishable from a measurement of independence
    and is not one. -/
theorem collapse_degenerate_of_dormant (ck : ℝ) :
    redundancyCollapse 0 ck (0 + ck - 0) = 0 := by
  unfold redundancyCollapse pairMobiusIndep pairMobius pairAssuranceIndep; ring

/-- **And its Fréchet interval collapses to a point.** At a dormant marginal there is no
    room for dependence to show at all --- the precision clause and the identifiability
    clause agree in the degenerate case, which is the consistency check on the split. -/
theorem frechet_width_zero_of_dormant {ck : ℝ} (h0 : 0 ≤ ck) (h1 : ck ≤ 1) :
    frechetCollapseHi 0 ck - frechetCollapseLo 0 ck = 0 := by
  unfold frechetCollapseHi frechetCollapseLo frechetJointHi frechetJointLo
  rw [min_eq_left h0, max_eq_left (by linarith)]
  ring


-- ════════════════════════════════════════════════════════════════
-- §RV-I. IDENTIFIABILITY --- can P-1b'-i and P-1b'-iii dissociate?
--
-- Issue #640's D4 asks where the two RQ-1b predictions are indistinguishable. Per the
-- crosswalk (PI-ratified 2026-07-28) they are **P-1b'-i** (some pairwise redundancy
-- collapse is significantly positive) and **P-1b'-iii** (the fitted-capacity assurance
-- `T_fit` is distinguishable from the flat-product prediction).
--
-- D4 was scoped as a sweep. It does not need one: the relation is an identity, and the
-- identity settles the question for every parameter value at once. Written at n = 3, the
-- smallest arity where the 2-additive truncation bites.
--
-- `T_fit` is the 2-additive capacity's assurance at the full set: singletons plus pairwise
-- Möbius mass. With `m_fit = m_indep - Δ` (§RV-D) that gives
--
--     ΔT  =  T_fit - T_flat  =  (2-additive truncation error)  -  Σ Δ
--
-- and the truncation error is `-abc`, a function of the **marginals alone**. Two
-- consequences, both proved below, and both bearing on whether RQ-1b's re-specified
-- predictions are separately falsifiable.
-- ════════════════════════════════════════════════════════════════

/-- Independent-OR assurance at n = 3 --- the flat-product prediction P-1b'-iii compares to. -/
def assuranceIndep3 (a b c : ℝ) : ℝ := 1 - (1 - a) * (1 - b) * (1 - c)

/-- The 2-additive capacity's assurance at the full set: singletons plus pairwise Möbius,
    with every pair at its independence reference. -/
def assurance2Additive3 (a b c : ℝ) : ℝ := a + b + c - (a * b + a * c + b * c)

/-- The fitted assurance: the same, with each pair's collapse subtracted (`m_fit = m_indep - Δ`). -/
def assuranceFitted3 (a b c dab dac dbc : ℝ) : ℝ :=
  assurance2Additive3 a b c - (dab + dac + dbc)

/-- **The truncation error is `-abc`** --- the third-order Möbius mass a 2-additive fit omits,
    signed. Consistent with `tripleMobiusIndep_eq`, which gives that mass as `+abc`. -/
theorem truncation_error_eq (a b c : ℝ) :
    assurance2Additive3 a b c - assuranceIndep3 a b c = -(a * b * c) := by
  unfold assurance2Additive3 assuranceIndep3; ring

/-- **`ΔT` is affine in the sum of the collapses**, with an offset fixed by the marginals. -/
theorem deltaT_eq (a b c dab dac dbc : ℝ) :
    assuranceFitted3 a b c dab dac dbc - assuranceIndep3 a b c
      = -(a * b * c) - (dab + dac + dbc) := by
  unfold assuranceFitted3 assurance2Additive3 assuranceIndep3; ring

/-- **P-1b'-iii fires on a perfectly independent corpus.** With every collapse zero --- the
    state ETHOS's theory calls a *healthy* infosphere --- `ΔT = -abc`, strictly negative
    whenever the three marginals are positive. So a nonzero `ΔT` is not evidence of captured
    structure: the 2-additive truncation alone produces one. -/
theorem deltaT_nonzero_at_independence {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    assuranceFitted3 a b c 0 0 0 - assuranceIndep3 a b c < 0 := by
  rw [deltaT_eq]
  have : 0 < a * b * c := by positivity
  linarith

/-- **The two predictions cannot dissociate.** At fixed marginals, `T_fit` determines the
    *total* collapse and nothing else: two collapse profiles give the same fitted assurance
    exactly when their sums agree. So P-1b'-iii carries no information about the interaction
    structure that P-1b'-i does not already carry --- it is a coarsening of it, not an
    independent test. -/
theorem deltaT_determines_collapse_sum (a b c d1 d2 d3 e1 e2 e3 : ℝ) :
    assuranceFitted3 a b c d1 d2 d3 = assuranceFitted3 a b c e1 e2 e3
      ↔ d1 + d2 + d3 = e1 + e2 + e3 := by
  unfold assuranceFitted3 assurance2Additive3
  constructor <;> intro h <;> linarith

/-- **P-1b'-iii's falsifier is unreachable under capture.** Its falsifier is `T_fit`
    statistically indistinguishable from the flat product, i.e. `ΔT = 0`. But with every
    collapse nonnegative --- which is what capture means (§3a: `Δ ≥ 0` under capture) --- `ΔT`
    is bounded strictly away from zero by the truncation error alone:

        ΔT = -abc - Σ Δ  ≤  -abc  <  0.

    So no captured corpus can trigger the falsifier. It can be triggered only by an
    *anti-captured* corpus whose total collapse is negative and of the right magnitude, or by
    a sample too noisy to resolve `abc`. The first is not the alternative RQ-1b is testing
    against and the second is a failure of power, not of structure --- which is the entailment
    pattern the pre-lock audit found in the *original* P-1b-i/ii/iii, recurring here in the
    re-specified P-1b'-iii. -/
theorem deltaT_neg_of_nonneg_collapses {a b c dab dac dbc : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : 0 ≤ dab) (h2 : 0 ≤ dac) (h3 : 0 ≤ dbc) :
    assuranceFitted3 a b c dab dac dbc - assuranceIndep3 a b c < 0 := by
  rw [deltaT_eq]
  have : 0 < a * b * c := by positivity
  linarith

/-- **And the coarsening is lossy in the direction that matters.** P-1b'-i is a claim about
    *which* pairs collapse --- section 4 requires the collapse "concentrated on the pairs F0-11
    section 5 flags as capture-carriers". `T_fit` sees only the total, so it cannot distinguish
    a carrier-concentrated profile from a diffuse one of equal sum. -/
theorem fitted_assurance_blind_to_concentration (a b c d : ℝ) :
    assuranceFitted3 a b c d d d = assuranceFitted3 a b c (3 * d) 0 0 := by
  unfold assuranceFitted3 assurance2Additive3; ring


-- ════════════════════════════════════════════════════════════════
-- §PS-U2. ETHOS U2 SPECIALIZATION --- EpistemicCommunity as an A-actor-
-- scoped HOAState AND EpistemicInstitution as a Σ-actor (Present-Domain
-- → Present-Formal); together they formalize the dual-stratum framing.
--
-- The HM Specialization Audit (`core/ethos/ETHOS_HM_Specialization_Audit.md`
-- §1) rated U2 as Present-Domain because ET-G-01
-- (`ethos:EpistemicCommunity` refining SC-G-25 HOA / SC-G-26 HumanCommunity)
-- named the HOA analog at the glossary + OWL layer but no Lean
-- specialization instantiated §HM's `HOAState` machinery. This section is
-- that specialization plus a companion Σ-actor typedef for the co-existing
-- `EpistemicInstitution` (ET-G-02) that jointly encode the dual-stratum
-- framing (Orphan 7 of the ETHOS audit: "EpistemicCommunity + Epistemic-
-- Institution both first-class in E1; neither reduces to the other").
--
-- Third and final polar case of Design B's `Constituent` sum type after
-- AGORA (A-actor only, §PS-U2) and ATLAS (Σ-actor only, §PS-U2). ETHOS's
-- distinctive contribution: BOTH types co-exist as first-class objects
-- at the Lean layer, not just at the glossary layer --- the maintaining
-- community (A-actor HOA) sustains the institution (Σ-actor) and neither
-- is a reduction of the other.
-- ════════════════════════════════════════════════════════════════

/-- **ETHOS's `EpistemicCommunity` as an HOAState subtype** (ET-G-01,
    refining SC-G-25 HOA). The A-actor coupling network (journalists,
    academics, researchers) whose collective NS produces the corpus.
    Same shape as `AgoraMaintainingCommunity` (both are A-actor HOAs);
    distinct type because their peer-level semantics differ (institutional
    maintenance vs epistemic knowledge production). -/
def EthosEpistemicCommunity (r : Region) : Type :=
  { s : HOAState r //
    ∀ c ∈ s.agents, ∃ a : Agent, c = Constituent.AAgent a }

/-- Extract the underlying `HOAState`; the §HM machinery applies via
    this projection. -/
def EthosEpistemicCommunity.toHOAState {r : Region}
    (ec : EthosEpistemicCommunity r) : HOAState r := ec.1

/-- **A-actor constraint witness.** Every constituent of an ETHOS
    epistemic community is a `Constituent.AAgent` --- the direct
    formalization of the ET-G-01 A-actor-population claim. -/
theorem EthosEpistemicCommunity.agents_are_AAgent {r : Region}
    (ec : EthosEpistemicCommunity r) :
    ∀ c ∈ ec.toHOAState.agents, ∃ a : Agent, c = Constituent.AAgent a :=
  ec.2

/-- **ETHOS's `EpistemicInstitution` as a Σ-actor** (ET-G-02, refining
    SC-G-09). A journal / discipline / news outlet as a co-inscribed
    formal B₃ membrane plus a maintaining community; the primary
    B₃-producing actor in the ETHOS domain. Encoded as a typedef over
    `SigmaActor` --- ETHOS's peer-specific narrative attaches to the
    Σ-actor role Core already provides; no additional Lean structure
    needed for this tier. Capture-at-Σ (ownership concentration, funding
    capture) and capture-at-Ω (engagement-optimizing platforms) live at
    the peer level, not §HM. -/
def EthosEpistemicInstitution : Type := SigmaActor

/-!
## Dual-stratum framing --- documented, enforced by construction

ETHOS's distinctive framing (Orphan 7 of the ETHOS audit) is that community
and institution co-exist without reduction. That claim is enforced at the
type layer by construction: `EthosEpistemicCommunity r` is a subtype of
`HOAState r` (a structure with agents / substrate / loopEndowment / etc.
fields), while `EthosEpistemicInstitution` is a typedef over `SigmaActor`
(an opaque Core carrier type). There is no cast between them --- ETHOS's
dual-stratum claim holds at the Lean type layer with no additional
theorems required.

Peer-side operations that relate the two --- e.g., "which community
sustains this institution?" --- would be modeled as separate axiom
relations (`sustains : EthosEpistemicInstitution → (r : Region) →
EthosEpistemicCommunity r → Prop`), reserved for future peer-specialization
work that goes beyond U2's HOA-typing scope.
-/


-- ════════════════════════════════════════════════════════════════
-- §PS-U1. ETHOS U1 SPECIALIZATION --- EpistemicCommunity self-
-- stabilization (Present-Domain → Present-Formal)
--
-- The HM Specialization Audit (`ETHOS_HM_Specialization_Audit.md` §1)
-- rated ETHOS's U1 as Present-Domain: EpistemicCommunity sustaining a
-- corpus IS self-stabilization at vocabulary level; Core-promoted
-- `FitnessCriterion` (via POLARIS∩ETHOS) is the fitness under which the
-- community self-stabilizes. No Lean specialization of
-- `SelfStabilizingWithin` existed. Peer-scoped abbrev over §HM's
-- polymorphic predicate, parameterized on the ETHOS U2 type
-- `EthosEpistemicCommunity`. Concrete Basin/Legitimate/Moves choices
-- (Legitimate = InfosphereHealthScore threshold; Moves = capture
-- dynamics; Basin = uncaptured domain) are Q4 BIND / peer-specific
-- future work.
-- ════════════════════════════════════════════════════════════════

/-- **ETHOS U1: self-stabilization of the epistemic community.**
    Peer-scoped abbrev for `SCORE.SelfStabilizingWithin` on
    `EthosEpistemicCommunity` (ET-G-01). Concrete Basin/Legitimate/Moves
    peer-specific. -/
def EthosEpistemicCommunity.stabilizesWithin {r : Region}
    (Basin      : EthosEpistemicCommunity r → Prop)
    (Legitimate : EthosEpistemicCommunity r → Prop)
    (Moves      : EthosEpistemicCommunity r → EthosEpistemicCommunity r → Prop) : Prop :=
  SelfStabilizingWithin Basin Legitimate Moves


-- ════════════════════════════════════════════════════════════════
-- §PS-U4. ETHOS U4 SPECIALIZATION --- autocatalytic feedback +
-- B₃-substrate prosthetic (Present-Domain → Present-Formal)
--
-- The HM Specialization Audit (`ETHOS_HM_Specialization_Audit.md` §1)
-- rated ETHOS's U4 as Present-Domain: `DisciplinaryCorpus` (ET-G-11)
-- is the B₃-substrate; `cites` edges (ET-G-12) build the derivation DAG;
-- `AmplificationChannel` (ET-G-07) is the propagation mechanism.
-- Autocatalytic loop is explicit at the vocabulary layer (high-quality
-- content amplified → shapes future producers → produces more
-- high-quality content). `Score/Ethos.lean` §15 specializes
-- DisciplinaryCorpus as `Core.DoctrinalNetwork`, NOT as §HM's
-- `AutocatalyticCombine`. This section binds §HM's autocatalytic
-- machinery to `EthosEpistemicCommunity` via peer-scoped wrappers.
-- ════════════════════════════════════════════════════════════════

/-- **ETHOS U4: autocatalytic weight of the epistemic community.**
    Aggregate observable weight under a chosen autocatalytic-combine
    operator, delegated via the peer's `.toHOAState` projection. -/
def EthosEpistemicCommunity.autocatalyticWeight {r : Region}
    (c : AutocatalyticCombine) (ec : EthosEpistemicCommunity r) : ℝ :=
  HOAState.weight c ec.toHOAState

/-- **ETHOS U4: hysteresis gap closes for the epistemic community.**
    Direct specialization of `AutocatalyticCombine.closes_hysteresis_gap`
    via the peer's `.toHOAState` projection. -/
theorem EthosEpistemicCommunity.autocatalytic_closes_gap {r : Region}
    (c : AutocatalyticCombine) (ec : EthosEpistemicCommunity r)
    (hs : (dissolutionThreshold r).val ≤ ec.toHOAState.substrate.val)
    (he : c.engagementThreshold r ≤ ec.toHOAState.loopEndowment.val) :
    (formationThreshold r).val ≤ ec.autocatalyticWeight c :=
  c.closes_hysteresis_gap r
    ec.toHOAState.substrate ec.toHOAState.loopEndowment hs he


-- ════════════════════════════════════════════════════════════════
-- §PS-PA. ETHOS central-lemma binding to §HM30 point-attenuation
-- family (audit synthesis §5.4 PointAttenuationLemma 5-peer echo)
--
-- ETHOS's `capture_cannot_increase_information_health` is the
-- scalar-multiplication attenuation shape: `capturedHealth κ H = κ·H`,
-- and for H ≥ 0 the map `x ↦ x·H` is monotone; applied to `κ ≤ 1`
-- this yields `κ·H ≤ 1·H = H`. The witness below binds this
-- explicitly to `point_attenuation_monotone`, making the §HM30
-- family membership explicit.
-- ════════════════════════════════════════════════════════════════

/-- **ETHOS captured-health as §HM30 `point_attenuation_monotone`.**
    Formal witness that the capture-cannot-increase-info-health result
    is an instance of the §HM30 point-level monotone attenuation family.
    Uses `f = (· * H)` monotone (from `H ≥ 0`) applied to `κ ≤ 1`. -/
theorem capturedHealth_as_pointAttenuationMonotone
    {κ H : ℝ} (hκ : κ ≤ 1) (hH : 0 ≤ H) :
    capturedHealth κ H ≤ H := by
  have hmono : Monotone (fun x : ℝ => x * H) :=
    fun _ _ h => mul_le_mul_of_nonneg_right h hH
  have := point_attenuation_monotone (fun x => x * H) hmono hκ
  unfold capturedHealth
  simpa using this


-- ════════════════════════════════════════════════════════════════
-- §PS-HM31. ETHOS InfosphereHealthScore as §HM31 CompositeMeasure
-- instance (audit synthesis §5.4 CompositeSigmaActorHealthScore 3-peer
-- echo).
--
-- ET-G-04 InfosphereHealthScore is a distribution-valued composite
-- H = Q × κ × β (Floridi content quality × capture discriminant ×
-- OMBF fairness). This section constructs a `CompositeMeasure`
-- instance over `EthosEpistemicCommunity` whose three factors are
-- peer-scoped opaque functions (Q4 BIND) matching the ET-G-04
-- decomposition. Scalar-valued at this tier.
-- ════════════════════════════════════════════════════════════════

/-- **Q factor** of ETHOS's InfosphereHealthScore --- Floridi content
    quality per ET-G-05. Q4 BIND. -/
axiom ethosContentQuality {r : Region} : EthosEpistemicCommunity r → ℝ

/-- **κ factor** of ETHOS's InfosphereHealthScore --- capture
    discriminant per ET-G-06. Q4 BIND. The reusable point-level
    attenuation content is captured by
    `capturedHealth_as_pointAttenuationMonotone` (§PS-PA) at a
    different scope. -/
axiom ethosCaptureDiscriminant {r : Region} : EthosEpistemicCommunity r → ℝ

/-- **β factor** of ETHOS's InfosphereHealthScore --- OMBF equitable-
    propagation term per ET-G-09. Q4 BIND. -/
axiom ethosFairness {r : Region} : EthosEpistemicCommunity r → ℝ

/-- **ETHOS InfosphereHealthScore as §HM31 CompositeMeasure instance.**
    H = Q × κ × β lifts to `CompositeMeasure.value` on the peer's U2
    type. -/
noncomputable def ethosInfosphereHealthScore {r : Region} :
    CompositeMeasure (EthosEpistemicCommunity r) :=
  { arity := 3,
    factor := ![ethosContentQuality, ethosCaptureDiscriminant, ethosFairness] }


-- ════════════════════════════════════════════════════════════════
-- §PS-HM36. ETHOS AdjacentPossibleMeasure instance (audit synthesis
-- §5.6 development-gap item 5, `core:AdjacentPossibleMeasure`)
--
-- ET-G-06 characterizes κ as the epistemic-domain instance of NS
-- contracting the reachable region of true B₃. This section
-- constructs an `AdjacentPossibleMeasure` instance parameterized by
-- the alternative-content type α, with the reachable set being the
-- corpus-consistent B₂ configurations and the breadth functional
-- expressing epistemic-reach. Concrete numeric κ is Q4 BIND.
-- ════════════════════════════════════════════════════════════════

/-- **ETHOS adjacent-possible measure.** Parameterized by the
    alternative type α, the reachable set (corpus-consistent B₂
    configurations), and the breadth functional. Concrete forms are
    Q4 BIND. -/
def ethosAdjacentPossible {α : Type}
    (reachable : Set α) (Φ : Set α → ℝ) : AdjacentPossibleMeasure α :=
  { reachable := reachable
    breadth   := Φ }


-- ════════════════════════════════════════════════════════════════
-- §PS-HM38. ETHOS FitnessCriterion instance (audit synthesis §5.6
-- development-gap item 7, `core:FitnessCriterion`)
--
-- ET-G-03 Floridi information health is ETHOS's fitness criterion ---
-- the first-invoked Q3 promotion of FitnessCriterion to Core (on the
-- POLARIS/ETHOS intersection). This section constructs a
-- `FitnessCriterion` instance where the fitness function is the
-- InfosphereHealthScore composite (H = Q × κ × β) evaluated on an
-- epistemic community, and the threshold is peer-scoped
-- (Q4 BIND per calibration).
-- ════════════════════════════════════════════════════════════════

/-- **Floridi fitness threshold** for the ETHOS information-health
    fitness criterion. Q4 BIND per ETHOS-InformationHealth.md
    calibration. -/
axiom ethosFloridiFitnessThreshold : ℝ

/-- **ETHOS Floridi FitnessCriterion instance.** Fitness function is
    `CompositeMeasure.value ethosInfosphereHealthScore` (Q × κ × β
    lifted to the composite value), threshold is
    `ethosFloridiFitnessThreshold`. An epistemic community is "fit"
    when its InfosphereHealthScore exceeds the threshold. -/
noncomputable def ethosFloridiFitness {r : Region} :
    FitnessCriterion (EthosEpistemicCommunity r) :=
  { fitness := ethosInfosphereHealthScore.value
    threshold := ethosFloridiFitnessThreshold }


-- ════════════════════════════════════════════════════════════════
-- §PS-HM40. ETHOS SpectralEWS instance (audit synthesis §5.6
-- development-gap item 6, `core:SpectralEarlyWarningIndicator`)
--
-- ET-G-13 InfosphereSpectralEWS is the n=3 filler of SC-G-49 alongside
-- POLARIS SEWI. `Score/Ethos.lean` already carries `ethosSpectralEWS`
-- and `ethosSpectralEWS_monotone` (built on `SCORE.spectralEWS` /
-- `SCORE.spectral_ews_monotone` from Core.lean §Spectral). This section
-- wraps ETHOS's arity-3 signature-weight configuration in a §HM40
-- `SpectralEWSInstance` structure.
-- ════════════════════════════════════════════════════════════════

/-- **ETHOS signature weights** for the arity-3 spectral EWS.
    Three nonneg weights composing critical-slowing-down signatures
    (low-frequency variance ratio, lag-1 autocorrelation, spectral-
    centroid drift). Q4 BIND per E5 calibration. -/
axiom ethosSpectralEWSWeights : Fin 3 → ℝ

/-- **Nonneg-weight condition on ETHOS spectral weights.** Q4 BIND
    calibration constraint --- LOAD-BEARING per
    `governance/SCORE_HM_Peer_Axiom_Audit.md` §5.1 (Category C):
    Phase F could falsify this if calibration warrants a negative
    weight on some signature (e.g., anti-correlation with EWS). -/
axiom ethosSpectralEWSWeights_nonneg : ∀ i, 0 ≤ ethosSpectralEWSWeights i

/-- **ETHOS SpectralEWS as §HM40 SpectralEWSInstance.** Arity 3 with
    the peer's signature weights. -/
noncomputable def ethosSpectralEWSInstance : SpectralEWSInstance :=
  { arity := 3
    weights := ethosSpectralEWSWeights
    weights_nonneg := ethosSpectralEWSWeights_nonneg }


-- ════════════════════════════════════════════════════════════════
-- §PS-HM41. ETHOS ethosCorpus binding to §HM41
-- DoctrinalNetworkL2Preserves (audit synthesis §5.6 development-gap
-- item 8, universal DoctrinalNetwork L2-specialization)
--
-- ET-G-11 DisciplinaryCorpus is ETHOS's DoctrinalNetwork specialization
-- (per Ethos.lean §15 = SS15) --- graded down-set of the citation DAG
-- under `ethosCites`. Epistemic communities transmit knowledge across
-- research generations via citations (audit's peer-story for L2
-- correspondence). This section asserts the L2/ethosCorpus
-- correspondence at the §HM41 level, completing the 5-peer witness
-- suite for §HM41 (BAC + NEXUS + AGORA + ATLAS + ETHOS).
-- ════════════════════════════════════════════════════════════════

/-- **ETHOS ethosCorpus getter** for §HM41 binding. Projects an HOAState
    to its ETHOS DisciplinaryCorpus down-closure. Q4 BIND. -/
axiom ethosCorpusGetter : ∀ {r : Region},
  HOAState r → Set EClaim

/-- **ETHOS DisciplinaryCorpus preserves under L2** (§PS-HM41 axiom).
    Successful generational renewal in an epistemic community preserves
    the DisciplinaryCorpus down-closure as an `ethosNetwork`-region.
    Formalizes the citation-across-research-generations transmission
    story.

    LOAD-BEARING per `governance/SCORE_HM_Peer_Axiom_Audit.md` §5.2
    (Category C): Phase F could falsify this if a real ETHOS L2 event
    (research-generation transition via citation propagation) either
    shrinks the DisciplinaryCorpus or produces a non-region post-state. -/
axiom ethosCorpus_L2preserves : ∀ {r : Region} (s s' : HOAState r),
  DoctrinalNetworkL2Preserves ethosNetwork ethosCorpusGetter s s'


end SCORE
