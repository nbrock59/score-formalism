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


end SCORE
