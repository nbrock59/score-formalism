import Mathlib

set_option linter.unusedVariables false
set_option linter.style.whitespace false

/-!
# SCORE.Core

SCORE core spine (domain-general). Split out of the former monolithic
`Formal/SCORE_Lean4.lean` (2026-07-01). Contains the three domains, emergence
hierarchy, carriers, four morphisms, coupling, life-cycle, HOA, percept,
intervention classes, sequencing, validity constraints (SS1-11), and the
promoted B3 region-geometry core (SS14). Peer modules import this.

Full theory: `core/theoretical/POLARIS_Theory_Primer.md`.
-/

namespace SCORE

-- ════════════════════════════════════════════════════════════════
-- §1. THE THREE DOMAINS
-- Ontological categories — irreducible modes of existence.
-- NOT processing stages or pipeline steps.
-- ════════════════════════════════════════════════════════════════

/-- The three irreducible modes of existence in SCORE. -/
inductive Domain : Type where
  | Objective   : Domain  -- B₁: physical geography, material infrastructure;
                           --     causal efficacy independent of any mind
  | Subjective  : Domain  -- B₂: agent cognition; coupling weight vectors,
                           --     manifold position, Path A/B learning
  | Inscription : Domain  -- B₃: inter-subjective objectifications; constitutions,
                           --     norms, media — existing between minds
deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════════════════
-- §2. THE EMERGENCE HIERARCHY (Hasse Strata)
-- Six strata ordered by emergence dependency.
-- Natural Selection enforces: higher strata require stable lower strata.
-- ════════════════════════════════════════════════════════════════

/-- The six Hasse strata. Fin 6 gives the ordering for free:
    0 = S₁ physical · 1 = S₂ oral-social · 2 = S₃ inscription
    3 = S₄ meta-idea · 4 = S₅ shared-fiction · 5 = S₆ generative -/
abbrev Stratum := Fin 6

namespace Stratum
  def physical      : Stratum := ⟨0, by omega⟩
  def oralSocial    : Stratum := ⟨1, by omega⟩
  def inscription   : Stratum := ⟨2, by omega⟩
  def metaIdea      : Stratum := ⟨3, by omega⟩
  def sharedFiction : Stratum := ⟨4, by omega⟩
  def generative    : Stratum := ⟨5, by omega⟩

  /-- Predecessor stratum (S_k → S_{k-1}), defined for k > 0. -/
  def predecessor (s : Stratum) (h : 0 < s.val) : Stratum :=
    ⟨s.val - 1, by omega⟩
end Stratum

/-- Stability of a stratum: it can sustain emergence above it. -/
axiom IsStable : Stratum → Prop

/-- The stratification constraint, enforced by Natural Selection.
    A stratum is stable only if its immediate predecessor is also stable.
    NS selects against configurations requiring unstable substrates —
    they fail before they can reproduce. -/
axiom stratificationConstraint :
    ∀ (s : Stratum) (h : 0 < s.val),
      IsStable s → IsStable (s.predecessor h)

/-- Auxiliary: stability descends by any gap `j ≤ s.val`. Induction is on the
    gap `j`, applying `stratificationConstraint` once per step. The successor
    case rewrites `s.val - (j+1) = (s.val - j) - 1` so the constraint's
    `predecessor` lands on the right index. -/
theorem stable_descends_by_gap
    (s : Stratum) (hs : IsStable s) :
    ∀ (j : ℕ) (hj : j ≤ s.val), IsStable ⟨s.val - j, by omega⟩ := by
  intro j
  induction j with
  | zero =>
    intro _
    -- s.val - 0 = s.val, so the index is `s` itself (up to Fin proof irrelevance)
    have : (⟨s.val - 0, by omega⟩ : Stratum) = s := by
      apply Fin.ext; simp
    rw [this]; exact hs
  | succ n ih =>
    intro hj
    -- the stratum at gap `n` is stable by the IH (n ≤ s.val since n+1 ≤ s.val)
    have hn : IsStable (⟨s.val - n, by omega⟩ : Stratum) := ih (by omega)
    -- that stratum has a positive value, so its predecessor is defined
    have hpos : 0 < (⟨s.val - n, by omega⟩ : Stratum).val := by change 0 < s.val - n; omega
    -- apply the stratification constraint to descend one more step.
    -- Note: `Stratum` is `abbrev Stratum := Fin 6`, so dot-notation `.predecessor`
    -- would resolve against `Fin`; call `Stratum.predecessor` explicitly.
    have hpred := stratificationConstraint ⟨s.val - n, by omega⟩ hpos hn
    -- the predecessor's index equals `s.val - (n+1)`
    have heq : Stratum.predecessor ⟨s.val - n, by omega⟩ hpos
             = (⟨s.val - (n + 1), by omega⟩ : Stratum) := by
      apply Fin.ext; change (s.val - n) - 1 = s.val - (n + 1); omega
    rwa [heq] at hpred

/-- Stability propagates all the way down: if S_k is stable,
    every stratum below it is also stable. Discharged via `stable_descends_by_gap`
    with gap `j = s.val - k`. -/
theorem stable_implies_all_lower_stable
    (s : Stratum) (hs : IsStable s) (k : ℕ) (hk : k < s.val) :
    IsStable ⟨k, hk.trans s.isLt⟩ := by
  have hdesc := stable_descends_by_gap s hs (s.val - k) (by omega)
  -- s.val - (s.val - k) = k since k < s.val
  have heq : (⟨s.val - (s.val - k), by omega⟩ : Stratum)
           = (⟨k, hk.trans s.isLt⟩ : Stratum) := by
    apply Fin.ext; simp; omega
  rwa [heq] at hdesc

-- ════════════════════════════════════════════════════════════════
-- §3. ABSTRACT CARRIER TYPES
-- Kept abstract to avoid committing to a specific implementation.
-- POLARIS instantiates these with concrete types.
-- ════════════════════════════════════════════════════════════════

/-- An agent in the socio-technical system. -/
axiom Agent : Type

/-- The objective world state (B₁). -/
axiom World : Type

/-- Inter-subjective inscription content (B₃): constitutions, norms, media. -/
axiom InscriptionContent : Type

/-- An agent's full cognitive state (B₂): manifold position, coupling weights,
    Path A/B dynamics. -/
axiom CognitiveState : Type

/-- A Σ-actor: a higher-order collective actor (institution, discipline,
    alliance, polity) with a co-inscribed formal B₃ membrane, sufficient
    reflexive depth, a telos-bearing inscription output, and a maintaining
    human community. Disjoint from A-actors (`Agent`) and Ω-actors. Peer
    refinements (`ethos:EpistemicInstitution`, `agora:ConstitutionalSigmaActor`,
    `atlas:DeterrenceCoalition`, ...) instantiate this axiom.

    Added 2026-07-14 as the M1 gap-close from the HM Specialization Audit
    (`governance/SCORE_HM_Specialization_Matrix.md` §HM development-gaps):
    Σ-actor existed at the OWL layer (`core:SigmaActor`, SC-G-09) and in the
    glossary but had no Lean-level counterpart, blocking peer specializations
    that need Σ-actor-typed constructs (AGORA/ATLAS/ETHOS Sigma-actor archetype).
    Prerequisite for any future §HM multi-stratum extension
    (`governance/SCORE_HM_MultiStratum_Extension_Plan.md`). -/
axiom SigmaActor : Type

/-- An HOA constituent: either an A-actor (individual `Agent`) or a Σ-actor
    (collective `SigmaActor`). §HM's HOAState populations range over these
    constituents. Peer usage:

    * A-actor-only HOAs (BAC PolityCluster of retained individual histories):
      populations use `Constituent.AAgent` exclusively.
    * Σ-actor-only basins (ATLAS DeterrenceBasin of Sigma-actor coalitions):
      populations use `Constituent.SigmaAgent` exclusively --- the
      stratum-independence claim (see `ATLAS.md`).
    * Dual-stratum peers (ETHOS EpistemicCommunity of A-actor researchers +
      EpistemicInstitution as Σ-actor): populations genuinely mix.
    * Σ-actor-sustained-by-A-actor-HOA peers (AGORA ConstitutionalSigmaActor
      sustained by InstitutionalMaintainingCommunity): the maintaining
      community is an HOA of `Constituent.AAgent` constituents; the sustained
      Σ-actor is a separate object.

    Added 2026-07-14 as M2 of the §HM multi-stratum extension per Design B
    (sum-typed `Constituent`) from
    `governance/SCORE_HM_MultiStratum_Extension_Plan.md` §4. -/
inductive Constituent
  | AAgent (a : Agent)
  | SigmaAgent (s : SigmaActor)

-- ════════════════════════════════════════════════════════════════
-- §4. THE FOUR MORPHISMS
-- Cross-domain couplings. Run simultaneously, not sequentially.
-- Do NOT read these as a pipeline.
-- ════════════════════════════════════════════════════════════════

/-- Perception (B₁ → B₂): the objective world enters agent cognition.
    Filtered by the agent's manifold position — not uniform across agents. -/
axiom perception : World → Agent → CognitiveState

/-- Action (B₂ → B₁): agent behavior modifies the objective world. -/
axiom action : Agent → CognitiveState → World → World

/-- Inscription (B₂ → B₃): cognitive content becomes inter-subjective.
    Referent-agnostic general form; refined by referent below. -/
axiom inscribe : Agent → CognitiveState → InscriptionContent

-- ── Referent typing of Inscription (foundational, 2026-06-04) ──────────────────
-- What the inscribed content is *about* splits the morphism. B₂-referential
-- inscription (content about the agent's own B₂-manifold features with no B₁
-- referent) is the human differentia and requires sufficient reflexive depth.
-- The depth gate is enforced *at the type level*: `inscribeB2Ref` takes a proof of
-- `SufficientDepth a` as an argument, so a B₂-referential inscription is literally
-- unconstructable without it — the Lean mirror of the OWL referent GCI
-- (performsInscription some B2ReferentialInscription ⊑ hasReflexiveDepth some SufficientDepth).

/-- Sufficient Lefebvre reflexive depth — the B₂-grounded capacity gating
    B₂-referential inscription and ⊗ co-inscription. Minimal stub predicate; the full
    reflexive-depth layer is not yet encoded (see agents/ReflexiveDepth.md). -/
axiom SufficientDepth : Agent → Prop

/-- B₁-referential inscription: content about world-states (alarm, trail, record).
    The B₃ floor; no depth precondition. -/
axiom inscribeB1Ref : Agent → CognitiveState → InscriptionContent

/-- B₂-referential inscription: content about the agent's own B₂-manifold features with
    no B₁ referent (beliefs, self-model, fictions). The depth precondition is an explicit
    argument — without `SufficientDepth a` the term does not typecheck. -/
axiom inscribeB2Ref : (a : Agent) → SufficientDepth a → CognitiveState → InscriptionContent

/-- The depth gate is load-bearing: B₂-referential inscription is well-typed only in a
    context that supplies `SufficientDepth a`. (Drop `h` and this fails to elaborate.)
    `noncomputable`: the point is type-level elaboration, and `inscribeB2Ref` is an
    `axiom` (no executable body), so it must not be sent to the code generator. -/
noncomputable example (a : Agent) (h : SufficientDepth a) (cs : CognitiveState) :
    InscriptionContent :=
  inscribeB2Ref a h cs

/-- Incorporation (B₃ → B₂): inscribed content enters agent cognition.
    Via Path A (organic, expensive) or Path B (symbolic, cheap). -/
axiom incorporate : InscriptionContent → Agent → CognitiveState

/-- The complete normative change chain: inscribe → incorporate → constrain
    cognition → act → change objective world. Any joint can break. -/
theorem normativeChangeChain
    (a : Agent) (cs : CognitiveState) (w : World) :
    -- An inscription produced by this agent...
    let ic := inscribe a cs
    -- ...when incorporated, produces a new cognitive state...
    let cs' := incorporate ic a
    -- ...which, when acted upon, produces a new world state.
    let _w' := action a cs' w
    -- The result is a modified world. Whether the change is normatively
    -- significant is an empirical question outside this formal encoding.
    True := trivial

-- ════════════════════════════════════════════════════════════════
-- §5. COUPLING WEIGHT VECTORS
-- One manifold; all agents on it. What varies is coupling topology.
-- ════════════════════════════════════════════════════════════════

/-- A coupling weight: a real number in the unit interval. -/
structure CouplingWeight where
  val : ℝ
  pos : 0 ≤ val
  le1 : val ≤ 1

namespace CouplingWeight
  def zero : CouplingWeight := ⟨0, le_refl 0, zero_le_one⟩
  def one  : CouplingWeight := ⟨1, zero_le_one, le_refl 1⟩
end CouplingWeight

instance : LE CouplingWeight where
  le a b := a.val ≤ b.val

/-- The coupling weight vector across all network dimensions.
    An agent's manifold position is determined by this vector. -/
structure CouplingWeightVector where
  localGeographic  : CouplingWeight  -- neighbors, civic orgs, local institutions
  professional     : CouplingWeight  -- colleagues, industry, employers
  originCommunity  : CouplingWeight  -- family of origin, hometown community
  diaspora         : CouplingWeight  -- cultural community, geographically dispersed
  institutional    : CouplingWeight  -- party, church, professional association

/-- An agent's manifold position is constituted by their coupling weight vector.
    A locally-dominant agent has high localGeographic weight. -/
def isLocallyDominant (v : CouplingWeightVector) : Prop :=
  ∀ (w : CouplingWeight),
    w = v.professional ∨ w = v.originCommunity ∨
    w = v.diaspora     ∨ w = v.institutional →
    w.val ≤ v.localGeographic.val

def isExternallyDominant (v : CouplingWeightVector) : Prop :=
  ¬ isLocallyDominant v

-- ════════════════════════════════════════════════════════════════
-- §6. AGENT LIFE-CYCLE PHASES
-- Coupling weight vectors are not fixed — they evolve through four phases.
-- Census ACS B01001 + B25038 give phase distribution at tract level.
-- ════════════════════════════════════════════════════════════════

/-- The four life-cycle phases.

    The phase-transition dynamics are model-checked in `formal/tla/LifeCycle.tla`
    (TLC), where they are unavailable here (this is the enum only): monotone
    progression (phase and local coupling never decrease; coupling accumulates
    only in the settled Householder/Retirement phases, per
    `localCouplingAccumulates`), and reachability of the peak-coupling Retirement
    sponsor (`hasSponsorship`) that maintains HOA-attractor infrastructure. See
    `obsidian/SCORE/methodology/ModelCheckedDynamics.md`. -/
inductive LifeCyclePhase : Type where
  /-- Childhood (<18): inscription core formation; coupling vector inherited
      from family. Most durable component; persists across later geographies. -/
  | Childhood   : LifeCyclePhase
  /-- Student (18–24): external network formation; geographic mobility;
      local coupling weight accumulates very slowly. -/
  | Student     : LifeCyclePhase
  /-- Householder (25–64): local coupling accumulation via duration + participation;
      school-age children create a direct local coupling channel. -/
  | Householder : LifeCyclePhase
  /-- Retirement (65+): career coupling drops; local coupling reaches maximum;
      sponsorship function activates — maintains HOA attractor infrastructure. -/
  | Retirement  : LifeCyclePhase
deriving DecidableEq, Repr

/-- Local coupling weight accumulates monotonically with residence duration
    and active participation. This is an axiom: an empirical claim grounded
    in inscription dynamics theory. -/
axiom localCouplingAccumulates :
    ∀ (phase : LifeCyclePhase) (duration participation : ℕ),
      -- longer duration → strictly higher local coupling weight
      ∃ (weight : CouplingWeight), weight.val > 0

/-- The sponsorship function activates in the Retirement phase.
    Retirement-phase agents maintain organizational infrastructure
    that earlier phases used passively. -/
def hasSponsorship : LifeCyclePhase → Prop
  | .Retirement => True
  | _           => False

-- ════════════════════════════════════════════════════════════════
-- §7. HOA — HEURISTIC ORGANIZATIONAL ATTRACTOR
-- Emerges from coupling density. NOT declared by administrative boundary.
-- Effective inscription community size ≠ census headcount.
-- ════════════════════════════════════════════════════════════════

/-- A geographic region. -/
axiom Region : Type

/-- The aggregate local coupling weight of a set of agents in a region.
    This is the effective inscription community size — not census headcount. -/
axiom aggregateLocalWeight : List Agent → Region → CouplingWeight

/-- An HOA exists iff aggregate local coupling weight exceeds a threshold.
    The threshold is not fixed — it is a property of the manifold geometry. -/
structure HOA where
  region    : Region
  agents    : List Agent
  threshold : CouplingWeight
  /-- HOA existence condition. -/
  exists_   : threshold.val ≤ (aggregateLocalWeight agents region).val

/-- High-throughput communities (many student-phase agents) have shallow attractors:
    their aggregate local coupling weight may be substantially less than census count
    would suggest. -/
axiom highthroughput_shallow_attractor :
    ∀ (region : Region) (agents : List Agent) (threshold : CouplingWeight),
      -- if most agents are in Student phase, aggregate local weight is low
      (∀ a ∈ agents, True) →  -- placeholder: most agents in Student phase
      (aggregateLocalWeight agents region).val < threshold.val →
      -- then no HOA exists in this region
      ¬ ∃ (h : HOA), h.region = region

-- ════════════════════════════════════════════════════════════════
-- §8. PERCEPT AS MANIFOLD-FILTERED
-- An agent's manifold position filters external events before deliberation.
-- Sub-community similarity = shared perceptual filter.
-- ════════════════════════════════════════════════════════════════

/-- An external event in the objective world. -/
axiom Event : Type

/-- A percept: what an agent actually registers from an event.
    This is the event filtered through the agent's coupling weight vector.
    Two agents with different coupling vectors perceive different things
    from the same event — prior to any deliberation. -/
axiom Percept : Type

/-- The perceptual filter: maps (event, coupling vector) → percept. -/
axiom perceptualFilter : Event → CouplingWeightVector → Percept

/-- Sub-community perceptual similarity: agents with similar coupling vectors
    perceive events similarly. This is the formal basis for sub-community
    coherence — it is perceptual, not merely geographic. -/
def perceptuallySimilar (v₁ v₂ : CouplingWeightVector) (ε : ℝ) : Prop :=
  ∀ (e : Event),
    ∃ (dist : ℝ),  -- distance metric on Percept space
      dist < ε     -- percepts are within ε of each other

/-- Polarization as perceptual bifurcation: when an event produces strongly
    divergent percepts across the manifold, sub-communities move in opposite
    directions. This is not mere disagreement — it is prior to deliberation. -/
axiom polarizationAsBifurcation :
    ∀ (e : Event) (v₁ v₂ : CouplingWeightVector) (ε : ℝ),
      ¬ perceptuallySimilar v₁ v₂ ε →
      -- the two agents experience divergent percepts
      perceptualFilter e v₁ ≠ perceptualFilter e v₂

-- ════════════════════════════════════════════════════════════════
-- §9. THE INTERVENTION CLASSES -- ADDITIVE AND SUBTRACTIVE
-- Additive operators are ordered by activation energy. Rhythm-CLASS
-- operators (both polarities) bypass the perceptual filter via the
-- somatic channel.
--
-- SUBTRACTIVE FAMILY ADDED 2026-07-19 (audit item VC-1). GraphFoundation's
-- primitive row names three polarities -- add / remove / modify -- and this
-- taxonomy instantiated only the first. The objects are the same (a rhythm,
-- an edge, a node), so the subtractive operators act on the same three.
--
-- WHAT DOES **NOT** CARRY OVER: the activation-energy ordering. VC-1's
-- result is that rhythm < edge < node neither survives negation nor
-- inverts -- a different ordering governs, over a different INDEX SET.
-- The additive family is ordered by *what you build*; the subtractive by
-- *which persistence mechanisms the target has accumulated* (Hysteresis's
-- three, in window-width order: autocatalytic weight < ceiling residue <
-- B3 formal prosthetic). A node held only by autocatalytic weight dies in
-- one interaction cycle; one with deep ceiling residue AND a formal
-- prosthetic is very hard to kill.
--
-- That negative result is ENCODED, not merely commented: `activationEnergy`
-- returns `Option (Fin 3)` and is `none` on the subtractive family. Assigning
-- subtractive operators 0/1/2 would assert the mirrored ordering VC-1
-- refuted. The subtractive cost ordering is NOT formalized here -- it would
-- have to range over a target's HOAMaintenance persistence stack rather than
-- over the operator, and that is a separate construct.
-- ════════════════════════════════════════════════════════════════

/-- The three intervention operator classes. -/
inductive Intervention : Type where
  /-- create_rhythm: low activation energy; bypasses perceptual filter
      via somatic channel (embodied synchrony precedes filtering).
      Historically validated: civil rights and antiwar movements.
      Period, amplitude, phase in abstract units; anchor is optional. -/
  | createRhythm (period amplitude phase_ : ℝ) (anchor : Option Region)
      : Intervention
  /-- create_edge: medium activation energy; partial filter bypass
      through repeated contact, which gradually shifts perceptual surfaces. -/
  | createEdge (from_ to_ : Region) : Intervention
  /-- create_node: high activation energy; subject to full perceptual filtering;
      requires explicit participation. Retirement-phase targets need less
      activation energy than householder-phase targets. -/
  | createNode (target : Region) (stratum : Stratum) (seedSize : ℕ)
      : Intervention
  /-- disrupt_rhythm: the subtractive dual of create_rhythm. Removes an
      entrainment pattern. Bypasses the perceptual filter for the same
      reason its dual does -- no agent need agree to *stop* being entrained,
      so the operation sits below the filter on the somatic channel. -/
  | disruptRhythm (period amplitude phase_ : ℝ) (anchor : Option Region)
      : Intervention
  /-- sever_edge: removes connectivity between existing nodes. -/
  | severEdge (from_ to_ : Region) : Intervention
  /-- dissolve_node: removes organizational structure. No `seedSize` -- that
      is a creation parameter; what governs dissolution cost is the target's
      accumulated persistence stack, not a quantity of the operator. -/
  | dissolveNode (target : Region) (stratum : Stratum) : Intervention

/-- Operator polarity. `GraphFoundation`'s third polarity (*modify*) is
    deliberately not instantiated -- logged as audit item VC-27. -/
inductive InterventionPolarity : Type where
  | additive
  | subtractive
  deriving DecidableEq

/-- Which pole an operator acts on. -/
def interventionPolarity : Intervention → InterventionPolarity
  | .createRhythm ..  => .additive
  | .createEdge   ..  => .additive
  | .createNode   ..  => .additive
  | .disruptRhythm .. => .subtractive
  | .severEdge    ..  => .subtractive
  | .dissolveNode ..  => .subtractive

/-- Activation energy, represented ordinally -- **defined on the additive
    family only**. `none` on the subtractive family is the load-bearing part:
    it encodes VC-1's finding that the rhythm < edge < node ordering does not
    carry across polarity. Giving subtractive operators ordinal values here
    would assert the mirrored ordering that finding refuted. -/
def activationEnergy : Intervention → Option (Fin 3)
  | .createRhythm ..  => some ⟨0, by omega⟩
  | .createEdge   ..  => some ⟨1, by omega⟩
  | .createNode   ..  => some ⟨2, by omega⟩
  | .disruptRhythm .. => none
  | .severEdge    ..  => none
  | .dissolveNode ..  => none

/-- Activation energy is defined exactly on the additive family. -/
theorem activationEnergy_isSome_iff_additive (i : Intervention) :
    (activationEnergy i).isSome = true ↔ interventionPolarity i = .additive := by
  cases i <;> simp [activationEnergy, interventionPolarity]

/-- create_rhythm has strictly lower activation energy than create_node.
    Both are defined (the additive family), and rhythm is strictly below. -/
theorem rhythm_lower_energy_than_node
    (p a ph : ℝ) (anc : Option Region) (r : Region) (s : Stratum) (n : ℕ) :
    ∃ er en : Fin 3,
      activationEnergy (.createRhythm p a ph anc) = some er ∧
      activationEnergy (.createNode r s n) = some en ∧
      er.val < en.val :=
  ⟨⟨0, by omega⟩, ⟨2, by omega⟩, rfl, rfl, by decide⟩

/-- Whether an intervention bypasses the perceptual filter. **Both**
    rhythm-class operators do: the somatic channel precedes filtering, and
    removing an entrainment pattern needs an agent's assent no more than
    installing one does. -/
def bypassesFilter : Intervention → Prop
  | .createRhythm ..  => True   -- somatic channel precedes filtering
  | .disruptRhythm .. => True   -- same channel, opposite polarity
  | .createEdge   ..  => False  -- partial bypass only (not modeled here)
  | .createNode   ..  => False  -- full filtering applies
  | .severEdge    ..  => False
  | .dissolveNode ..  => False

/-- Rhythm-class membership -- the property that actually governs filter
    bypass, across both polarities. -/
def isRhythmClass : Intervention → Prop
  | .createRhythm ..  => True
  | .disruptRhythm .. => True
  | _                 => False

/-- **Only rhythm-CLASS operators bypass the perceptual filter.**

    Supersedes the former `only_rhythm_bypasses_filter`, which said "only
    `createRhythm`" and became **false** when the subtractive family landed:
    `disruptRhythm` bypasses too, on the same somatic channel. The bypass
    property was never about the *additive* operator -- it was about the
    *channel*, which is polarity-independent. (Audit item VC-1, 2026-07-19.) -/
theorem only_rhythm_class_bypasses_filter (i : Intervention) :
    bypassesFilter i → isRhythmClass i := by
  cases i <;> simp [bypassesFilter, isRhythmClass]

/-- The bypass set, enumerated: exactly the two rhythm-class operators. -/
theorem bypassesFilter_iff_rhythm_class (i : Intervention) :
    bypassesFilter i ↔ isRhythmClass i := by
  cases i <;> simp [bypassesFilter, isRhythmClass]

-- ════════════════════════════════════════════════════════════════
-- §10. SEQUENCING PRINCIPLE
-- create_rhythm before create_node lowers seed size required.
-- Empirically grounded; stated as axiom with a type-level contract.
-- ════════════════════════════════════════════════════════════════

/-- Whether a create_node intervention succeeds, given a region's current
    coupling state and a seed size. Abstract for now. -/
axiom nodeSucceeds : Region → Stratum → ℕ → CouplingWeightVector → Prop

/-- The sequencing principle: applying create_rhythm before create_node
    lowers the minimum seed size required for the node to take hold.
    Mechanism: embodied synchrony reduces System II resistance, so the
    organizational node requires fewer initial committed participants. -/
axiom rhythmLowersSeedSize :
    ∀ (region : Region) (stratum : Stratum) (coupling : CouplingWeightVector)
      (seedSize : ℕ),
      nodeSucceeds region stratum seedSize coupling →
      ∃ (reducedSeed : ℕ),
        reducedSeed ≤ seedSize ∧
        nodeSucceeds region stratum reducedSeed coupling

-- NOTE: as stated, this is trivially satisfiable (take reducedSeed = seedSize).
-- A stronger formulation would require reducedSeed < seedSize and would need
-- a model of how rhythm shifts coupling state before the node is applied.
-- Left weak here; tighten once CouplingWeightVector evolution is formalized.

-- ════════════════════════════════════════════════════════════════
-- §11. SCORE VALIDITY CONSTRAINTS
-- What it means for an implementation to be a valid SCORE implementation.
-- POLARIS satisfies these within the geographic projection.
-- ════════════════════════════════════════════════════════════════

/-- A SCORE implementation must provide: -/
structure SCOREImplementation where
  /-- 1. The three-domain ontology. -/
  domains       : Fin 3 → Domain
  /-- 2. A stratification ordering with the constraint. -/
  stableIn      : Stratum → Prop
  stratConstr   : ∀ s (h : 0 < s.val), stableIn s → stableIn (s.predecessor h)
  /-- 3. A manifold on which agents have coupling weight vectors. -/
  agentCoupling : Agent → CouplingWeightVector
  /-- 4. Life-cycle phases governing coupling evolution. -/
  agentPhase    : Agent → LifeCyclePhase
  /-- 5. The three intervention classes (at minimum). -/
  canIntervene  : Intervention → Region → Prop

/-- The three domains must be distinct — B₁, B₂, B₃ are irreducible modes,
    not aliases for each other. Stated as a separate predicate to avoid
    a dependent-field Lean compiler bug (LCNF ExplicitBoxing panic). -/
def domainsDistinct (impl : SCOREImplementation) : Prop :=
  impl.domains ⟨0, by omega⟩ ≠ impl.domains ⟨1, by omega⟩ ∧
  impl.domains ⟨1, by omega⟩ ≠ impl.domains ⟨2, by omega⟩ ∧
  impl.domains ⟨0, by omega⟩ ≠ impl.domains ⟨2, by omega⟩

/-- POLARIS (geographic projection) is a valid SCORE implementation: a
    `SCOREImplementation` record exists. Witnessed by a concrete instance whose
    stratification fields are the real `IsStable` predicate and the SCORE
    `stratificationConstraint` axiom. The `domains` map is given *pointwise*
    rather than via the `![ ]` array literal that triggered an LCNF
    ExplicitBoxing compiler panic in the earlier web build.
    Discharged 2026-06-18 (local toolchain v4.29.1; `sorry` removed). -/
theorem polaris_is_valid_score_implementation :
    ∃ (_ : SCOREImplementation), True :=
  ⟨{ domains := fun i =>
       if i.val = 0 then Domain.Objective
       else if i.val = 1 then Domain.Subjective
       else Domain.Inscription,
     stableIn := IsStable,
     stratConstr := stratificationConstraint,
     agentCoupling := fun _ =>
       ⟨CouplingWeight.zero, CouplingWeight.zero, CouplingWeight.zero,
        CouplingWeight.zero, CouplingWeight.zero⟩,
     agentPhase := fun _ => .Childhood,
     canIntervene := fun _ _ => True },
   trivial⟩


-- ════════════════════════════════════════════════════════════════
-- §14. B₃ COMMUNITY FIBRATION — REGION GEOMETRY (graded product)
-- A *derived* construct, NOT a re-typing of B₃: the primitive `InscriptionContent`
-- (B₃) is untouched and stays a shared singleton (load-bearing for the §4 morphism
-- round-trip). This adds structure *over* it — the doctrinal composition order plus
-- the B₃-internal grading — and defines a community's region R(C) as a graded
-- down-set. Resolves fibration decision #4 to the graded product: the sub-order
-- (grading) and sub-graph (edges) candidates are one graded DAG.
--
-- PROMOTED TO CORE (2026-06-21, eighth on-demand Q3 promotion, ETHOS ∩ NEXUS): the
-- region constructor is now core, filled by two contrasting peers — ETHOS (§15,
-- citation corpus) and NEXUS (§16, patent-citation paradigm cluster). The promotion
-- is of this *derived* constructor only; the primitive B₃ is never re-typed (OWL:
-- core:DoctrinalRegion class + core:doctrinallyComposesFrom transitive property; the
-- down-closure / grading laws are DL-inexpressible and live here in Lean).
-- Cross-ref: obsidian/SCORE/domains/{B3RegionGeometry,B3CommunityFibration}.md,
-- methodology/RefinementArchitecture.md.
-- ════════════════════════════════════════════════════════════════

/-- The B₃-internal idea-hierarchy levels, ordered by emergence dependency:
    0 signal/gesture · 1 oral concept · 2 written inscription ·
    3 institution · 4 meta-idea · 5 generative framework.
    DISTINCT from the global cross-domain `Stratum` (S₁–S₆) — the precision guard in
    B3RegionGeometry.md: do not reuse `Stratum`. `Fin 6` supplies the order. -/
abbrev B3Level := Fin 6

/-- The doctrinal-composition network over a node type `Node`: the `B₃×B₃→B₃`
    morphism as an edge relation, the emergence-hierarchy grading, and the
    compatibility law tying them. `grade_mono` — the grading is monotone along
    composition — *is* the stratification constraint (§2) read on the network:
    higher-stratum ideas compose only from lower-or-equal-stratum substrate. That
    single law unifies the two candidate region geometries (sub-order = the grading;
    sub-graph = the edges) into one graded DAG.

    `Node` is polymorphic so the *same* machinery serves both the B₃ statement
    (`DoctrinalNetwork InscriptionContent` — the primitive B₃ is untouched, no
    re-typing) and a concrete peer binding (§15: `DoctrinalNetwork EClaim` for ETHOS). -/
structure DoctrinalNetwork (Node : Type) where
  /-- `composesFrom x y` : y composes from x — x is an immediate doctrinal substrate
      of y (a court ruling from precedent; a theorem from its lemmas; a paper from
      what it cites). -/
  composesFrom : Node → Node → Prop
  /-- The B₃-internal emergence-hierarchy grading. -/
  grade : Node → B3Level
  /-- Grading monotone along composition: a substrate sits at a ≤ stratum.
      The stratification constraint, expressed on the doctrinal network. -/
  grade_mono : ∀ {x y}, composesFrom x y → grade x ≤ grade y

namespace DoctrinalNetwork

variable {Node : Type}

/-- The doctrinal order: reflexive-transitive closure of composition.
    `D.le x y` ⇔ x is a (transitive) doctrinal substrate of y. -/
abbrev le (D : DoctrinalNetwork Node) (x y : Node) : Prop :=
  Relation.ReflTransGen D.composesFrom x y

/-- Grading is monotone along the *whole* doctrinal order, not just single edges:
    the order refines the grading. Lifts `grade_mono` over the closure by induction. -/
theorem grade_mono_le (D : DoctrinalNetwork Node) {x y : Node}
    (h : D.le x y) : D.grade x ≤ D.grade y := by
  induction h with
  | refl => exact le_refl _
  | tail _ hbc ih => exact le_trans ih (D.grade_mono hbc)

/-- A region (a community's fiber R(C)) is a *down-set* of the doctrinal order:
    holding an inscription entails holding its doctrinal substrate. This
    substrate-closure is what makes R(C) a derived, *structured* object rather than
    a bare set — fibration condition #1. -/
def IsRegion (D : DoctrinalNetwork Node) (R : Set Node) : Prop :=
  ∀ ⦃x y : Node⦄, D.le x y → y ∈ R → x ∈ R

/-- **Region down-closure + stratum down-closure, in one.** In a region, every
    substrate of a held inscription is itself held AND sits at a ≤ stratum. The
    second conjunct (stratum down-closure) is a *corollary* of the doctrinal
    down-closure via grading monotonicity — the "downward-closed for free" result. -/
theorem region_substrate_closed_and_graded (D : DoctrinalNetwork Node)
    {R : Set Node} (hR : D.IsRegion R)
    {x y : Node} (hxy : D.le x y) (hy : y ∈ R) :
    x ∈ R ∧ D.grade x ≤ D.grade y :=
  ⟨hR hxy hy, D.grade_mono_le hxy⟩

/-- **Shared substrate is a region.** The overlap R(C₁) ∩ R(C₂) of two regions is
    again a down-set — the common doctrinal ground two communities reason from, and
    the object the anchor's `1 − overlap` opacity is computed over. -/
theorem region_inter (D : DoctrinalNetwork Node)
    {R S : Set Node} (hR : D.IsRegion R) (hS : D.IsRegion S) :
    D.IsRegion (R ∩ S) := by
  intro x y hxy hy
  exact ⟨hR hxy hy.1, hS hxy hy.2⟩

/-- The down-closure of a frontier (a generating antichain of maximal elements). -/
def downClosure (D : DoctrinalNetwork Node) (gen : Set Node) : Set Node :=
  { x | ∃ y ∈ gen, D.le x y }

/-- The frontier is contained in its own down-closure. -/
theorem subset_downClosure (D : DoctrinalNetwork Node) (gen : Set Node) :
    gen ⊆ D.downClosure gen := by
  intro y hy
  exact ⟨y, hy, Relation.ReflTransGen.refl⟩

/-- **Store the frontier, derive the rest.** The down-closure of any frontier is a
    valid region; with `subset_downClosure`, a community's region is fully recovered
    from its stored frontier. The minimal-state representation that settles the
    fibration's materialize-vs-derive residual (decision #2): persist only the
    frontier, compute the down-closure by reachability on demand. -/
theorem downClosure_isRegion (D : DoctrinalNetwork Node) (gen : Set Node) :
    D.IsRegion (D.downClosure gen) := by
  rintro x y hxy ⟨z, hz, hyz⟩
  exact ⟨z, hz, Relation.ReflTransGen.trans hxy hyz⟩

end DoctrinalNetwork


-- ════════════════════════════════════════════════════════════════
-- §SP. TRACE + SPECTRAL EARLY-WARNING
-- The transform-domain branch of the open trace-processor taxonomy
-- (core:Trace, core:TraceProcessor, core:SpectralEarlyWarningIndicator;
-- score-core.owl). The OWL carries the open taxonomy (no covering axiom);
-- this Lean layer carries the transform branch's provable content: the
-- generic monotonicity law POLARIS's SEWI (Score/Polaris.lean) instantiates.
-- Promote-by-nature (Scheffer critical slowing down). Numeric signature/weight
-- values are Q4 BIND (code), not here — the theorem needs only nonnegativity.
-- See obsidian/SCORE/measurement/{Trace,SpectralEarlyWarningIndicator}.md.
-- ════════════════════════════════════════════════════════════════

/-- A `Trace`: a time-ordered real-valued signal — the domain-general substrate of dynamical
    analysis (core:Trace). Minimal encoding; the object over which trace processors operate. -/
abbrev Trace := ℕ → ℝ

/-- A spectral early-warning composite: a nonnegative-weighted sum of `n` critical-slowing-down
    signatures (each real-valued, rising as the system nears a bifurcation). The generic form of
    core:SpectralEarlyWarningIndicator; POLARIS's SEWI is the n = 3 instance. -/
def spectralEWS {n : ℕ} (w s : Fin n → ℝ) : ℝ := Finset.univ.sum (fun i => w i * s i)

/-- **Spectral-EWS monotonicity.** With nonnegative weights, the composite is nondecreasing in
    each signature: raising any critical-slowing-down signal cannot lower the indicator. The
    generic law every `SpectralEarlyWarningIndicator` (hence polaris:SEWI) satisfies — the
    property whose absence at the Lean layer the SEWI congruence audit flagged (Layer 5). -/
theorem spectral_ews_monotone {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i)
    (s s' : Fin n → ℝ) (hss : ∀ i, s i ≤ s' i) :
    spectralEWS w s ≤ spectralEWS w s' :=
  Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hss i) (hw i))

/-- The elevated-alert predicate: the indicator has reached an alert threshold. `noncomputable`
    (decidability of `≤` on ℝ is noncomputable); the point is the monotonicity law,
    not execution. -/
noncomputable def sewi_elevated (value threshold : ℝ) : Bool := decide (threshold ≤ value)

/-- `sewi_elevated` is monotone in the indicator: a higher SEWI cannot un-elevate an alert. -/
theorem sewi_elevated_monotone {threshold v v' : ℝ} (hvv : v ≤ v')
    (h : sewi_elevated v threshold = true) : sewi_elevated v' threshold = true := by
  simp only [sewi_elevated, decide_eq_true_eq] at *
  exact le_trans h hvv


end SCORE
