import Formal.Score.CouplingKernel

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

/-- The three domains are pairwise disjoint — the Lean counterpart of
    `B1_Objective ⊔ B2_Subjective ⊔ B3_Inscription` all-disjoint in `score-core.owl`,
    and the first of the five category errors the `score-theory` skill exists to
    prevent ("the three domains are not a pipeline"; they are irreducible modes).

    Recorded 2026-09-12. The fact was always there — constructor distinctness is free in
    Lean — but nothing *stated* it, so `scripts/owl_lean_check.py` reported the axiom as
    the largest uncovered gap in the ontology while this inductive sat three lines above.
    The mismatch was only ever one of spelling: OWL says `B1_Objective`, Lean says
    `Domain.Objective`, and the `-- B₁:` comments that bridge them are stripped before
    matching.

    Stated for the same reason as `Sigma.actorType_trichotomy_disjoint`: an obligation
    discharged only by construction is invisible to a coverage check, and an invisible
    discharge is indistinguishable from an absent one. -/
theorem domain_trichotomy_disjoint :
    Domain.Objective ≠ Domain.Subjective ∧
    Domain.Objective ≠ Domain.Inscription ∧
    Domain.Subjective ≠ Domain.Inscription := by
  decide

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

/-- Stability of a stratum: it can sustain emergence above it. 
    **axiom-kind:** definitional -/
axiom IsStable : Stratum → Prop

/-- The stratification constraint, enforced by Natural Selection.
    A stratum is stable only if its immediate predecessor is also stable.
    NS selects against configurations requiring unstable substrates —
    they fail before they can reproduce. 
    **axiom-kind:** empirical
    **anchor:** vault:SO-NS-Stratification -/
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

/-- An agent in the socio-technical system. 
    **axiom-kind:** carrier -/
axiom Agent : Type

/-- The objective world state (B₁). 
    **axiom-kind:** carrier -/
axiom World : Type

/-- Inter-subjective inscription content (B₃): constitutions, norms, media. 
    **axiom-kind:** carrier -/
axiom InscriptionContent : Type

/-- An agent's full cognitive state (B₂): manifold position, coupling weights,
    Path A/B dynamics. 
    **axiom-kind:** carrier -/
axiom CognitiveState : Type

/-- A Σ-actor **carrier**: the opaque Constituent-level identity of a higher-order
    collective actor (institution, discipline, alliance, polity) with a co-inscribed
    formal B₃ membrane, sufficient reflexive depth, a telos-bearing inscription
    output, and a maintaining human community. Disjoint from A-actors (`Agent`) and
    Ω-actors. Peer refinements (`ethos:EpistemicInstitution`,
    `agora:ConstitutionalSigmaActor`, `atlas:DeterrenceCoalition`, ...) instantiate
    this axiom, and `Constituent.SigmaAgent` / §HM's `HOAState` populations range
    over it.

    Added 2026-07-14 as the M1 gap-close from the HM Specialization Audit
    (`governance/SCORE_HM_Specialization_Matrix.md` §HM development-gaps): the §HM
    spine needed a Σ-actor type it could use as an opaque HOA constituent.

    **Correction 2026-07-24.** M1's original doc-comment here claimed "Σ-actor had
    no Lean-level counterpart." That was false: `Score/Sigma.lean` already carried a
    rich `structure SigmaActor` (formation event, telos, life-cycle, coupling). What
    was actually missing was an *opaque carrier* usable by the spine as an HOA
    constituent — this axiom. Because `Sigma.lean` was not in the build then, adding this
    axiom silently collided with that structure (both `SCORE.SigmaActor`) and left
    `Sigma.lean` non-compiling until the 2026-07-24 rename-and-bridge: that structure
    is now `SCORE.SigmaActorArchitecture` (the architecture-view), this axiom is the
    carrier-view, and `SigmaActorArchitecture.carrier` bridges them — both Lean views
    of the one OWL class `core:SigmaActor`. See the §HM MultiStratum plan §9.6. 
    **axiom-kind:** carrier -/
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

-- Perception (B₁ → B₂) is DEFINED in § 8 (`perceive`): an event, filtered by the agent's
-- manifold, updates its cognitive state, with a somatic route that bypasses the filter. It
-- lives there because it reads an `Event` (§ 4d). The opaque
-- `perception : World → Agent → CognitiveState` it replaces was deleted 2026-10-18
-- (supersession rule): it read a snapshot, had no consumer, and claimed a filtering its type
-- did not carry.

/-- Action (B₂ → B₁): agent behavior modifies the objective world. 
    **axiom-kind:** definitional -/
axiom action : Agent → CognitiveState → World → World

/-- Inscription (B₂ → B₃): cognitive content becomes inter-subjective.
    Referent-agnostic general form; refined by referent below. 
    **axiom-kind:** definitional -/
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
    reflexive-depth layer is not yet encoded (see agents/ReflexiveDepth.md). 
    **axiom-kind:** definitional -/
axiom SufficientDepth : Agent → Prop

/-- B₁-referential inscription: content about world-states (alarm, trail, record).
    The B₃ floor; no depth precondition. 
    **axiom-kind:** definitional -/
axiom inscribeB1Ref : Agent → CognitiveState → InscriptionContent

/-- B₂-referential inscription: content about the agent's own B₂-manifold features with
    no B₁ referent (beliefs, self-model, fictions). The depth precondition is an explicit
    argument — without `SufficientDepth a` the term does not typecheck. 
    **axiom-kind:** definitional -/
axiom inscribeB2Ref : (a : Agent) → SufficientDepth a → CognitiveState → InscriptionContent

/-- The depth gate is load-bearing: B₂-referential inscription is well-typed only in a
    context that supplies `SufficientDepth a`. (Drop `h` and this fails to elaborate.)
    `noncomputable`: the point is type-level elaboration, and `inscribeB2Ref` is an
    `axiom` (no executable body), so it must not be sent to the code generator. -/
noncomputable example (a : Agent) (h : SufficientDepth a) (cs : CognitiveState) :
    InscriptionContent :=
  inscribeB2Ref a h cs

-- Incorporation (B₃ → B₂) is DEFINED in § 8 (`incorporate`), through the same manifold
-- filter as perception, with the Path A / Path B asymmetry in the update. The opaque
-- `incorporate : InscriptionContent → Agent → CognitiveState` it replaces was deleted
-- 2026-10-18 (supersession rule): it took no prior cognitive state, so it could not express
-- that what an inscription does depends on the manifold it lands on.

/-- The five OWL `Morphism` subclasses, as a disjoint sum — the Lean counterpart of
    `Action ⊔ Incorporation ⊔ Inscription ⊔ Perception ⊔ Transformation` all-disjoint in
    `score-core.owl`.

    **NOT the morphism space.** This mirrors an OWL *grouping*, and that grouping is not a
    principled closure. The full space (`MorphismCompleteness`) is six directed SIMPLE
    morphisms plus a product class, and this type omits four of its members:

    | outside this type | why |
    |---|---|
    | B₃→B₁ | simple, non-B₂-incident. Established — software automation, predates AI |
    | B₁→B₃ | simple, non-B₂-incident. Open, and possibly structurally unavailable |
    | Schema application `B₁×B₃→B₃` | product; not an OWL class at all |
    | Co-inscription `B₂×B₂→B₃` | product; OWL carries `CoInscriptionEvent` as an Event, not a Morphism subclass |

    The name was `MorphismKind` for about an hour on 2026-09-12 and that overclaimed: a
    reader would take it for the exhaustive tag type. Renamed the same day, after the
    vault was found flattening the same distinction at `obsidian/SCORE.md`.

    **The principled subset is four, not five.** `B2Incidence` is exact: "of the six
    directed simple morphisms, exactly four are B₂-incident", and those four are what
    SCORE calls *primary* — an exhaustive enumeration, not a chosen emphasis.
    Transformation joins them here because the OWL groups it in, being the first product
    morphism; it is B₂-incident too, but it is not simple, so "five B₂-incident
    morphisms" would be wrong in the other direction (co-inscription is also B₂-incident
    and is not here).

    **This is a tag, not a pipeline.** The morphisms run simultaneously and in multiple
    directions; enumerating them as constructors says they are mutually exclusive *as
    classifications of a coupling*, and nothing about order. Do not read the constructor
    order as a sequence — that is the first of the five category errors the
    `score-theory` skill exists to prevent. -/
inductive MorphismClass : Type where
  /-- B₁ → B₂, filtered by manifold position. -/
  | perception     : MorphismClass
  /-- B₂ → B₁, behaviour modifying the objective world. -/
  | action         : MorphismClass
  /-- B₂ → B₃, cognitive content becoming inter-subjective. -/
  | inscription    : MorphismClass
  /-- B₃ → B₂, inscribed content entering cognition (Path A or Path B). -/
  | incorporation  : MorphismClass
  /-- B₂ × B₃ → B₃, the product morphism — the fifth, and not a simple one. -/
  | transformation : MorphismClass
deriving DecidableEq, Repr

/-- The five OWL `Morphism` subclasses are pairwise distinct. Free from the inductive;
    stated so a
    coverage check can see the OWL axiom discharged, per `domain_trichotomy_disjoint`. -/
theorem morphismClass_pairwise_distinct :
    MorphismClass.perception ≠ MorphismClass.action ∧
    MorphismClass.inscription ≠ MorphismClass.incorporation ∧
    MorphismClass.transformation ≠ MorphismClass.perception := by
  decide

-- ════════════════════════════════════════════════════════════════
-- §4c. THE REFERENT AXIS — what an inscription is ABOUT
-- OWL: `B1ReferentialInscription` disjointWith `B2ReferentialInscription`, both
-- ⊑ Inscription. Added 2026-09-12 (A1).
--
-- `inscribeB1Ref` / `inscribeB2Ref` above type the MORPHISM by referent; nothing
-- typed the CONTENT, which is what the OWL disjointness is about. Orthogonal to
-- provenance (Sigma.lean §25): every inscription has a referent and a provenance,
-- and the two axes do not constrain each other.
-- ════════════════════════════════════════════════════════════════

/-- What an inscription's content is *about*. B₂-referential inscription requires
    sufficient reflexive depth and is the human differentia from which the higher B₃
    strata, Σ-actors and cultural evolution follow. -/
inductive Referent : Type where
  /-- About B₁ world-states — alarm calls, trails, records. The B₃ floor. -/
  | b1Referential : Referent
  /-- About features of the agent's own B₂ manifold with no B₁ referent — beliefs, the
      self-model, abstractions, shared fictions. -/
  | b2Referential : Referent
deriving DecidableEq, Repr

/-- The referent of a piece of content, if it has one of the two.

    `Option` for the same reason as `provenanceOf`: OWL declares the pair disjoint and
    asserts no covering axiom. A total `InscriptionContent → Referent` would add one.
    **axiom-kind:** definitional -/
axiom referentOf : InscriptionContent → Option Referent

/-- B₁-referential and B₂-referential content are disjoint. -/
theorem referent_axis_disjoint :
    ∀ (c : InscriptionContent),
      referentOf c = some Referent.b1Referential →
      referentOf c ≠ some Referent.b2Referential := by
  intro c h1 h2
  rw [h1] at h2
  simp at h2

-- ════════════════════════════════════════════════════════════════
-- §4d. B₁'S OWN DYNAMICS — the world changes with no agent in the loop
-- Vault: domains/B1-Objective.md ("SO and NS operate *within* B₁, mind-independently";
-- B₁ is "arguably their home domain"). Added 2026-10-18.
--
-- Until this section, `World` changed only through `action`: a world with no agents never
-- changed, and nothing could make a tree ring. That was a gap in model completeness, not a
-- commitment: the vault has always said B₁ has causal dynamics of its own.
--
-- **This is NOT a morphism.** Morphisms are cross-domain couplings, and core has no intra-B₁
-- morphism (`score-core.owl` `PureB1Cycle`; `MorphismCompleteness`). `b1Step` is causation
-- *within* a domain, a different kind of thing. It takes no `Agent`, so its independence of
-- B₂ holds by its type.
--
-- It is also what makes marks safe to define as *made by* a change (§ 4b): without it, every
-- change would be an agent's action, and "made by a change" would mean "made by an agent",
-- contradicting `mark_without_content` (natural patterned matter).
--
-- Deterministic (`World → World`) at this tier; stochastic B₁ would be a later refinement.
-- ════════════════════════════════════════════════════════════════

/-- **B₁'s own dynamics**: how the world changes in one step with no agent acting. Not a
    morphism (see the section header).
    **axiom-kind:** definitional -/
axiom b1Step : World → World

/-- **B₁ changes on its own.** Some world state is not fixed by B₁'s dynamics. A one-point
    world fails this (its only step is the identity).
    **axiom-kind:** empirical
    **anchor:** vault:B1-Objective -/
axiom b1_has_own_dynamics : ∃ w : World, b1Step w ≠ w

/-- **The two ways B₁ changes**: by its own dynamics, or by an agent's action. -/
def Transition (w w' : World) : Prop :=
  w' = b1Step w ∨ ∃ (a : Agent) (cs : CognitiveState), w' = action a cs w

/-- **An external event in the objective world: a real change of world state.** "B₁ events
    are occurrences on this manifold" (`Manifold.md`): a before, a distinct after, and a
    transition between them, natural or agent-made.

    *History.* An opaque carrier until 2026-10-18; then a pair of distinct states; the
    `transition` field was added the same day with § 4d, so that an event is something B₁
    can actually do, not an arbitrary pair. -/
structure Event where
  before : World
  after : World
  changes : before ≠ after
  transition : Transition before after

/-- An event occurs at the world state it changes: events are localized features of the one
    objective world, not a separate B₁. -/
def occursIn (e : Event) (w : World) : Prop := w = e.before

/-- **Events are localized in the world.** Every event occurs in some world state and not in
    every one. A theorem: the event's own `after` is a state where it does not occur. -/
theorem event_localized :
    ∀ e : Event, (∃ w : World, occursIn e w) ∧ (∃ w : World, ¬ occursIn e w) :=
  fun e => ⟨⟨e.before, rfl⟩, ⟨e.after, fun h => e.changes h.symm⟩⟩

/-- **A natural event exists**: a change of world state with no agent in it. The formal
    form of "B₁ has dynamics independent of any agent". -/
theorem natural_event_exists : ∃ e : Event, e.after = b1Step e.before := by
  obtain ⟨w, hw⟩ := b1_has_own_dynamics
  exact ⟨⟨w, b1Step w, fun h => hw h.symm, Or.inl rfl⟩, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- §4b. B₁ REALIZATION OF INSCRIPTION — realization WITHOUT reduction
-- OWL: `B3_Inscription ⊑ carriedBy some B1_Objective` (score-core.owl).
-- Vault: domains/B3-Inscription.md § "The B₁ realization of inscription".
--
-- Added 2026-09-12. `scripts/owl_lean_check.py` reported this restriction as having
-- no Lean counterpart, and it is the largest gap that check found: it encodes the
-- second of the five category errors the `score-theory` skill exists to prevent ---
-- "B₃ is neither free-floating nor reducible to its carrier."
--
-- The near-miss worth recording: Core.lean already contained several "carrier"
-- mentions, so a name-only search reports this covered. They are the *Σ-actor*
-- carrier (an opaque HOA-constituent identity, §3), an unrelated sense of the word.
--
-- THREE axioms, and all three are needed. Totality alone would license reading B₃ as
-- its mark; multiple realizability alone would leave B₃ free-floating. Encoding one
-- without the other commits the category error in the formalism itself.
-- ════════════════════════════════════════════════════════════════

/-- A **mark**: a particular physical change in B₁ — ink on paper, a pressure wave, a
    charge pattern, a tree ring. Distinct from `World` (a total B₁ state); a mark is a
    localized feature of world states, **made by an event**: absent before it, present after.
    The event may be natural (`b1Step`) or an agent's action (§ 4d), so natural patterned
    matter (`mark_without_content`) and authored marks are both covered.

    *History.* An opaque carrier until 2026-10-18, when § 4d gave B₁ its own dynamics and
    made this definition safe. `feature` is the persisting part: the mark is present in every
    world state where it holds, not only at the moment of making. -/
structure B1Mark where
  madeBy : Event
  feature : World → Prop
  present : feature madeBy.after
  absent : ¬ feature madeBy.before

/-- Token-level realization: content `c` is carried by mark `m`. A *relation*, not a
    function — a function `InscriptionContent → B1Mark` would assert each content has
    exactly one carrier, which is precisely the multiple realizability this section
    denies. 
    **axiom-kind:** definitional -/
axiom carriedBy : InscriptionContent → B1Mark → Prop

/-- **Totality.** "There is no B₃ token without a B₁ realization." This is the clause
    the OWL restriction states. 
    **axiom-kind:** empirical
    **anchor:** owl:carriedBy, vault:B3-Inscription -/
axiom inscription_carried : ∀ c : InscriptionContent, ∃ m : B1Mark, carriedBy c m

/-- **Multiple realizability** (type level). The Rosetta Stone's three scripts carry one
    decree; a poem exists in breath, ink, or bits. Invariance of the content across its
    carriers is the standing reason B₃ is irreducible. 
    **axiom-kind:** empirical
    **anchor:** vault:B3-Inscription -/
axiom carrier_multiply_realizable :
    ∃ (c : InscriptionContent) (m₁ m₂ : B1Mark),
      m₁ ≠ m₂ ∧ carriedBy c m₁ ∧ carriedBy c m₂

/-- **B₁ is necessary, not sufficient.** Some marks carry no content at all: mere
    patterned matter. What makes a mark a B₃ object is B₂ *provenance* — authored to
    bear recoverable content — not the physics of the mark. This is also what keeps
    `B₁→B₃` structurally unavailable (see `MorphismCompleteness`): B₁ alone cannot
    reach B₃. 
    **axiom-kind:** empirical
    **anchor:** vault:B3-Inscription -/
axiom mark_without_content : ∃ m : B1Mark, ∀ c : InscriptionContent, ¬ carriedBy c m

/-- **Realization without reduction.** B₃ does not collapse into its carrier: content
    cannot be identified with a unique mark, so "the inscription *is* the physical
    trace" is false. Derived from multiple realizability, not assumed. -/
theorem b3_not_reducible_to_carrier :
    ¬ (∀ (c : InscriptionContent) (m₁ m₂ : B1Mark),
         carriedBy c m₁ → carriedBy c m₂ → m₁ = m₂) := by
  intro h
  obtain ⟨c, m₁, m₂, hne, h₁, h₂⟩ := carrier_multiply_realizable
  exact hne (h c m₁ m₂ h₁ h₂)

/-- The two halves stated together: every content has a carrier (necessity), and not
    every mark carries content (insufficiency). The conjunction is what "realization,
    not reduction" amounts to at the token level. -/
theorem b1_necessary_not_sufficient :
    (∀ c : InscriptionContent, ∃ m : B1Mark, carriedBy c m)
    ∧ ¬ (∀ m : B1Mark, ∃ c : InscriptionContent, carriedBy c m) := by
  refine ⟨inscription_carried, ?_⟩
  intro h
  obtain ⟨m, hm⟩ := mark_without_content
  obtain ⟨c, hc⟩ := h m
  exact hm c hc

/-! ### Marks are features of the one world (2026-10-18)

`World`, `Event` and `B1Mark` were three B₁ carriers with no stated relation, so a model
could interpret them as three different worlds (`CoreModel` chose `Bool`, `Unit` and
`Fin 3` independently). The core's fourth category error says there is **one** B₁. Events
and marks are now both *defined* over `World` (§ 4d, § 4b): an event is a real transition,
and a mark is a feature made by one. So both localizations are theorems. An earlier version
of this section (#952) asserted `markIn` and `mark_localized` as axioms; § 4d's B₁ dynamics
retired both. Recorded as the residual of a withdrawn correction in
`reference/correction-ledger.md`. -/

/-- A mark is present in a world state where its feature holds. -/
def markIn (m : B1Mark) (w : World) : Prop := m.feature w

/-- **Marks are localized in the world.** Every mark is present in some world state (after
    the event that made it) and absent from another (before it). A theorem since 2026-10-18;
    it was an empirical axiom until § 4d gave B₁ its own dynamics. -/
theorem mark_localized :
    ∀ m : B1Mark, (∃ w : World, markIn m w) ∧ (∃ w : World, ¬ markIn m w) :=
  fun m => ⟨⟨m.madeBy.after, m.present⟩, ⟨m.madeBy.before, m.absent⟩⟩

/-- **Every inscription is realized in the one world**: each content has a carrier mark
    that is present in some world state. `inscription_carried` said every content has a
    mark; this says where the mark is. -/
theorem inscription_realized_in_world :
    ∀ c : InscriptionContent, ∃ (m : B1Mark) (w : World), carriedBy c m ∧ markIn m w := by
  intro c
  obtain ⟨m, hm⟩ := inscription_carried c
  obtain ⟨w, hw⟩ := (mark_localized m).1
  exact ⟨m, w, hm, hw⟩

/-- **The axioms force more than one world state**: B₁'s own dynamics moves some state
    (`b1_has_own_dynamics`). Stated so the non-triviality is a checked fact. -/
theorem world_nontrivial : ∃ w₁ w₂ : World, w₁ ≠ w₂ := by
  obtain ⟨w, hw⟩ := b1_has_own_dynamics
  exact ⟨w, b1Step w, fun h => hw h.symm⟩

-- `normativeChangeChain` moved to § 8 (2026-10-18): it uses the defined `incorporate`.

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
    the life-cycle phase ordering), and reachability of the peak-coupling Retirement
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

-- `localCouplingAccumulates` was DELETED 2026-07-26 (audit Appendix D.3).
--
-- It read:
--     ∀ (phase : LifeCyclePhase) (duration participation : ℕ),
--       ∃ (weight : CouplingWeight), weight.val > 0
--
-- None of the three bound variables occurs in the conclusion, so it asserted
-- only that *some* positive coupling weight exists -- true of any inhabited
-- CouplingWeight, and nothing to do with duration or participation. Its
-- docstring claimed monotonic accumulation, which the statement never said.
-- It was referenced nowhere.
--
-- Same defect as the former `perceptuallySimilar` (repaired in § 8). Deleted
-- rather than restated because restating it needs a real weight function
-- `localWeight : LifeCyclePhase → ℕ → ℕ → CouplingWeight` and a monotonicity
-- claim over it -- a modelling commitment, not a repair. The empirical content
-- lives in `obsidian/SCORE/agents/LifeCyclePhases.md` and is model-checked in
-- `formal/tla/` (see ModelCheckedDynamics.md); cite those, not this.

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

/-- A geographic region. 
    **axiom-kind:** carrier -/
axiom Region : Type

/-- The aggregate local coupling weight of a set of agents in a region: the
    effective inscription community size, as against census headcount.

    **Descriptive only.** This is *not* the HOA existence criterion — see the
    spectral condition on `HOA` below. A scalar cannot express criticality,
    because criticality is a property of the coupling kernel's *spectrum*: two
    regions with equal aggregate weight can lie on opposite sides of the phase
    transition. Retained because effective-vs-census community size is a live
    POLARIS measurement concern in its own right.

    **Validity domain, now formal (BJR proposal M4, 2026-07-31).** The scalar
    reads criticality correctly exactly on the homogeneous (rung-1 /
    Erdős–Rényi) slice, where `spectralNorm_plantedPartition_er_slice`
    (`CouplingKernel.lean` §CK6) proves the spectral statistic collapses to
    the mean-coupling scalar; off that slice the finite-type value is
    `spectralNorm_plantedPartition`'s Perron form, which mean density does not
    determine. The spectral successor is already wired in: `HOA.supercrit`
    below is the `Supercritical` predicate on the population's kernel. 
    **axiom-kind:** definitional -/
axiom aggregateLocalWeight : List Agent → Region → CouplingWeight

/-- **An HOA over a finite agent population.** Existence is *supercriticality of
    the population's coupling kernel* — `‖T_κ‖ > 1` — per Bollobás–Janson–Riordan
    applied to the inhomogeneous coupling graph.

    This replaces a scalar aggregate-weight threshold (superseded 2026-07-26).
    The scalar form was not merely under-specified but wrongly *typed*: it
    encoded the Erdős–Rényi criticality statistic (mean degree) for a graph
    whose edge rule — `overlap(B₂ᵢ,B₂ⱼ) ≥ link_threshold` — depends on node
    attributes and is therefore a kernel, not a constant edge probability. See
    `obsidian/SCORE/emergence/mechanism/CouplingKernel.md`. -/
structure HOA (Pop : Type) [Fintype Pop] [DecidableEq Pop] where
  region     : Region
  /-- Which agent each population index denotes. -/
  member     : Pop → Agent
  /-- The population's coupling kernel: `kernel i j` is the coupling propensity
      between `i` and `j`, a decreasing function of their B₂ manifold distance. -/
  kernel     : CouplingKernel Pop
  wellFormed : IsCouplingKernel kernel
  /-- HOA existence condition — spectral, not scalar. -/
  supercrit  : Supercritical kernel

/-- No HOA rests on a subcritical kernel. Formerly the conclusion of the
    `highthroughput_shallow_attractor` **axiom**; now a one-line consequence of
    the existence condition, because `Subcritical` and `Supercritical` are
    negations of one another. -/
theorem no_hoa_of_subcritical {Pop : Type} [Fintype Pop] [DecidableEq Pop]
    {κ : CouplingKernel Pop} (h : Subcritical κ) :
    ¬ ∃ hoa : HOA Pop, hoa.kernel = κ := by
  rintro ⟨hoa, rfl⟩
  exact absurd hoa.supercrit (not_lt.mpr h)

/-- **Empirical axiom.** A population dominated by Student-phase agents has a
    subcritical coupling kernel: high turnover prevents accumulation of the
    manifold overlap that supercriticality requires.

    Note the scoping. The superseded `highthroughput_shallow_attractor` axiom
    quantified `agents` and `threshold` *independently of the HOA it denied*, so
    instantiating `threshold := 1` proved that a single HOA anywhere in a region
    forces **every** agent list in that region to sit at maximal aggregate
    weight — an absurdity that was machine-checkable from the axiom as written.
    This replacement constrains only the population's own kernel. 
    **axiom-kind:** empirical
    **anchor:** vault:CouplingKernel -/
axiom studentDominated_subcritical {Pop : Type} [Fintype Pop] [DecidableEq Pop]
    (κ : CouplingKernel Pop) (phase : Pop → LifeCyclePhase) :
    (∀ p, phase p = LifeCyclePhase.Student) → Subcritical κ

/-- High-throughput communities have shallow attractors: a Student-dominated
    population supports no HOA, whatever its census headcount. Now a *theorem*,
    resting on the narrowly-scoped empirical axiom above. -/
theorem highthroughput_shallow_attractor {Pop : Type} [Fintype Pop] [DecidableEq Pop]
    (κ : CouplingKernel Pop) (phase : Pop → LifeCyclePhase)
    (h : ∀ p, phase p = LifeCyclePhase.Student) :
    ¬ ∃ hoa : HOA Pop, hoa.kernel = κ :=
  no_hoa_of_subcritical (studentDominated_subcritical κ phase h)

-- ════════════════════════════════════════════════════════════════
-- §8. PERCEPTION — FILTER, REGISTRATION, AND THE PUTNAM LOOP
-- An agent's manifold (its cognitive state: the accumulated conditioned history, Putnam's
-- CR) filters external events before deliberation. Sub-community similarity = shared
-- manifold structure. Rewritten 2026-10-18: the filter reads the cognitive state, not the
-- coupling vector, and the Perception morphism is defined from it.
-- ════════════════════════════════════════════════════════════════

-- `Event` (a real change of world state) is defined in § 4d, beside B₁'s own dynamics,
-- because marks (§ 4b) are made by events. Here it is what a percept filters.

/-- A percept: what an agent actually registers from an event. This is the event filtered
    through the agent's manifold, its current cognitive state. Two agents whose manifolds
    differ perceive different things from the same event, prior to any deliberation.
    **axiom-kind:** carrier -/
axiom Percept : Type

/-- A **stimulus**: what reaches an agent's cognition. One filter, two sources: a B₁ event
    (perception) or a B₃ inscription (incorporation). `DomainTrichotomy` § Cardinality and
    `InscriptionMarket` (δ's docstring) both say the percept and incorporation filters are
    one mechanism on the two shared sources; this type is that claim. (Added 2026-10-18.) -/
inductive Stimulus where
  | world (e : Event)
  | inscription (c : InscriptionContent)

/-- **The manifold filter**: what a stimulus registers as, given the receiver's current
    cognitive state (its manifold: the accumulated conditioned history, Putnam's CR). Coupling
    decides *which* stimuli reach an agent (exposure, not yet formalized); the manifold decides
    *what* they register as.
    **axiom-kind:** definitional -/
axiom stimulusFilter : Stimulus → CognitiveState → Percept

/-- **The perceptual filter**: the manifold filter on a B₁ event. *Retyped 2026-10-18* from
    `Event → CouplingWeightVector → Percept`, and a definition (not an axiom) since
    incorporation joined the same filter the same day. -/
noncomputable def perceptualFilter (e : Event) (cs : CognitiveState) : Percept :=
  stimulusFilter (.world e) cs

/-- A distance on percept space, so that "similar percepts" is a claim about the
    percepts rather than an unconstrained existential.
    **axiom-kind:** definitional -/
axiom perceptDist : Percept → Percept → ℝ

-- axiom-kind: definitional
axiom perceptDist_nonneg : ∀ p q, 0 ≤ perceptDist p q
-- axiom-kind: definitional
axiom perceptDist_self   : ∀ p, perceptDist p p = 0
-- axiom-kind: definitional
axiom perceptDist_comm   : ∀ p q, perceptDist p q = perceptDist q p

/-- Sub-community perceptual similarity: agents in similar manifold states perceive events
    similarly. This is the formal basis for sub-community coherence — it is perceptual, not
    merely geographic. (Stated over coupling vectors until 2026-10-18.)

    **Repaired 2026-07-26.** The former definition read
    `∀ e, ∃ dist : ℝ, dist < ε` — `dist` was unconstrained and neither side occurred in
    the body, so it was provable for *every* pair at *every* `ε`, which in turn made
    `polarizationAsBifurcation`'s hypothesis refutable and that axiom unusable. -/
def perceptuallySimilar (s₁ s₂ : CognitiveState) (ε : ℝ) : Prop :=
  ∀ e : Event, perceptDist (perceptualFilter e s₁) (perceptualFilter e s₂) < ε

/-- Polarization as perceptual bifurcation: when an event produces strongly
    divergent percepts across the manifold, sub-communities move in opposite
    directions. This is not mere disagreement — it is prior to deliberation.

    Now a *theorem*. Note also that the superseded axiom concluded divergence at
    **every** event, which was too strong: dissimilarity somewhere does not make
    two agents perceive every event differently. The existential is the correct
    statement, and it is what the metric definition actually yields. -/
theorem polarizationAsBifurcation
    (s₁ s₂ : CognitiveState) (ε : ℝ) (hε : 0 < ε)
    (h : ¬ perceptuallySimilar s₁ s₂ ε) :
    ∃ e : Event, perceptualFilter e s₁ ≠ perceptualFilter e s₂ := by
  unfold perceptuallySimilar at h
  rw [not_forall] at h
  obtain ⟨e, he⟩ := h
  refine ⟨e, fun heq => ?_⟩
  rw [heq, perceptDist_self] at he
  exact he hε

/-- **Polarization in the shared world.** `polarizationAsBifurcation` with its event placed:
    two agents whose manifolds are not perceptually similar perceive differently an event
    that occurs in a world state. "The same B₁ event, mapped onto different manifolds" is a
    statement about one world. -/
theorem polarizationInSharedWorld
    (s₁ s₂ : CognitiveState) (ε : ℝ) (hε : 0 < ε)
    (h : ¬ perceptuallySimilar s₁ s₂ ε) :
    ∃ (e : Event) (w : World), occursIn e w ∧ perceptualFilter e s₁ ≠ perceptualFilter e s₂ := by
  obtain ⟨e, he⟩ := polarizationAsBifurcation s₁ s₂ ε hε h
  obtain ⟨w, hw⟩ := (event_localized e).1
  exact ⟨e, w, hw, he⟩

/-! ### The Perception morphism, defined (2026-10-18)

B₁ reaches cognition only as **stimulation**, by two routes: the *filtered* route (a percept,
whose content depends on the manifold) and the *somatic* route (entrainment, which acts on
the substrate below the filter; § 9's rhythm-class interventions). The morphism is their
composite. What it does not yet include: exposure (which events reach which agents, the job
coupling now has) and the registration floor δ (`InscriptionMarket`). The Path A / Path B
asymmetry lives in `register` (below), shared with incorporation. -/

/-! ### Registration: Path A and Path B (2026-10-18)

Putnam: "There is no differentiation except via explicit contradiction." A percept that
contradicts the agent's current **relative dominant** (RD: the act that stops search, defined
by what it rejects) forces differentiation, the Path A substrate: expensive, durable, it
rewires the rejection structure. A percept that fits it reinforces, the Path B substrate:
cheap, it strengthens existing links and creates none. The split is by contradiction, not
by source: a B₁ event and a B₃ inscription pass through the same update. Whether an
inscription can, in practice, force differentiation (the vault leans "rarely, and fragile")
is not decided here. -/

/-- Putnam's **relative dominant**: what an agent's cognitive state currently settles on,
    individuated by the rejection structure that constitutes it (`Putnam-Peter` § RD).
    **axiom-kind:** carrier -/
axiom RelativeDominant : Type

/-- The relative dominant a cognitive state currently holds.
    **axiom-kind:** definitional -/
axiom dominantOf : CognitiveState → RelativeDominant

/-- A percept **contradicts** a cognitive state when it violates the state's current
    dominant: the conditioned prediction fails (`Putnam-Peter` § Emotions: "CR prediction
    failure").
    **axiom-kind:** definitional -/
axiom contradicts : Percept → CognitiveState → Prop

/-- **Differentiation** (Path A substrate): the update a contradicting percept forces.
    **axiom-kind:** definitional -/
axiom differentiate : Percept → CognitiveState → CognitiveState

/-- **Reinforcement** (Path B substrate): the update a fitting percept makes.
    **axiom-kind:** definitional -/
axiom reinforce : Percept → CognitiveState → CognitiveState

/-- **Reinforcement does not change the relative dominant.** "Simple reinforcement ...
    strengthens existing links but does not create new ones"; it "only deepens the existing
    SS" (`Putnam-Peter` § Differentiation via contradiction only).
    **axiom-kind:** empirical
    **anchor:** vault:AgentResponseMechanism -/
axiom reinforce_preserves_dominant :
    ∀ (p : Percept) (cs : CognitiveState), dominantOf (reinforce p cs) = dominantOf cs

open Classical in
/-- **Registration**: how a registered percept updates the cognitive state (Putnam's CR
    update), split by contradiction into differentiation (Path A) and reinforcement (Path B).
    A definition since 2026-10-18 (it was an opaque axiom for one PR). -/
noncomputable def register (p : Percept) (cs : CognitiveState) : CognitiveState :=
  if contradicts p cs then differentiate p cs else reinforce p cs

/-- **No differentiation except via contradiction** (Putnam), as a theorem: if registering a
    percept changes the relative dominant, the percept contradicted the state. Follows from
    `reinforce_preserves_dominant` alone. -/
theorem no_differentiation_without_contradiction
    (p : Percept) (cs : CognitiveState)
    (h : dominantOf (register p cs) ≠ dominantOf cs) : contradicts p cs := by
  by_contra hc
  apply h
  unfold register
  rw [if_neg hc]
  exact reinforce_preserves_dominant p cs

/-- **The somatic route**: stimulation that acts on the cognitive substrate without passing
    the manifold filter. It takes no `Percept`. This is where rhythm-class interventions act
    (§ 9, `bypassesFilter`, `only_rhythm_class_bypasses_filter`): entrainment pre-conditions
    the substrate before any percept forms.
    **axiom-kind:** definitional -/
axiom entrain : Event → CognitiveState → CognitiveState

/-- **Perception (B₁ → B₂), defined.** An event reaches the agent by both routes: the somatic
    route acts on the substrate, then the filtered route registers what the event is *for that
    manifold*. The filter reads the state *after* entrainment, so a rhythm that has
    pre-conditioned the substrate changes what registers. Reads a change (an `Event`), not a
    snapshot; replaces the deleted opaque `perception`. -/
noncomputable def perceive (e : Event) (cs : CognitiveState) : CognitiveState :=
  let cs' := entrain e cs
  register (perceptualFilter e cs') cs'

/-- Perceiving a sequence of events: each is perceived by the state the previous ones left. -/
noncomputable def perceiveSeq : List Event → CognitiveState → CognitiveState
  | [], cs => cs
  | e :: es, cs => perceiveSeq es (perceive e cs)

/-- **The Putnam loop, stated.** The state an event leaves is the filter for the next one: the
    processing chain is recursive (`AgentResponseMechanism` § "Manifold evolution"). True by
    construction; its content is in the types (the filter reads the state the loop updates). -/
theorem perceiveSeq_cons (e : Event) (es : List Event) (cs : CognitiveState) :
    perceiveSeq (e :: es) cs = perceiveSeq es (perceive e cs) := rfl

/-- The second of two events is filtered by the state the first one left. -/
theorem second_percept_filtered_by_first (e₁ e₂ : Event) (cs : CognitiveState) :
    perceiveSeq [e₁, e₂] cs = perceive e₂ (perceive e₁ cs) := rfl

/-- **Incorporation (B₃ → B₂), defined.** An inscription passes through the same manifold
    filter as a B₁ event and the same Path A / Path B update. It takes the prior cognitive
    state, so what an inscription does depends on the manifold it lands on: Path B's
    conditionality on prior Path A roads is now expressible. (No somatic route: entrainment is
    bodily, and an inscription reaches the agent as content.) Replaces the deleted opaque
    `incorporate`; matches Z's `Incorporate`, which already extended the prior B₂. -/
noncomputable def incorporate (c : InscriptionContent) (cs : CognitiveState) :
    CognitiveState :=
  register (stimulusFilter (.inscription c) cs) cs

/-- **An inscription changes the dominant only by contradicting it**: the B₃ instance of
    `no_differentiation_without_contradiction`. Reading something that fits what one already
    holds deepens it and changes no rejection structure. -/
theorem incorporation_differentiates_only_by_contradiction
    (c : InscriptionContent) (cs : CognitiveState)
    (h : dominantOf (incorporate c cs) ≠ dominantOf cs) :
    contradicts (stimulusFilter (.inscription c) cs) cs :=
  no_differentiation_without_contradiction _ cs h

/-! ### Exposure: whether a stimulus reaches an agent at all (2026-10-18)

The gate upstream of the others. Coverage filtering (`stimulusFilter`), the registration
floor δ (`InscriptionMarket`) and capacity gating (`SufficientDepth`) are all properties of
B₂. Exposure is not: it is where the agent sits in B₁ and in the coupling graph. Decisions
recorded with it (PI, 2026-10-18):

* **By source.** B₁ events reach an agent by co-presence (the local geographic channel);
  B₃ inscriptions reach it through the coupling network and the platforms that deliver
  content (the B₃-mediated channels, `CouplingWeightVector`). Not formalized at this tier:
  Core has no agent location and no Core-level coupling graph.
* **Binary at this tier.** Graded exposure is amplification (ETHOS's `a(c)`), later.
* **The formal home of platform power.** Ω-actors and platforms operate on *what reaches*
  agents, as distinct from *how it registers*.

What it buys now: divergent reactions have two formally distinct sources. Agents who were
exposed to different stimuli diverge by **exposure**; agents exposed to the same stimulus
who register it differently diverge by **perceptual bifurcation** (category error 5, and
`polarizationInSharedWorld`, which applies exactly under shared exposure). -/

/-- An agent is **exposed to** a stimulus: it reaches the agent at all.
    **axiom-kind:** definitional -/
axiom exposedTo : Agent → Stimulus → Prop

/-- **Exposure is not uniform**: some stimulus reaches one agent and not another. The
    minimum that makes exposure divergence (a filter bubble) possible, and that keeps it
    distinct from perceptual bifurcation. Fails in a model where everyone is exposed to
    everything.
    **axiom-kind:** empirical
    **anchor:** vault:Percept -/
axiom exposure_nonuniform :
    ∃ (a b : Agent) (s : Stimulus), exposedTo a s ∧ ¬ exposedTo b s

/-- Two agents share exposure to a stimulus. Perceptual bifurcation is the divergence that
    remains under shared exposure. -/
def sharedExposure (a b : Agent) (s : Stimulus) : Prop := exposedTo a s ∧ exposedTo b s

/-- **Exposure is not always shared**, so divergence under shared exposure (perceptual
    bifurcation) is a strict special case of divergence in general: some pair of agents does
    not share exposure to some stimulus. -/
theorem exposure_not_always_shared : ∃ (a b : Agent) (s : Stimulus), ¬ sharedExposure a b s := by
  obtain ⟨a, b, s, _, hb⟩ := exposure_nonuniform
  exact ⟨a, b, s, fun h => hb h.2⟩

open Classical in
/-- **Reception**: a stimulus updates an agent's cognitive state only if the agent is exposed
    to it, and then by perception (a B₁ event) or incorporation (a B₃ inscription). -/
noncomputable def receive (a : Agent) (s : Stimulus) (cs : CognitiveState) : CognitiveState :=
  if exposedTo a s then
    match s with
    | .world e => perceive e cs
    | .inscription c => incorporate c cs
  else cs

/-- **No registration without exposure**: a stimulus that does not reach an agent leaves its
    cognitive state unchanged. -/
theorem unexposed_changes_nothing (a : Agent) (s : Stimulus) (cs : CognitiveState)
    (h : ¬ exposedTo a s) : receive a s cs = cs := by
  unfold receive
  rw [if_neg h]

/-- The complete normative change chain: inscribe → incorporate → constrain
    cognition → act → change objective world. Any joint can break. (Moved here from § 4b on
    2026-10-18; `incorporate` now takes the prior cognitive state.) -/
theorem normativeChangeChain
    (a : Agent) (cs : CognitiveState) (w : World) :
    -- An inscription produced by this agent...
    let ic := inscribe a cs
    -- ...when incorporated into a cognitive state, produces a new one...
    let cs' := incorporate ic cs
    -- ...which, when acted upon, produces a new world state.
    let _w' := action a cs' w
    -- The result is a modified world. Whether the change is normatively
    -- significant is an empirical question outside this formal encoding.
    True := trivial

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

-- `nodeSucceeds` was DELETED 2026-09-12, as the residue of the deletion below.
--
-- It was the predicate `rhythmLowersSeedSize` was stated over:
--     axiom nodeSucceeds : Region → Stratum → ℕ → CouplingWeightVector → Prop
-- When that axiom went in 2026-07-26 its support stayed, and nothing referenced
-- `nodeSucceeds` afterwards except the note below describing the thing that had
-- been removed. `scripts/axiom_report.py` surfaced it: no theorem depended on it,
-- and stripping comments before counting showed no declaration did either.
--
-- The deletion is the supersession rider applied to itself. Removing a construct
-- has to sweep what it leaves unsupported, or the next reader finds a predicate
-- with no proposition and no consumer and cannot tell whether it is scaffolding
-- for future work or debris. Restoring it costs one line if the real version
-- below is ever built.

-- `rhythmLowersSeedSize` was DELETED 2026-07-26 (audit Appendix D.3).
--
-- It asserted that applying create_rhythm before create_node lowers the
-- minimum seed size, as:
--     nodeSucceeds region stratum seedSize coupling →
--     ∃ reducedSeed, reducedSeed ≤ seedSize ∧ nodeSucceeds region stratum reducedSeed coupling
--
-- The file's own NOTE admitted it: "as stated, this is trivially satisfiable
-- (take reducedSeed = seedSize)". The `≤` makes it a tautology. It was
-- referenced nowhere, and `InterventionClasses.md` nevertheless described it
-- as "(axiom -- empirically grounded)" -- a vacuous axiom laundering an
-- untested intervention hypothesis through the formal layer, which is worse
-- than no axiom.
--
-- A real version needs strict inequality AND a model of how rhythm shifts
-- coupling state before the node is applied -- i.e. the ceiling-raising
-- mechanism of CycleFormationAndClosure § "Interventional ordering". That is
-- new modelling, not a repair, so nothing is asserted here in the meantime.
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
-- (grading) and sub-graph (edges) candidates are one graded preorder. `grade_mono`
-- permits cycles among equal-grade nodes, so it is a DAG only where acyclic
-- (Alloy E1). Frontiers keep each such cycle whole (Alloy E2b; B3RegionGeometry.md).
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
    sub-graph = the edges) into one graded preorder (a DAG wherever it is acyclic).

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
