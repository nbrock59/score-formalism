import Formal.Score.Core

set_option linter.unusedVariables false
set_option linter.style.whitespace false

/-!
# SCORE.Sigma

Σ-actor spine (Tier-1 parity, Session 1): the co-inscription morphism with a
type-level depth gate on BOTH participants, the `CoInscriptionEvent` formation
primitive, the `SigmaActorArchitecture` structure, the A/Σ/Ω actor-type tag, the
closure-derived Σ-actor life-cycle phases, the five-operator Σ-intervention
taxonomy, and the multi-layer inter-Σ coupling relation.

**Two Lean views of a Σ-actor (reconciled 2026-07-24).** `Core.SigmaActor`
(Core.lean §3) is the *opaque carrier* — the Constituent-level identity §HM's
`HOAState` populations range over. This module's `SigmaActorArchitecture` is the
*architectural refinement* — how a Σ-actor is formed, maintained, and what telos
it bears. Both are Lean counterparts of the one OWL class `core:SigmaActor`
(SC-G-09); `SigmaActorArchitecture.carrier` is the forgetful bridge between them.
Before 2026-07-24 this structure was itself named `SigmaActor`, which *collided*
with the carrier Core added at M1 (#461, 2026-07-17). Because nothing imports this
module (it was absent from `Formal/Score.lean`), the collision left it silently
non-compiling and unguarded by CI for a week. This module is now wired into
`Formal/Score.lean`, so the build guards it.

The depth gate is the Lean mirror of the OWL constraint
`SigmaActor ⊑ hasReflexiveDepth some SufficientDepth` applied at the formation
morphism itself: `coInscribe` takes `SufficientDepth a` AND `SufficientDepth b`
as explicit arguments, so a co-inscription term is literally unconstructable
without both witnesses. Direct analog of Core's `inscribeB2Ref` single-side gate
lifted to the B₂×B₂→B₃ morphism.

Vault: obsidian/SCORE/emergence/mechanism/SigmaActorArchitecture.md
       obsidian/SCORE/emergence/mechanism/FormalInformalClosure.md
OWL:   formal/score-core.owl §§ SigmaActor, CoInscriptionEvent,
       TelosBearingContent, SigmaInterventionClass, coupledTo family.

Session 2 (deferred): disjointness lemmas witnessing the A/Σ/Ω trichotomy,
monotonicity lemmas over the coupling layers, peer-module frontmatter updates
advertising Σ-actor Lean parity, and end-to-end compile-verify.
-/

namespace SCORE

-- ════════════════════════════════════════════════════════════════
-- §23. CO-INSCRIPTION MORPHISM (B₂×B₂→B₃) — TYPE-LEVEL DEPTH GATE
-- The foundational new primitive for the Σ-actor spine. NOT derivable from
-- A-actor machinery: requires the ⊗ joint-state precondition that each party
-- model the others modeling it — which requires sufficient reflexive depth on
-- BOTH participants. Enforced at the type level so an ill-depthed co-inscription
-- fails to elaborate. See SigmaActorArchitecture.md § "The Formal/Informal
-- Closure" for the theoretical grounding.
-- ════════════════════════════════════════════════════════════════

/-- Co-inscription (B₂×B₂→B₃): two agents jointly produce inscription content
    that neither would have produced alone. The upward direction of organizational
    closure — the ongoing scale-enabling, formal-layer-sustaining operation that
    cannot be reduced to sequential individual B₂→B₃ inscriptions.

    **Depth gate.** Both participants must supply `SufficientDepth` explicitly —
    without either proof the term does not elaborate. Contrast Core's `inscribe`
    (referent-agnostic, ungated) and `inscribeB2Ref` (single-side B₂-referential
    gate). -/
axiom coInscribe :
    (a b : Agent) → SufficientDepth a → SufficientDepth b →
    CognitiveState → CognitiveState → InscriptionContent

/-- The gate is load-bearing on BOTH sides: dropping either depth witness fails
    to elaborate. `noncomputable` because `coInscribe` is an axiom (no executable
    body), and the point of the example is type-level elaboration, not execution. -/
noncomputable example
    (a b : Agent) (ha : SufficientDepth a) (hb : SufficientDepth b)
    (csA csB : CognitiveState) : InscriptionContent :=
  coInscribe a b ha hb csA csB

-- ════════════════════════════════════════════════════════════════
-- §24. THE CO-INSCRIPTION EVENT — Σ-ACTOR FORMATION PRIMITIVE
-- OWL: CoInscriptionEvent + `SigmaActor ⊑ formedBy some CoInscriptionEvent`.
-- The specific founding instance whose output is the Σ-actor's constitutive
-- founding B₃. Distinct from the ongoing `coInscribe` morphism (an operation
-- type) — this is the event that grounds a Σ-actor's existence. Autonomous
-- closure: constituents self-produce the constraint that closes their cycle
-- (contrast the heteronomous closure of an Ω-actor — SoftwareOntology.md).
-- ════════════════════════════════════════════════════════════════

/-- A co-inscription event. Packaging the depth witnesses into the structure
    materializes the OWL depth axiom as a construction precondition: instantiating
    a `CoInscriptionEvent` requires supplying `SufficientDepth` for both
    participants. -/
structure CoInscriptionEvent where
  participantA : Agent
  participantB : Agent
  depthA       : SufficientDepth participantA
  depthB       : SufficientDepth participantB
  stateA       : CognitiveState
  stateB       : CognitiveState

namespace CoInscriptionEvent
  /-- The founding B₃ produced by this event: the participants' depth witnesses
      packaged with the event discharge the `coInscribe` depth gate. -/
  noncomputable def output (e : CoInscriptionEvent) : InscriptionContent :=
    coInscribe e.participantA e.participantB e.depthA e.depthB e.stateA e.stateB
end CoInscriptionEvent

-- ════════════════════════════════════════════════════════════════
-- §25. TELOS-BEARING vs LOSS-FUNCTION CONTENT (Ω CONTRAST)
-- OWL: `TelosBearingContent` (Σ-actor characteristic output) vs
-- `LossFunctionContent` (Ω-actor characteristic output). The B₃-content axis
-- that discriminates the two non-A actor types — the Ω contrast that makes a
-- Σ-actor a Σ-actor rather than an Ω-actor. See B3-Inscription.md.
-- ════════════════════════════════════════════════════════════════

/-- The Σ-actor B₃-output class marker: content encoding a contestable telos. -/
axiom IsTelosBearing : InscriptionContent → Prop

/-- The Ω-actor B₃-output class marker: content encoding a non-contestable loss
    function (the software/AI contrast). -/
axiom IsLossFunction : InscriptionContent → Prop

-- ════════════════════════════════════════════════════════════════
-- §26. THE MAINTAINING COMMUNITY
-- OWL: `SigmaActor ⊑ maintainedBy some HumanCommunity`. Persistence requires a
-- maintaining community — closure failure ≡ dissolution
-- (FormalInformalClosure.md § "Death"; MortalityBoundary.md).
-- ════════════════════════════════════════════════════════════════

/-- A `HumanCommunity` — the maintaining substrate a Σ-actor persists on. -/
abbrev HumanCommunity := List Agent

-- ════════════════════════════════════════════════════════════════
-- §27. THE Σ-ACTOR STRUCTURE
-- OWL axioms carried as structure fields:
--   SigmaActor ⊑ Actor ⊓ HigherOrderAgent                  (docstring)
--   ⊑ formedBy some CoInscriptionEvent                      (formationEvent)
--   ⊑ maintainedBy some HumanCommunity                      (maintainingCommunity)
--   ⊑ inscribesTo some TelosBearingContent                  (foundingTelos + telosBearing)
--   ⊑ hasReflexiveDepth some SufficientDepth                (inherited via formationEvent)
-- ════════════════════════════════════════════════════════════════

/-- A Σ-actor's **architectural refinement**: a higher-order collective agent
    formed by a `CoInscriptionEvent`, maintained by a `HumanCommunity`, inscribing
    telos-bearing content. Reflexive depth is inherited from the formation event's
    participants — autonomous closure grounds the Σ-actor's depth in the depth of
    its founders.

    **Naming.** This structure carries the *architecture* of a Σ-actor (how it is
    formed, maintained, and what telos it bears). It is deliberately distinct from
    `Core.SigmaActor` (Core.lean §3), the **opaque carrier** that `Constituent.
    SigmaAgent` and §HM's `HOAState` populations range over. Both are Lean
    counterparts of the single OWL class `core:SigmaActor` (SC-G-09) at two levels
    of detail; `SigmaActorArchitecture.carrier` (below) is the seam between them.
    Renamed from `SigmaActor` on 2026-07-24 to end the name collision that had left
    this module silently non-compiling since M1 (#461) added the Core carrier — see
    the module header. -/
structure SigmaActorArchitecture where
  formationEvent       : CoInscriptionEvent
  maintainingCommunity : HumanCommunity
  foundingTelos        : InscriptionContent
  telosBearing         : IsTelosBearing foundingTelos

namespace SigmaActorArchitecture
  /-- Inherited reflexive depth on participant A of the formation event. -/
  def inheritedDepthA (σ : SigmaActorArchitecture) :
      SufficientDepth σ.formationEvent.participantA :=
    σ.formationEvent.depthA
  /-- Inherited reflexive depth on participant B of the formation event. -/
  def inheritedDepthB (σ : SigmaActorArchitecture) :
      SufficientDepth σ.formationEvent.participantB :=
    σ.formationEvent.depthB
end SigmaActorArchitecture

/-- **Bridge to the Constituent-level carrier.** Every architecturally-described
    Σ-actor has an opaque identity as an HOA constituent — the `Core.SigmaActor`
    carrier that `Constituent.SigmaAgent` and §HM's `HOAState` populations consume.
    This forgetful map is the seam between the two Lean views of a Σ-actor:
    `SigmaActorArchitecture` (this module — the architecture) and `SigmaActor`
    (Core.lean §3 — the opaque carrier the maintenance spine ranges over). Both are
    Lean counterparts of the single OWL class `core:SigmaActor` (SC-G-09); this
    axiom records that the architectural description determines a carrier identity.
    Axiomatic because the carrier is an opaque `axiom SigmaActor : Type` with no
    constructors, so the map cannot be given a computational body. -/
axiom SigmaActorArchitecture.carrier : SigmaActorArchitecture → SigmaActor

-- ════════════════════════════════════════════════════════════════
-- §28. ACTOR-TYPE TRICHOTOMY TAG (A / Σ / Ω)
-- OWL: `AAgent ⊔ OmegaActor ⊔ SigmaActor` all-disjoint. The three actor kinds
-- partition the actor stratum. Constructors are pairwise-distinct by Lean
-- construction; the corresponding disjointness lemma discharging the OWL
-- AllDisjoint axiom is Session 2. Constructors named `AAgent`/`Sigma`/`Omega`
-- (not `SigmaActor`/`OmegaActor`) to avoid shadowing the top-level
-- `SigmaActorArchitecture` structure name.
-- ════════════════════════════════════════════════════════════════

/-- The three actor-type tags: A-actor (individual, B₂-grounded, biological),
    Σ-actor (higher-order collective, telos-bearing), Ω-actor (non-B₂-grounded,
    loss-function-bearing — software, AI systems). -/
inductive ActorType : Type where
  | AAgent : ActorType
  | Sigma  : ActorType
  | Omega  : ActorType
deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════════════════
-- §29. Σ-ACTOR LIFE-CYCLE PHASES (CLOSURE-DERIVED)
-- Formation → Maturity → Crossover → Death → Reinvention. Grounded in the
-- formal/informal closure framework: phases are CLOSURE EVENTS, not merely
-- organizational descriptions. See FormalInformalClosure.md § "Lifecycle
-- derivation from closure". SIBLING of Core's A-actor `LifeCyclePhase`, not
-- a subclass — different actor strata; a forced common parent would be premature
-- abstraction.
-- ════════════════════════════════════════════════════════════════

/-- The five Σ-actor life-cycle phases, derived from formal/informal closure.

    The transition dynamics between these phases are model-checked in
    `formal/tla/SigmaLifeCycle.tla` (TLC), where they are unavailable here (this
    is the enum only). Over a dual `formal`/`informal` closure state, TLC checks:
    the stratification constraint (a live Maturity closure needs both layers
    stable; the formal higher stratum rises only via co-inscription gated on a
    stable informal lower stratum — SO-NS-Stratification.md); that Reinvention
    occurs only within a surviving formal shell (never after formal dissolution);
    and a reachability trace of the full Formation→…→Reinvention trajectory. See
    `obsidian/SCORE/methodology/ModelCheckedDynamics.md`. -/
inductive SigmaLifeCyclePhase : Type where
  /-- Formation: first achievement of closure — informal networks co-inscribe
      formal B₃ that begins to constrain those networks. HOA crystallization
      at the Σ-actor level. -/
  | Formation   : SigmaLifeCyclePhase
  /-- Maturity: stable closure — formal and informal layers reliably generating
      each other. Absorbs membership turnover without losing closure. -/
  | Maturity    : SigmaLifeCyclePhase
  /-- Crossover: metabolic stress — informal-layer permeability declines relative
      to coordination-problem scale. West's superlinear→sublinear transition;
      fossilization risk increases. -/
  | Crossover   : SigmaLifeCyclePhase
  /-- Death: closure failure — either informal-layer collapse (formal B₃ persists
      as an archived document) or formal-layer dissolution (informal networks
      survive but lack official delineation). -/
  | Death       : SigmaLifeCyclePhase
  /-- Reinvention: new closure formation within a surviving formal shell — new
      informal networks co-inscribing new founding B₃ into the persisted formal
      layer. IBM-under-Gerstner pattern. -/
  | Reinvention : SigmaLifeCyclePhase
deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════════════════
-- §30. Σ-ACTOR INTERVENTION TAXONOMY (FIVE OPERATORS)
-- OWL: `SigmaInterventionClass`, five pairwise-disjoint operators. SIBLING of
-- Core's `Intervention` (A-actor), not a subclass — different actor strata; a
-- forced common parent would be premature abstraction (RefinementArchitecture
-- no-premature-abstraction rule). Q3 promotions: the first four from AGORA∩ETHOS
-- (2026-06-04, second on-demand event); the fifth from ATLAS∩NEXUS (2026-06-04,
-- fifth on-demand event). Morphism-routing per operator and activation energies
-- are not DL-expressible; carried in SigmaActorArchitecture.md § 5.
-- ════════════════════════════════════════════════════════════════

/-- The five Σ-actor intervention operator classes. -/
inductive SigmaIntervention : Type where
  /-- `InstitutionalDesign`: modifies internal coupling topology of the target
      (supermajority gates, tenure protection, independent-appointment
      commissions, distributed-authority centrality reduction). Changes the
      attractor structure of the collective manifold rather than individual
      coupling. -/
  | institutionalDesign        (target : SigmaActorArchitecture) : SigmaIntervention
  /-- `InterSigmaCoupling`: creates or dissolves formal coupling between
      Σ-actors — treaty formation, alliance, sanctions, diplomatic recognition.
      The Σ-level analog of A-actor `create_edge`. -/
  | interSigmaCoupling         (σ₁ σ₂ : SigmaActorArchitecture) : SigmaIntervention
  /-- `FoundingConditionIntervention`: influences the founding B₃ of a nascent
      Σ-actor at the `CoInscriptionEvent` moment. Highest-leverage, longest-
      lasting; the Σ-analog of childhood inscription influence. -/
  | foundingCondition          (event : CoInscriptionEvent) : SigmaIntervention
  /-- `CollectiveManifoldShift`: operations that shift a Σ-actor's effective
      collective manifold toward or away from B₁ accuracy — disruption pole
      (information operations, leadership-succession engineering); restoration
      pole (automatic correction triggers acting on the maintaining community
      without the captured comparator). -/
  | collectiveManifoldShift    (target : SigmaActorArchitecture) : SigmaIntervention
  /-- `AdjacentPossibleConstraint`: acts on structural possibility space
      directly — infrastructure, supply-chain, technology control — opening or
      closing behavioral paths regardless of the target's manifold. Least
      reflexive-depth-dependent operator (needs only structural dependencies,
      not a model of the target). ATLAS surfaced it; NEXUS was the second peer. -/
  | adjacentPossibleConstraint                     : SigmaIntervention

-- ════════════════════════════════════════════════════════════════
-- §31. INTER-Σ COUPLING (MULTI-LAYER, EXECUTIVE-MEDIATED)
-- OWL: `coupledTo` (Q3 PROMOTE 2026-06-04, third on-demand event, AGORA∩ATLAS
-- intersection) with three sub-relations. Density over `coupledTo` crystallizes
-- Σ-HOAs (coalitions / deterrence basins) at the SAME Erdős-Rényi threshold that
-- governs A-actor HOA formation — SO is ER at every stratum. Symmetric (mutual
-- coupling). The ER threshold and layer-superposition weighting are DL-
-- inexpressible and live in prose (SigmaActorArchitecture.md § 2a).
-- ════════════════════════════════════════════════════════════════

/-- Treaty-based coupling: formal B₃ commitments (alliance, security guarantee,
    trade agreement). Slow, legible — the formal membrane. -/
axiom coupledByTreaty : SigmaActorArchitecture → SigmaActorArchitecture → Prop

/-- Behavioral coupling: repeated interaction (trade flows, diplomatic contact,
    military coordination). Medium-timescale — the metabolic layer over the
    formal membrane. -/
axiom coupledByBehavior : SigmaActorArchitecture → SigmaActorArchitecture → Prop

/-- Manifold-proximity coupling: similarity of effective collective manifolds.
    Direct analog of the A-actor |φᵢ − φⱼ|⁻¹ criterion lifted one stratum up. -/
axiom coupledByManifoldProximity : SigmaActorArchitecture → SigmaActorArchitecture → Prop

/-- The total inter-Σ coupling relation: any of the three sub-layers holding
    counts as coupling (layer-superposition; disjunctive union). Executive-to-
    executive A-actor relationships modulate all three — the informal channel
    that runs the formal membrane's metabolism. -/
def coupledTo (σ₁ σ₂ : SigmaActorArchitecture) : Prop :=
  coupledByTreaty σ₁ σ₂ ∨ coupledByBehavior σ₁ σ₂ ∨ coupledByManifoldProximity σ₁ σ₂

end SCORE
