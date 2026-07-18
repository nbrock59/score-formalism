import Formal.Score.Core
import Formal.Score.HOAMaintenance

set_option linter.unusedVariables false
set_option linter.style.whitespace false

/-!
# SCORE.Nexus

NEXUS peer: the contraction-antitone lemma (SS13) and the patent-citation
network binding (SS16).
-/

namespace SCORE

-- ── NEXUS: contraction is antitone in the adjacent possible ──
-- The proof-side of the NEXUS∩ETHOS core:AdjacentPossibleMeasure promotion.
-- (NEXUS-KillZoneMeasurement.md Phase B; OWL nexus:KillZoneExtent ⊑
-- core:AdjacentPossibleMeasure.)

/-- A contraction (kill-zone) event removes reachable configurations: the post-event
    adjacent possible is a subset of the pre-event one. -/
def IsContraction {α : Type} (pre post : Set α) : Prop := post ⊆ pre

/-- **NEXUS antitone.** Against any monotone breadth functional Φ (a larger reachable
    set is at least as broad), a contraction cannot increase breadth: Φ(post) ≤ Φ(pre),
    i.e. the expand/contract discriminant δ = Φ(post) − Φ(pre) ≤ 0. -/
theorem contraction_is_antitone_in_adjacent_possible
    {α : Type} {pre post : Set α}
    (h : IsContraction pre post)
    (Φ : Set α → ℝ)
    (hΦ : ∀ {A B : Set α}, A ⊆ B → Φ A ≤ Φ B) :
    Φ post ≤ Φ pre :=
  hΦ h


-- ════════════════════════════════════════════════════════════════
-- §16. NEXUS — PATENT-CITATION NETWORK BOUND TO §14 (second specializing peer)
-- The second peer of the ETHOS ∩ NEXUS intersection that promoted §14 to core. NEXUS
-- already clusters its patent-citation network into paradigm clusters for the Φ
-- paradigm-diversity measure (obsidian/SCORE/emergence/applications/
-- NEXUS-KillZoneMeasurement.md) — a paradigm cluster IS a region R(C). The *same*
-- core `DoctrinalNetwork` serves a structurally different (chain) DAG and a contrasting
-- domain (innovation/market vs ETHOS's epistemic) — the domain-contrast that makes the
-- ≥2-peer promotion strong. Toy witness; real patent-citation networks are Q4 BIND.
-- ════════════════════════════════════════════════════════════════

/-- A toy NEXUS technical inscription. Stands for a B₃ inscription (`nexusAsB3`). -/
inductive NexusArtifact
  | priorArt    -- raw prior art / dataset
  | component   -- a component technology
  | standard    -- a technical standard built on components
  | platform    -- a platform / paradigm built on standards
deriving DecidableEq, Repr

/-- Every NEXUS artifact is realized as a B₃ inscription (documents the domain tie;
    not used in the proofs). -/
axiom nexusAsB3 : NexusArtifact → InscriptionContent

/-- Patent / standard citation as a `Bool` relation: `patentCites x y = true` ⇔ y
    cites / builds on prior art x (x is y's substrate). A chain DAG — a different shape
    from ETHOS's (§15) branching one, on the same core machinery. -/
def patentCites : NexusArtifact → NexusArtifact → Bool
  | .priorArt,  .component => true
  | .component, .standard  => true
  | .standard,  .platform  => true
  | _,          _          => false

/-- The technical grading: prior art (written inscription), component (institution),
    standard (meta-idea), platform (generative framework). -/
def nexusGrade : NexusArtifact → B3Level
  | .priorArt  => ⟨2, by omega⟩
  | .component => ⟨3, by omega⟩
  | .standard  => ⟨4, by omega⟩
  | .platform  => ⟨5, by omega⟩

/-- The grading is monotone along every citation edge (the §14 `grade_mono` law). -/
theorem patentCites_graded : ∀ {x y : NexusArtifact},
    patentCites x y = true → nexusGrade x ≤ nexusGrade y := by
  intro x y h
  cases x <;> cases y <;> first | exact absurd h (by decide) | decide

/-- NEXUS's patent-citation network as a §14 `DoctrinalNetwork`. -/
def nexusNetwork : DoctrinalNetwork NexusArtifact where
  composesFrom x y := patentCites x y = true
  grade := nexusGrade
  grade_mono := patentCites_graded

/-- A paradigm cluster = the down-closure of a frontier; a region for free. -/
def paradigmCluster (frontier : Set NexusArtifact) : Set NexusArtifact :=
  nexusNetwork.downClosure frontier

theorem paradigmCluster_isRegion (frontier : Set NexusArtifact) :
    nexusNetwork.IsRegion (paradigmCluster frontier) :=
  nexusNetwork.downClosure_isRegion frontier

/-- **Worked witness.** A platform's paradigm cluster contains its full cited substrate
    down to the raw prior art — recovered from the single stored frontier node
    (priorArt → component → standard → platform). -/
example : NexusArtifact.priorArt ∈ paradigmCluster {NexusArtifact.platform} := by
  refine ⟨NexusArtifact.platform, rfl, ?_⟩
  have h1 : nexusNetwork.composesFrom NexusArtifact.priorArt NexusArtifact.component := rfl
  have h2 : nexusNetwork.composesFrom NexusArtifact.component NexusArtifact.standard := rfl
  have h3 : nexusNetwork.composesFrom NexusArtifact.standard NexusArtifact.platform := rfl
  exact ((Relation.ReflTransGen.single h1).tail h2).tail h3


-- ════════════════════════════════════════════════════════════════
-- §PS-U2. NEXUS U2 SPECIALIZATION --- InnovationHOA as an unfiltered
-- HOAState (Present-Domain → Present-Formal); the *fourth polar case*
-- of Design B's Constituent sum type.
--
-- The HM Specialization Audit (`core/nexus/NEXUS_HM_Specialization_Audit.md`
-- §1) rated U2 as Present-Domain because NX-G-01 (`nexus:InnovationHOA`
-- refining SC-G-11 HigherOrderAgent) named the HOA at the glossary + OWL
-- layer but no Lean specialization instantiated §HM's `HOAState`
-- machinery.
--
-- NEXUS is the *fourth polar case* of `Constituent`, orthogonal to
-- AGORA/ATLAS/ETHOS-community: those three subtypes constrain the
-- population to one stratum; NEXUS's mixed A/Sigma constituency (Orphan 5
-- of the NEXUS audit: "researchers + firms + VCs + universities +
-- regulators") requires the population to admit BOTH `Constituent.AAgent`
-- (researchers, founders) AND `Constituent.SigmaAgent` (firms, VC funds,
-- platform incumbents) freely. That is exactly `HOAState r` with no
-- subtype filter --- NX-G-01's mixed-constituency framing IS the
-- unrestricted case of Design B's sum type.
--
-- Together the four peers exhaust the polar cases:
--   AGORA / BAC / ETHOS-community: `Constituent.AAgent`-only subtype
--   ATLAS: `Constituent.SigmaAgent`-only subtype
--   NEXUS: no filter (mixed A/Σ)
--   ETHOS-institution: separate `SigmaActor` typedef (dual-stratum)
-- ════════════════════════════════════════════════════════════════

/-- **NEXUS's `InnovationHOA` as an unfiltered HOAState** (NX-G-01,
    refining SC-G-11 HigherOrderAgent). Mixed A/Σ constituency:
    researchers / founders (A-actors, appearing as `Constituent.AAgent`)
    and firms / VC funds / platform incumbents (Σ-actors, appearing as
    `Constituent.SigmaAgent`) both populate the ecosystem freely. NX-G-01's
    mixed-constituency framing IS the unrestricted case of Design B ---
    a typedef over `HOAState` with no subtype filter, distinct from
    AGORA / ATLAS / ETHOS-community which each constrain to one stratum. -/
def NexusInnovationHOA (r : Region) : Type := HOAState r

/-- Extract the underlying `HOAState`; §HM machinery applies directly
    (no projection needed since `NexusInnovationHOA r` reduces to
    `HOAState r`). Provided for symmetry with the other peer
    specializations and for future refactoring flexibility. -/
def NexusInnovationHOA.toHOAState {r : Region}
    (ih : NexusInnovationHOA r) : HOAState r := ih


-- ════════════════════════════════════════════════════════════════
-- §PS-U1. NEXUS U1 SPECIALIZATION --- InnovationHOA self-stabilization
-- (Present-Domain → Present-Formal)
--
-- The HM Specialization Audit (`NEXUS_HM_Specialization_Audit.md` §1)
-- rated NEXUS's U1 as Present-Domain: two co-existing self-stabilization
-- stories --- healthy (InnovationHOA maintenance) and pathological
-- (`NSAsCartel`, NX-G-05, "self-maintaining but net-information-
-- decreasing"). No Lean specialization of `SelfStabilizingWithin`
-- existed. Peer-scoped abbrev over §HM's polymorphic predicate,
-- parameterized on the NEXUS U2 type `NexusInnovationHOA`. The
-- healthy-vs-pathological polarity contrast (audit's Joint-abstraction
-- candidate #4) is a genuine theory extension reserved for future
-- HealthyVsPathologicalPolarity work; here we bind only the healthy
-- case at the type layer.
-- ════════════════════════════════════════════════════════════════

/-- **NEXUS U1: self-stabilization of the innovation ecosystem.**
    Peer-scoped abbrev for `SCORE.SelfStabilizingWithin` on
    `NexusInnovationHOA` (NX-G-01). Healthy case; pathological
    (`NSAsCartel`) counterpart reserved for future
    HealthyVsPathologicalPolarity work. Concrete Basin/Legitimate/Moves
    peer-specific / Q4 BIND. -/
def NexusInnovationHOA.stabilizesWithin {r : Region}
    (Basin      : NexusInnovationHOA r → Prop)
    (Legitimate : NexusInnovationHOA r → Prop)
    (Moves      : NexusInnovationHOA r → NexusInnovationHOA r → Prop) : Prop :=
  SelfStabilizingWithin Basin Legitimate Moves


-- ════════════════════════════════════════════════════════════════
-- §PS-U4. NEXUS U4 SPECIALIZATION --- autocatalytic feedback +
-- B₃-substrate prosthetic (Present-Domain → Present-Formal)
--
-- The HM Specialization Audit (`NEXUS_HM_Specialization_Audit.md` §1)
-- rated NEXUS's U4 as Present-Domain: two co-existing autocatalytic
-- stories --- healthy (paradigm-diversity sustained via patent-citation
-- substrate) and pathological (`NSAsCartel`, NX-G-05, VC/incumbent
-- interlock as self-reinforcing predatory loop). Patents / standards
-- (via `paradigmCluster`, §16) provide the real B₃-substrate.
-- `Score/Nexus.lean` §16 specializes patents-network as
-- `Core.DoctrinalNetwork`, NOT as §HM's `AutocatalyticCombine`. This
-- section binds §HM's autocatalytic machinery to `NexusInnovationHOA`
-- via peer-scoped wrappers; the pathological polarity companion is
-- reserved for future HealthyVsPathologicalPolarity work per the audit
-- synthesis §5.5.
-- ════════════════════════════════════════════════════════════════

/-- **NEXUS U4: autocatalytic weight of the innovation ecosystem
    (healthy case).** Aggregate observable weight under a chosen
    autocatalytic-combine operator, delegated via the peer's
    `.toHOAState` projection. Pathological (NSAsCartel) counterpart
    is HealthyVsPathologicalPolarity work. -/
def NexusInnovationHOA.autocatalyticWeight {r : Region}
    (c : AutocatalyticCombine) (ih : NexusInnovationHOA r) : ℝ :=
  HOAState.weight c ih.toHOAState

/-- **NEXUS U4: hysteresis gap closes for the innovation ecosystem
    (healthy case).** Direct specialization of
    `AutocatalyticCombine.closes_hysteresis_gap` via the peer's
    `.toHOAState` projection. -/
theorem NexusInnovationHOA.autocatalytic_closes_gap {r : Region}
    (c : AutocatalyticCombine) (ih : NexusInnovationHOA r)
    (hs : (dissolutionThreshold r).val ≤ ih.toHOAState.substrate.val)
    (he : c.engagementThreshold r ≤ ih.toHOAState.loopEndowment.val) :
    (formationThreshold r).val ≤ ih.autocatalyticWeight c :=
  c.closes_hysteresis_gap r
    ih.toHOAState.substrate ih.toHOAState.loopEndowment hs he


-- ════════════════════════════════════════════════════════════════
-- §PS-U7. NEXUS U7 SPECIALIZATION --- L2 GenerationalRenewalMove
-- (Present-Domain → Present-Formal)
--
-- The HM Specialization Audit (`NEXUS_HM_Specialization_Audit.md` §1)
-- rated NEXUS's U7 as Present-Domain: L2 GenerationalRenewal is
-- particularly natural for NEXUS since patent citations propagate
-- technical knowledge across generations of components → standards →
-- platforms (`paradigmCluster`, §16). `Score/Nexus.lean` §16 specializes
-- patents-network as `Core.DoctrinalNetwork`, NOT as §HM's
-- `GenerationalRenewalMove`. This section binds §HM's L2 axiom to
-- `NexusInnovationHOA` via a peer-scoped wrapper. L1 MemberTurnoverMove
-- (VC funds, founders, firms turning over) is also natural per the audit
-- but is left as a follow-up under the same pattern.
-- ════════════════════════════════════════════════════════════════

/-- **NEXUS U7: L2 generational-renewal slow-move on the innovation
    ecosystem.** Peer-scoped wrapper for `GenerationalRenewalMove` on
    `NexusInnovationHOA`. Peer story: patent citations propagate technical
    knowledge across generations of prior-art → component → standard →
    platform (`paradigmCluster` down-closure). -/
def NexusInnovationHOA.generationalRenewal {r : Region}
    (a b : NexusInnovationHOA r) : Prop :=
  GenerationalRenewalMove a.toHOAState b.toHOAState

/-- **NEXUS U7: renewal maintains ceiling.** The §HM26
    `generationalRenewalMove_maintains_ceiling` axiom lifts through the
    peer's projection: successful generational inscription in the
    innovation ecosystem preserves (or grows) the ceiling residue. -/
theorem NexusInnovationHOA.generationalRenewal_maintains_ceiling
    {r : Region} (a b : NexusInnovationHOA r) :
    a.generationalRenewal b →
      a.toHOAState.ceilingResidue.val ≤ b.toHOAState.ceilingResidue.val :=
  generationalRenewalMove_maintains_ceiling _ _


-- ════════════════════════════════════════════════════════════════
-- §PS-PA. NEXUS central-lemma binding to §HM30 point-attenuation
-- family (audit synthesis §5.4 PointAttenuationLemma 5-peer echo)
--
-- NEXUS's `contraction_is_antitone_in_adjacent_possible` is the
-- monotone-under-set-restriction shape: for a monotone breadth
-- functional Φ, a contraction (post ⊆ pre) yields Φ post ≤ Φ pre.
-- The witness below binds this to `point_attenuation_monotone`, making
-- explicit that NEXUS's central lemma is an instance of the §HM30
-- family.
-- ════════════════════════════════════════════════════════════════

/-- **NEXUS contraction as §HM30 `point_attenuation_monotone`.** Formal
    witness that the contraction-antitone-in-adjacent-possible result is
    an instance of the §HM30 point-level monotone attenuation family.
    Refactor of the original lemma to take `Monotone Φ` directly rather
    than the unfolded pointwise definition. -/
theorem contraction_as_pointAttenuationMonotone
    {α : Type} {pre post : Set α}
    (h : IsContraction pre post) (Φ : Set α → ℝ) (hΦ : Monotone Φ) :
    Φ post ≤ Φ pre :=
  point_attenuation_monotone Φ hΦ h


-- ════════════════════════════════════════════════════════════════
-- §PS-HM32. NEXUS selection-event discriminant as §HM32
-- `EventDiscriminant` instance (audit synthesis §5.4 ThresholdCrossingEventDiscriminant
-- 2-peer echo).
--
-- NX-G-06 kill-zone extent: `δ = Φ(post) − Φ(pre)`. A selection event
-- (acquisition, funding decision, regulation) maps a pre-set of
-- approaches to a post-set. `δ > 0` classifies expansion (healthy
-- selection); `δ ≤ 0` classifies contraction (kill-zone). This section
-- constructs an `EventDiscriminant` instance whose events are
-- (pre, post) pairs of approach sets, discriminant is `Φ post − Φ pre`,
-- and threshold is 0. The Hill-number breadth functional Φ (NX-G-06)
-- is a parameter --- concrete numeric form is Q4 BIND per NX-G-06.
-- ════════════════════════════════════════════════════════════════

/-- **NEXUS selection-event discriminant as §HM32 EventDiscriminant.**
    Parameterized by the breadth functional Φ. For a (pre, post) pair
    of approach sets, `discriminant = Φ post − Φ pre`; threshold is 0
    (kill-zone boundary). `isAbove` classifies expansion (healthy
    selection); `isAtOrBelow` classifies contraction (kill-zone). -/
def nexusSelectionEventDiscriminant {α : Type} (Φ : Set α → ℝ) :
    EventDiscriminant (Set α × Set α) :=
  { discriminant := fun ev => Φ ev.2 - Φ ev.1
    threshold := 0 }

/-- **NEXUS contraction → EventDiscriminant.isAtOrBelow.** A contraction
    (post ⊆ pre) under monotone Φ maps to at-or-below classification
    (`δ ≤ 0`) in the event-discriminant view --- the formal link between
    NEXUS's §NEXUS-antitone contraction lemma and the §HM32 event
    discriminant. -/
theorem nexusContraction_isAtOrBelow {α : Type} {pre post : Set α}
    (h : IsContraction pre post) (Φ : Set α → ℝ) (hΦ : Monotone Φ) :
    (nexusSelectionEventDiscriminant Φ).isAtOrBelow (pre, post) := by
  unfold EventDiscriminant.isAtOrBelow nexusSelectionEventDiscriminant
  have hle : Φ post ≤ Φ pre :=
    contraction_as_pointAttenuationMonotone h Φ hΦ
  linarith


-- ════════════════════════════════════════════════════════════════
-- §PS-HM35. NEXUS polarity labels (audit synthesis §5.5
-- HealthyVsPathologicalPolarity Joint-abstraction candidate 3)
--
-- NEXUS's `NSAsCartel` (NX-G-05) is described as "self-maintaining
-- but net-information-decreasing" --- the paradigmatic PATHOLOGICAL
-- attractor in the peer family (already Core-promoted as `core:PathologicalAttractor`
-- subclass on the four-peer recurrence). The healthy counterpart is
-- the innovation-ecosystem `InnovationHOA` sustaining paradigm diversity.
-- This section labels NSAsCartel with the §HM35 `Polarity.pathological`
-- classification, formalizing NEXUS's contribution to the joint-abstraction
-- HealthyVsPathologicalPolarity axis.
-- ════════════════════════════════════════════════════════════════

/-- **NSAsCartel polarity label.** NX-G-05 `NSAsCartel` classified as
    `Polarity.pathological`. Formal marker on the §HM35 axis; the
    healthy `InnovationHOA` counterpart carries `Polarity.healthy`. -/
def nsAsCartelPolarity : Polarity := Polarity.pathological

/-- **InnovationHOA (healthy case) polarity label.** The healthy
    counterpart to NSAsCartel on the same §HM35 axis. -/
def innovationHOAHealthyPolarity : Polarity := Polarity.healthy

/-- **The two NEXUS polarities are opposites.** Direct instance of
    `Polarity.opposite`: NSAsCartel and the healthy InnovationHOA sit
    on opposite ends of the §HM35 polarity axis. -/
theorem nsAsCartel_and_healthyHOA_are_opposites :
    nsAsCartelPolarity = innovationHOAHealthyPolarity.opposite := rfl


end SCORE
