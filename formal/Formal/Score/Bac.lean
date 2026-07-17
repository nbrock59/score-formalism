import Formal.Score.Core
import Formal.Score.HOAMaintenance

set_option linter.unusedVariables false
set_option linter.style.whitespace false

/-!
# SCORE.Bac

SCORE-BAC peer: second-order (preservation) lossiness (SS12) and the polity
corpus + preservation interaction on the region structure (SS20).
-/

namespace SCORE

-- ════════════════════════════════════════════════════════════════
-- §12. SCORE-BAC — SECOND-ORDER (PRESERVATION) LOSSINESS
-- The source-criticism layer (SCORE-BAC development-plan item 1). The inscription
-- morphism B₂→B₃ is lossy in a known direction (§4); SCORE-BAC adds a *second*
-- filter: the B₃ corpus that survives to the 2026 researcher is a subset of the
-- B₃ that existed in 1200 BCE, so the set of B₂ states consistent with it can
-- only GROW. Recoverable B₂ information cannot increase under preservation
-- filtering. Formal core of the source-criticism layer
-- (obsidian/SCORE/emergence/applications/SCORE-BAC-SourceCriticism.md; OWL:
-- bac:PreservationFilteredInscription ⊑ core:Inscription).
-- ════════════════════════════════════════════════════════════════

/-- Compatibility: whether a B₂ cognitive state could have produced a given B₃
    inscription — the first-order content-fidelity relation `F`. Abstract. -/
axiom Compatible : CognitiveState → InscriptionContent → Prop

/-- The B₂ states consistent with an observed corpus: those compatible with every
    item in it. A *smaller* set means B₂ is pinned down more tightly — i.e. more
    recoverable information. -/
def consistentB2 (corpus : Set InscriptionContent) : Set CognitiveState :=
  { cs | ∀ ic ∈ corpus, Compatible cs ic }

/-- More evidence pins B₂ down at least as tightly: `consistentB2` is antitone in
    the corpus (more constraints ⇒ the consistent set can only shrink). -/
theorem consistentB2_antitone {C₁ C₂ : Set InscriptionContent}
    (h : C₁ ⊆ C₂) : consistentB2 C₂ ⊆ consistentB2 C₁ := by
  intro cs hcs ic hic
  exact hcs ic (h hic)

/-- A preservation filter: the surviving corpus is a subset of the original B₃
    that existed (fired clay baked in a destruction fire survives; papyrus mostly
    does not). The second-order lossiness the source-criticism layer formalizes. -/
def IsPreservationFilter (original surviving : Set InscriptionContent) : Prop :=
  surviving ⊆ original

/-- **Monotone-lossiness lemma.** Preservation filtering can only ENLARGE the set
    of B₂ states consistent with the evidence: the set recovered from the surviving
    corpus contains the set recovered from the original. Filtering never reduces
    B₂ ambiguity, so it never adds recoverable B₂ information. -/
theorem preservation_filter_loses_b2
    {original surviving : Set InscriptionContent}
    (h : IsPreservationFilter original surviving) :
    consistentB2 original ⊆ consistentB2 surviving :=
  consistentB2_antitone h

/-- Against any antitone information functional (smaller consistent set ⇒ more
    information), recoverable B₂ information from the surviving corpus never exceeds
    that from the original B₃ — the data-processing-style inequality for the
    inscription morphism's second-order (preservation) lossiness. -/
theorem preservation_cannot_increase_b2_information
    {original surviving : Set InscriptionContent}
    (h : IsPreservationFilter original surviving)
    (info : Set CognitiveState → ℝ)
    (hinfo : ∀ {A B : Set CognitiveState}, A ⊆ B → info B ≤ info A) :
    info (consistentB2 surviving) ≤ info (consistentB2 original) :=
  hinfo (preservation_filter_loses_b2 h)


-- ════════════════════════════════════════════════════════════════
-- §20. SCORE-BAC — POLITY CORPUS + PRESERVATION INTERACTION (Q2 SPECIALIZE)
-- Fills the region machinery for the historical/retrodictive peer, and ties it to the
-- §12 preservation filter. DISTINCTIVE: a polity's *intended* corpus is a region
-- (down-closed), but the *surviving* (preservation-filtered) subset need NOT be — a
-- surviving decree whose source record was lost breaks down-closure. That is the
-- source-criticism hazard, now visible on the §14 region structure. OWL: bac:PolityCorpus,
-- bac:derivesFromRecord. See SCORE-BAC-SourceCriticism.md and §12.
-- ════════════════════════════════════════════════════════════════

inductive HistoricalInscription
  | adminRecord | decree
deriving DecidableEq, Repr

axiom bacAsB3 : HistoricalInscription → InscriptionContent

def derivesFromRecord : HistoricalInscription → HistoricalInscription → Bool
  | .adminRecord, .decree => true
  | _,            _       => false

def bacGrade : HistoricalInscription → B3Level
  | .adminRecord => ⟨2, by omega⟩
  | .decree      => ⟨3, by omega⟩

theorem derivesFromRecord_graded : ∀ {x y : HistoricalInscription},
    derivesFromRecord x y = true → bacGrade x ≤ bacGrade y := by
  intro x y h
  cases x <;> cases y <;> first | exact absurd h (by decide) | decide

def bacNetwork : DoctrinalNetwork HistoricalInscription where
  composesFrom x y := derivesFromRecord x y = true
  grade := bacGrade
  grade_mono := derivesFromRecord_graded

def bacPolityCorpus (frontier : Set HistoricalInscription) : Set HistoricalInscription :=
  bacNetwork.downClosure frontier

theorem bacPolityCorpus_isRegion (frontier : Set HistoricalInscription) :
    bacNetwork.IsRegion (bacPolityCorpus frontier) :=
  bacNetwork.downClosure_isRegion frontier

-- **Preservation filtering breaks down-closure (the source-criticism hazard).** The
-- intended polity corpus ↓{decree} = {decree, adminRecord} is a region; but the
-- preservation-filtered survivor {decree} (the source record lost to gradual abandonment)
-- is *not* a region — a surviving decree whose substrate is gone. This is the §12
-- preservation lossiness seen on the §14 region structure.
open HistoricalInscription in
example : ¬ bacNetwork.IsRegion {decree} := by
  intro hreg
  have hc : bacNetwork.composesFrom adminRecord decree := rfl
  have hmem : adminRecord ∈ ({decree} : Set HistoricalInscription) :=
    hreg (Relation.ReflTransGen.single hc) rfl
  rw [Set.mem_singleton_iff] at hmem
  exact absurd hmem (by decide)


-- ════════════════════════════════════════════════════════════════
-- §PS-U2. SCORE-BAC U2 SPECIALIZATION --- PolityCluster as an A-actor-
-- scoped HOAState (Present-Domain → Present-Formal)
--
-- The HM Specialization Audit (`core/bac/SCORE_BAC_HM_Specialization_Audit.md`
-- §1) rated U2 as Present-Domain because BAC-G-01 (`bac:PolityCluster`
-- refining SC-G-26 HumanCommunity) named the HOA analog at the glossary +
-- OWL layer but no Lean specialization instantiated §HM's `HOAState`
-- machinery. This section is that specialization, using M2's Constituent
-- typing.
--
-- BAC's distinctive framing (`SCORE-BAC.md` "retain grain"): individual
-- elite-agent histories are RETAINED, not coalesced. Polity aggregates
-- (Hatti, Ugarit, Egypt, Mycenae) are computed on demand. This maps
-- naturally to `Constituent.AAgent`-scoped subtype of `HOAState`, same
-- shape as `AgoraMaintainingCommunity` and `EthosEpistemicCommunity`,
-- distinct type reflecting BAC's peer-level semantics (retrodictive
-- historical HOA under source-criticism filtering).
-- ════════════════════════════════════════════════════════════════

/-- **SCORE-BAC's `PolityCluster` as an HOAState subtype** (BAC-G-01,
    refining SC-G-26 HumanCommunity). An omega-bounded HOA state whose
    entire population is A-actor elite / administrative agents ---
    captured by the subtype constraint that every constituent is a
    `Constituent.AAgent`. BAC's retain-grain: individual histories are
    preserved at the type layer (not coalesced into a Σ-actor). -/
def BacPolityCluster (r : Region) : Type :=
  { s : HOAState r //
    ∀ c ∈ s.agents, ∃ a : Agent, c = Constituent.AAgent a }

/-- Extract the underlying `HOAState`; §HM machinery inherited via
    this projection. -/
def BacPolityCluster.toHOAState {r : Region}
    (pc : BacPolityCluster r) : HOAState r := pc.1

/-- **A-actor constraint witness.** Every constituent of a BAC polity
    cluster is a `Constituent.AAgent` --- the direct formalization of
    the BAC-G-01 retain-grain claim (elite-agent histories preserved
    individually, not coalesced). -/
theorem BacPolityCluster.agents_are_AAgent {r : Region}
    (pc : BacPolityCluster r) :
    ∀ c ∈ pc.toHOAState.agents, ∃ a : Agent, c = Constituent.AAgent a :=
  pc.2


-- ════════════════════════════════════════════════════════════════
-- §PS-U1. SCORE-BAC U1 SPECIALIZATION --- PolityCluster self-
-- stabilization (Natural → Present-Formal)
--
-- The HM Specialization Audit (`SCORE_BAC_HM_Specialization_Audit.md` §1)
-- rated BAC's U1 as Natural: LBA polities historically exhibited
-- "coherent while alive, then collapsed" behavior --- self-stabilization
-- within a viability set is the natural mechanism account, but BAC does
-- not formalize the maintenance dynamic (it formalizes the source-
-- criticism problem of *studying it after collapse*). This section
-- introduces a peer-scoped self-stabilization abbrev, upgrading BAC's
-- U1 from Natural to Present-Formal by giving the concept a peer-scoped
-- Lean binding on the U2 type `BacPolityCluster`.
--
-- Because BAC's central subject IS the retrodictive study of collapsed
-- polities, the peer's U1 story is dual: what's studied is the
-- retrodiction of when self-stabilization *stopped*, i.e., the
-- Basin-loss event that produced the surviving-corpus subset (see the
-- §12 `preservation_filter_loses_b2` monotone-lossiness result). The
-- retrodictive-side companion of `SelfStabilizingWithin` is future work.
-- ════════════════════════════════════════════════════════════════

/-- **BAC U1: self-stabilization of the polity cluster.** Peer-scoped
    abbrev for `SCORE.SelfStabilizingWithin` on `BacPolityCluster`
    (BAC-G-01). Concrete Basin/Legitimate/Moves peer-specific / Q4 BIND
    against retrodictive historical data. -/
def BacPolityCluster.stabilizesWithin {r : Region}
    (Basin      : BacPolityCluster r → Prop)
    (Legitimate : BacPolityCluster r → Prop)
    (Moves      : BacPolityCluster r → BacPolityCluster r → Prop) : Prop :=
  SelfStabilizingWithin Basin Legitimate Moves


-- ════════════════════════════════════════════════════════════════
-- §PS-U7. SCORE-BAC U7 SPECIALIZATION --- L2 GenerationalRenewalMove
-- (Present-Domain → Present-Formal)
--
-- The HM Specialization Audit (`SCORE_BAC_HM_Specialization_Audit.md` §1)
-- rated BAC's U7 as Present-Domain, load-bearing on L2 specifically:
-- `PolityCorpus` (BAC-G-08) is precisely the mechanism BAC models for
-- L2 GenerationalRenewal --- the graded down-set of the historical-
-- record DAG whose role is generational transmission of inscription
-- across polity lifetimes. `derivesFromRecord` composition ($n$-
-- generation deep down-closure, §20) makes the L2 slow-move explicit
-- as a region-preservation property. This section binds §HM's L2 axiom
-- to `BacPolityCluster` via a peer-scoped wrapper. L1 MemberTurnoverMove
-- and L4 CoInscriptionMove are natural fits per the BAC audit but the
-- retrodictive-historical timescale makes L3 PathAMove awkward; only
-- L2 is bound here.
-- ════════════════════════════════════════════════════════════════

/-- **BAC U7: L2 generational-renewal slow-move on the polity cluster.**
    Peer-scoped wrapper for `GenerationalRenewalMove` on
    `BacPolityCluster`. Peer story: `PolityCorpus`'s
    `derivesFromRecord`-graded down-closure IS the L2 mechanism made
    explicit as a region. -/
def BacPolityCluster.generationalRenewal {r : Region}
    (a b : BacPolityCluster r) : Prop :=
  GenerationalRenewalMove a.toHOAState b.toHOAState

/-- **BAC U7: renewal maintains ceiling.** The §HM26
    `generationalRenewalMove_maintains_ceiling` axiom lifts through the
    peer's projection: successful generational inscription in the polity
    cluster preserves (or grows) the ceiling residue. The formal
    counterpart of BAC's PolityCorpus as an L2 generational-transmission
    mechanism. -/
theorem BacPolityCluster.generationalRenewal_maintains_ceiling
    {r : Region} (a b : BacPolityCluster r) :
    a.generationalRenewal b →
      a.toHOAState.ceilingResidue.val ≤ b.toHOAState.ceilingResidue.val :=
  generationalRenewalMove_maintains_ceiling _ _


-- ════════════════════════════════════════════════════════════════
-- §PS-PA. SCORE-BAC central-lemma binding to §HM30 point-attenuation
-- family (audit synthesis §5.4 PointAttenuationLemma 5-peer echo)
--
-- BAC's SS12 `preservation_filter_loses_b2` is the antitone-under-set-
-- restriction shape: `consistentB2` is antitone (smaller corpus → larger
-- consistent-B₂ set). The witness below binds this to
-- `point_attenuation_antitone`, making explicit that BAC's central
-- lemma is an instance of the §HM30 family. Documentation-only for
-- BAC's verdicts (already Present-Domain / Present-Formal on other
-- cells); establishes the 5-peer PointAttenuation family witness suite.
-- ════════════════════════════════════════════════════════════════

/-- `consistentB2` is `Antitone` on set-inclusion. Direct restatement
    of `consistentB2_antitone` in Mathlib's `Antitone` shape. -/
theorem consistentB2_isAntitone : Antitone consistentB2 :=
  fun _ _ h => consistentB2_antitone h

/-- **BAC SS12 as §HM30 `point_attenuation_antitone`.** Formal witness
    that the monotone-lossiness result is an instance of the §HM30
    point-level antitone attenuation family. -/
theorem ss12_as_pointAttenuationAntitone
    {original surviving : Set InscriptionContent}
    (h : IsPreservationFilter original surviving) :
    consistentB2 original ⊆ consistentB2 surviving :=
  point_attenuation_antitone consistentB2 consistentB2_isAntitone h


end SCORE
