import Formal.Score.Core

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


end SCORE
