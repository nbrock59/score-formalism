import Formal.Score.Core
import Formal.Score.HOAMaintenance

set_option linter.unusedVariables false
set_option linter.style.whitespace false

/-!
# SCORE.Agora

AGORA peer: the captured-correction impossibility lemma (SS13), the
legal-precedent network binding (SS17), and the maintenance-bridge
(§HM-Bridge) restating SS13 in the population/predicate vocabulary of
`HOAMaintenance` (Hook 3, §HM22) with an honest delta comment on why
the two are analogous but not formally reducible at this tier.
-/

namespace SCORE

-- ── AGORA: captured-only correction cannot reach zero mismatch ──
-- The proof-side of the AGORA∩ATLAS core:CollectiveManifoldUpdate promotion.
-- (AGORA-CollectiveManifoldUpdate.md Phase B; OWL agora:CapturedCorrectionUpdate ⊑
-- core:CollectiveManifoldUpdate.)

/-- The residual mismatch reachable by correcting through a node is bounded below by
    that node's own mismatch floor (a node cannot correct below its own drift). -/
def reachableMismatch (nodeFloor : ℝ) : ℝ := nodeFloor

/-- **AGORA impossibility.** If the available correcting node is captured (its own
    mismatch floor is at least a positive `floor`), the reachable mismatch is nonzero:
    zero mismatch is unreachable without an independent (zero-floor) node. -/
theorem captured_correction_needs_independent_node
    {floor nodeFloor : ℝ} (hfloor : 0 < floor) (hcap : floor ≤ nodeFloor) :
    reachableMismatch nodeFloor ≠ 0 := by
  unfold reachableMismatch
  exact (lt_of_lt_of_le hfloor hcap).ne'


-- ════════════════════════════════════════════════════════════════
-- §17. AGORA — LEGAL-PRECEDENT NETWORK BOUND TO §14 (Q2 SPECIALIZE)
-- Fills the now-core `DoctrinalNetwork`/region machinery for the constitutional peer.
-- AGORA is the most *literal* down-closure in the family: under stare decisis a holding
-- legally *requires* its precedential/constitutional substrate, not merely references it.
-- A diamond DAG (constitution ⊳ statute, precedent; statute, precedent ⊳ doctrine).
-- Region-bearer: agora:InstitutionalMaintainingCommunity. OWL: agora:DoctrinalCorpus,
-- agora:citesAuthority. See AGORA.md.
-- ════════════════════════════════════════════════════════════════

inductive LegalInscription
  | constitution | statute | precedent | doctrine
deriving DecidableEq, Repr

axiom agoraAsB3 : LegalInscription → InscriptionContent

def citesAuthority : LegalInscription → LegalInscription → Bool
  | .constitution, .statute   => true
  | .constitution, .precedent => true
  | .statute,      .doctrine  => true
  | .precedent,    .doctrine  => true
  | _,             _          => false

def agoraGrade : LegalInscription → B3Level
  | .constitution => ⟨2, by omega⟩
  | .statute      => ⟨3, by omega⟩
  | .precedent    => ⟨3, by omega⟩
  | .doctrine     => ⟨4, by omega⟩

theorem citesAuthority_graded : ∀ {x y : LegalInscription},
    citesAuthority x y = true → agoraGrade x ≤ agoraGrade y := by
  intro x y h
  cases x <;> cases y <;> first | exact absurd h (by decide) | decide

def agoraNetwork : DoctrinalNetwork LegalInscription where
  composesFrom x y := citesAuthority x y = true
  grade := agoraGrade
  grade_mono := citesAuthority_graded

def agoraCorpus (frontier : Set LegalInscription) : Set LegalInscription :=
  agoraNetwork.downClosure frontier

theorem agoraCorpus_isRegion (frontier : Set LegalInscription) :
    agoraNetwork.IsRegion (agoraCorpus frontier) :=
  agoraNetwork.downClosure_isRegion frontier

/-- **Stare-decisis down-closure (witness).** A body of doctrine holds the constitution
    as substrate — reachable through statute (or, symmetrically, precedent: the diamond). -/
example : LegalInscription.constitution ∈ agoraCorpus {LegalInscription.doctrine} := by
  refine ⟨LegalInscription.doctrine, rfl, ?_⟩
  have h1 : agoraNetwork.composesFrom LegalInscription.constitution LegalInscription.statute := rfl
  have h2 : agoraNetwork.composesFrom LegalInscription.statute LegalInscription.doctrine := rfl
  exact (Relation.ReflTransGen.single h1).tail h2


-- ════════════════════════════════════════════════════════════════
-- §HM-Bridge. AGORA MAINTENANCE-BRIDGE — restating SS13 in the
-- population/predicate vocabulary of Hook 3 (`HOAMaintenance` §HM22).
--
-- Purpose: make visible in Lean the correspondence between AGORA's SS13
-- `captured_correction_needs_independent_node` impossibility lemma and
-- the abstract `hoaFragilityHomogeneous` fragility theorem, WITHOUT
-- overclaiming a formal reduction that does not hold at this tier.
--
-- What lands here:
--   1. `AgoraCorrectingNode` opaque type + `nodeFloorOf` association
--      axiom — the AGORA-side analog of §HM22's `Agent` +
--      `agentCouplingWeightVector`.
--   2. `PopulationCorrectingNodeCaptured` predicate — the AGORA-side
--      sibling of §HM22's `PopulationCouplingHomogeneous`, structurally
--      parallel but scoped to a functional role (correcting nodes)
--      rather than the whole agent population.
--   3. `populationCaptured_reachableMismatch_nonzero` — a trivial
--      reformulation of SS13 in the new vocabulary, giving Hook-3-shaped
--      access to the AGORA impossibility.
--
-- What does NOT land here (deliberately):
--
-- A formal derivation of SS13 from `hoaFragilityHomogeneous`. Both
-- capture the intuition "uniformity along a specific axis prevents the
-- maintenance mechanism from operating", but at different formal levels:
--
--   * `captured_correction_needs_independent_node` is a POINT-LEVEL
--     ARITHMETIC BOUND: `nodeFloor > 0 → reachableMismatch ≠ 0`. A
--     single-state claim about what a given node configuration can
--     achieve.
--
--   * `hoaFragilityHomogeneous` is a TRACE-LEVEL DYNAMICS CLAIM:
--     `PopulationCouplingHomogeneous s → ∀ trace ∀ i, ¬ feedbackEngaged`.
--     A statement about how a homogeneous population's history must
--     evolve.
--
-- A reduction would require either
--   (a) a *partial-homogeneity* variant of Hook 3 predicating over a
--       functional role (correcting nodes) rather than all agents, or
--   (b) an abstract *structural-fragility* theorem that both impossi-
--       bility claims are instances of.
-- Neither exists at this tier; both are candidate future formalizations.
-- Until then, the correspondence is REAL but DOCUMENTED, not DERIVED.
--
-- Spec-side counterpart: `core/agora/AGORA_Interface_Contracts.md`
-- §6 (SCORE Maintenance Machinery Mapping). Cross-ref: `agora:CapturedCorrec-
-- tionUpdate` (OWL), Hook 3 (SC-G-58, `AgentHomogeneityFragility`).
-- ════════════════════════════════════════════════════════════════

/-- AGORA-side opaque type for the correcting-node role. Analog of the
    `Agent` type consumed by §HM22's `agentCouplingWeightVector`. -/
axiom AgoraCorrectingNode : Type

/-- Each AGORA correcting node has a `nodeFloor` in the reals (the
    residual mismatch it *cannot* correct below — its own drift).
    Analog of §HM22's `agentCouplingWeightVector`. -/
axiom nodeFloorOf : AgoraCorrectingNode → ℝ

/-- **Population-side captured predicate.** All correcting nodes in a
    given set are captured: their floors are all at least a common
    positive `floor`. Sibling of §HM22's `PopulationCouplingHomogeneous`
    (structurally parallel; scoped to the correcting-node role rather
    than the whole agent population). -/
def PopulationCorrectingNodeCaptured
    (floor : ℝ) (nodes : Set AgoraCorrectingNode) : Prop :=
  0 < floor ∧ ∀ n ∈ nodes, floor ≤ nodeFloorOf n

/-- **Bridge restatement of SS13.** For a captured population of
    correcting nodes, every node's reachable mismatch is nonzero — no
    route to zero exists among the captured nodes. Trivial lift of SS13
    over `PopulationCorrectingNodeCaptured`, giving the AGORA
    impossibility a Hook-3-shaped statement (population predicate →
    universal impossibility over its members). -/
theorem populationCaptured_reachableMismatch_nonzero
    {floor : ℝ} {nodes : Set AgoraCorrectingNode}
    (h : PopulationCorrectingNodeCaptured floor nodes) :
    ∀ n ∈ nodes, reachableMismatch (nodeFloorOf n) ≠ 0 :=
  fun n hn => captured_correction_needs_independent_node h.1 (h.2 n hn)


end SCORE
