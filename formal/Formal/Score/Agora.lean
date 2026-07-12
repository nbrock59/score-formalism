import Formal.Score.Core

set_option linter.unusedVariables false
set_option linter.style.whitespace false

/-!
# SCORE.Agora

AGORA peer: the captured-correction impossibility lemma (SS13) and the
legal-precedent network binding (SS17).
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


end SCORE
