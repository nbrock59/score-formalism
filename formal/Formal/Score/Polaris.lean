import Formal.Score.Core

set_option linter.unusedVariables false
set_option linter.style.whitespace false

/-!
# SCORE.Polaris

POLARIS peer: the political-doctrine network binding of the SS14 region
machinery (SS18).
-/

namespace SCORE

-- ════════════════════════════════════════════════════════════════
-- §18. POLARIS — POLITICAL-DOCTRINE NETWORK BOUND TO §14 (Q2 SPECIALIZE)
-- Fills the region machinery for the flagship peer. Regions index over GEOGRAPHIC
-- communities (polaris:GeographicCommunity) — R(C) on the bounded-but-valid geographic
-- projection. Chain civicNorm ⊳ policy ⊳ ideology. OWL: polaris:CommunityCorpus,
-- polaris:invokesNorm. See HOA.md, PeerImplementations.md (POLARIS row).
-- ════════════════════════════════════════════════════════════════

inductive PoliticalInscription
  | civicNorm | policy | ideology
deriving DecidableEq, Repr

axiom polarisAsB3 : PoliticalInscription → InscriptionContent

def invokesNorm : PoliticalInscription → PoliticalInscription → Bool
  | .civicNorm, .policy   => true
  | .policy,    .ideology => true
  | _,          _         => false

def polarisGrade : PoliticalInscription → B3Level
  | .civicNorm => ⟨2, by omega⟩
  | .policy    => ⟨3, by omega⟩
  | .ideology  => ⟨4, by omega⟩

theorem invokesNorm_graded : ∀ {x y : PoliticalInscription},
    invokesNorm x y = true → polarisGrade x ≤ polarisGrade y := by
  intro x y h
  cases x <;> cases y <;> first | exact absurd h (by decide) | decide

def polarisNetwork : DoctrinalNetwork PoliticalInscription where
  composesFrom x y := invokesNorm x y = true
  grade := polarisGrade
  grade_mono := invokesNorm_graded

def polarisCorpus (frontier : Set PoliticalInscription) : Set PoliticalInscription :=
  polarisNetwork.downClosure frontier

theorem polarisCorpus_isRegion (frontier : Set PoliticalInscription) :
    polarisNetwork.IsRegion (polarisCorpus frontier) :=
  polarisNetwork.downClosure_isRegion frontier

-- A geographic community's ideology holds its civic-norm substrate.
open PoliticalInscription in
example : civicNorm ∈ polarisCorpus {ideology} := by
  refine ⟨ideology, rfl, ?_⟩
  have h1 : polarisNetwork.composesFrom civicNorm policy := rfl
  have h2 : polarisNetwork.composesFrom policy ideology := rfl
  exact (Relation.ReflTransGen.single h1).tail h2


-- ── SEWI: the n = 3 instance of the generic spectral EWS (Core §SP) ──
-- polaris:SEWI SPECIALIZEs core:SpectralEarlyWarningIndicator: the Φ oral-social trace
-- with three critical-slowing-down signatures (low-frequency variance, lag-1
-- autocorrelation, spectral-centroid downshift). The concrete weights (0.45,0.35,0.20;
-- Segment 6 §6.2) and the signature computations are Q4 BIND (src/polaris/spectral/sewi.py);
-- the theorem needs only that the weights are nonnegative. See MeasurementMetrics.md.

/-- POLARIS SEWI as the n = 3 instance of the generic `spectralEWS`: `w` the three (nonnegative)
    signature weights, `s` the three normalized critical-slowing-down signatures. -/
def polarisSEWI (w s : Fin 3 → ℝ) : ℝ := spectralEWS w s

/-- **POLARIS SEWI monotonicity** — the n = 3 instance of `spectral_ews_monotone`: SEWI is
    nondecreasing in each of its three signatures. SEWI's first formal verification condition
    (the Gate-5 test in test_sewi enforces it on `compute_sewi`). -/
theorem polarisSEWI_monotone (w : Fin 3 → ℝ) (hw : ∀ i, 0 ≤ w i)
    (s s' : Fin 3 → ℝ) (hss : ∀ i, s i ≤ s' i) :
    polarisSEWI w s ≤ polarisSEWI w s' :=
  spectral_ews_monotone w hw s s' hss


end SCORE
