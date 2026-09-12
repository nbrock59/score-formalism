import Formal.Score.Core
-- §22b needs the B₃ provenance markers (`IsTelosBearing`, `IsLossFunction`) and their
-- disjointness, which live in Sigma.lean §25. Added 2026-09-12: the telos vocabulary
-- and the contestability theorems were in the same build and had never met.
import Formal.Score.Sigma

set_option linter.unusedVariables false
set_option linter.style.whitespace false

/-!
# SCORE.InscriptionMarket

Inscription-market peer: FA1-FA4 verification conditions VC-IL-1..5 for the
'Inscription Layer as Market Power' working paper (SS21).
-/

namespace SCORE

-- ════════════════════════════════════════════════════════════════
-- §21. INSCRIPTION-MARKET — FA1–FA4 VERIFICATION CONDITIONS
-- Formal additions for "The Inscription Layer as Market Power: What Hayek Missed"
-- (Brock, 2026). Five verification conditions (VC-IL-1 through VC-IL-5) form
-- the traceable spine of the working paper's argument.
--
-- FA1: Second-order perception (π²)
-- FA2: Inscription topology as owned infrastructure (Τ_ι)
-- FA3: Perceptibility thresholds and sub-threshold steering
-- FA4: Inscription coverage cliff (κ*)
--
-- OWL: score-inscription-market.owl (DL-expressible fragment)
-- Vault: morphisms/SecondOrderPerception.md, domains/InscriptionTopology.md,
--        agents/PerceptibilityThreshold.md,
--        emergence/mechanism/InscriptionCoverageCliff.md
-- Status: developing (2026-06-29). Axioms are genuine design constraints.
-- ════════════════════════════════════════════════════════════════

-- ── FA2: Inscription topology ──────────────────────────────────

/-- An inscription channel in the market. -/
axiom Channel : Type

/-- The ownership function Ω: maps a channel to its controlling agent,
    or Nothing if the channel is unowned (public/commons). -/
axiom ownership : Channel → Option Agent

/-- The read-access resolution function R: how much of the inscriptions
    flowing through a channel are legible to a given agent. 0 = opaque,
    1 = full resolution. -/
axiom readAccess : Agent → Channel → CouplingWeight

/-- Coupling opacity (new concept, not a redefinition): quantifies how much
    of the coupling between two agents is visible to an observer, derived
    from the inscription topology. -/
axiom couplingOpacity : Agent → Agent → CouplingWeight

-- ── FA1: Second-order perception ───────────────────────────────

/-- Whether an agent has second-order perception capacity (π²).
    Structural, not intrinsic — depends on inscription topology ownership. -/
axiom HasSecondOrderPerception : Agent → Prop

/-- The second-order perception morphism: reconstructs other agents'
    cognitive states from their B₃ traces at the resolution granted by R.
    The composite chain: agents inscribe (B₂→B₃), platform reads B₃,
    platform reconstructs B₂ states. -/
axiom secondOrderPerceive : (a : Agent) → HasSecondOrderPerception a →
    Agent → CognitiveState

-- ── FA3: Perceptibility thresholds ─────────────────────────────

/-- The perceptibility threshold δ for an agent: minimum magnitude of B₁
    change registrable by the agent across the SHARED -> INDEXED direction
    given current manifold grain -- the resolution floor on BOTH B2-input
    morphisms, Perception (B1->B2) and Incorporation (B3->B2). Related to but
    distinct from the percept filter (§8): the filter determines WHAT
    registers; δ determines the MINIMUM MAGNITUDE that registers at all.

    Scope corrected 2026-07-18 (audit re-run). This docstring previously said
    "B1 modification ... perception morphism", which was narrower than the
    type: `Modification` is abstract, so nothing here ever restricted δ to
    B1-sourced change -- and the vault was already applying it to B3-delivered
    steering (IncorporationAsymmetry § "The two-threshold structure").
    DomainTrichotomy § Cardinality licenses the wider reading: the percept and
    incorporation filters are ONE mechanism on the two shared sources, and δ is
    that filter's magnitude axis. No proof changes -- VC-IL-2, VC-DI-1/2/3 and
    Theorems DI-A/DI-B are stated over generic `Modification` and are
    unaffected. -/
axiom perceptibilityThreshold : Agent → CouplingWeight

-- ── FA4: Inscription coverage ──────────────────────────────────

/-- Inscription coverage κ(a): fraction of market transactions whose B₃
    records are accessible to agent a at sufficient resolution for π². -/
axiom inscriptionCoverage : Agent → CouplingWeight

/-- The cliff threshold κ*: above this, second-order perception becomes
    self-reinforcing through a positive-sign morphism cycle. -/
axiom kappaStar : CouplingWeight

-- ── VC-IL-1: FA2 enables FA1 ──────────────────────────────────
-- Ownership of a channel with full read access implies second-order
-- perception is well-defined.

axiom vc_il_1 :
    ∀ (a : Agent) (c : Channel),
      ownership c = some a →
      readAccess a c = CouplingWeight.one →
      HasSecondOrderPerception a

-- ── VC-IL-2: FA1 enables FA3 ──────────────────────────────────
-- Second-order perception enables calibration of sub-threshold
-- modifications: for any first-order agent, there exists a B₁
-- modification below their perceptibility threshold.

/-- A change whose magnitude is compared against the perceptibility threshold.
    Deliberately abstract: ranges over B1-sourced modification (the action
    instantiation) AND B3-delivered content change (the incorporation
    instantiation) alike, since δ is a resolution floor on the shared ->
    indexed direction, not on one source domain. (Docstring corrected
    2026-07-18: previously read "A B₁ modification magnitude", which described
    one instantiation as though it were the type.) -/
axiom Modification : Type
axiom modificationMagnitude : Modification → CouplingWeight

/-- The B₃ content a modification delivers — its *provenance* handle, as
    `modificationMagnitude` is its amplitude handle. Added 2026-09-12 for §22b: with
    magnitude as the only observable, §22 could express the amplitude route to
    non-contestability and no other. This is what makes the provenance route
    *expressible*; it does not by itself make it true. -/
axiom modificationContent : Modification → InscriptionContent

axiom vc_il_2 :
    ∀ (platform : Agent),
      HasSecondOrderPerception platform →
      ∀ (target : Agent),
        ¬ HasSecondOrderPerception target →
        ∃ (m : Modification),
          modificationMagnitude m ≤ perceptibilityThreshold target

-- ── VC-IL-3: Self-reinforcing above κ* ────────────────────────
-- Above the cliff threshold, inscription coverage is self-reinforcing:
-- the rate of coverage change is positive.

/-- The rate of change of inscription coverage (simplified to a sign). -/
axiom coverageGrowthRate : Agent → ℝ

axiom vc_il_3 :
    ∀ (a : Agent),
      kappaStar.val < (inscriptionCoverage a).val →
      0 < coverageGrowthRate a

-- ── VC-IL-4: Symmetric Τ_ι → no π² ───────────────────────────
-- The Hayekian baseline: when no agent owns any channel, second-order
-- perception is not available to anyone.

axiom vc_il_4 :
    (∀ (c : Channel), ownership c = none) →
    ∀ (a : Agent), ¬ HasSecondOrderPerception a

-- ── VC-IL-5: Common carrier revokes π² ────────────────────────
-- Restructuring Ω to null (common carrier doctrine) revokes second-order
-- perception going-forward.

axiom vc_il_5 :
    ∀ (a : Agent),
      (∀ (c : Channel), ownership c ≠ some a) →
      ¬ HasSecondOrderPerception a

-- ── Consistency check: VC-IL-4 and VC-IL-1 compose correctly ──
-- Under symmetric Τ_ι (VC-IL-4), no agent can satisfy the premise of
-- VC-IL-1 (ownership c = some a), so the two are consistent.

theorem vc_il_4_and_1_consistent :
    (∀ (c : Channel), ownership c = none) →
    ∀ (a : Agent) (c : Channel),
      ownership c = some a → False := by
  intro h_sym a c h_own
  have h := h_sym c
  simp [h_own] at h


-- ════════════════════════════════════════════════════════════════
-- §22. DELIBERATION INVERSION — VC-DI-1..3
-- Formal spine for the second (companion) paper: the deliberation
-- inversion. Same formal root as FA1–FA4 (asymmetric Τ_ι), applied to
-- the canonical *democratic* argument instead of the Hayekian one.
--
-- Claim: deliberative legitimacy assumes influence travels through
-- perceptible, contestable exchange — an argument can be answered.
-- Sub-threshold, individually calibrated influence cannot be contested
-- because it cannot be perceived. The capstone theorem composes VC-IL-2
-- (the market paper's sub-threshold-steering result) with the
-- contestability-requires-perceptibility axiom to show a platform can
-- steer a first-order agent non-contestably.
--
-- Vault: morphisms/IncorporationAsymmetry.md (§ "The deliberation inversion")
-- Status: developing (2026-07-06). Axioms are design constraints; the two
-- theorems are proved from them.
-- ════════════════════════════════════════════════════════════════

/-- Whether an agent can perceive a B₁ modification at all (the percept
    machinery registering it, given its perceptibility threshold δ). -/
axiom canPerceive : Agent → Modification → Prop

/-- Whether an agent can *contest* a modification: challenge, answer, or
    hold to account the influence it represents. The deliberative act. -/
axiom canContest : Agent → Modification → Prop

-- ── VC-DI-1: Contestability requires perceptibility ───────────────
-- The load-bearing premise of the inversion: you cannot contest an
-- influence you cannot perceive. Deliberation presupposes perception.

axiom vc_di_1 :
    ∀ (a : Agent) (m : Modification),
      canContest a m → canPerceive a m

-- ── VC-DI-2: Sub-threshold modifications are imperceptible ────────
-- A modification at or below the agent's perceptibility threshold δ does
-- not register. (Same ≤-form as VC-IL-2, so the two compose directly.)

axiom vc_di_2 :
    ∀ (a : Agent) (m : Modification),
      modificationMagnitude m ≤ perceptibilityThreshold a →
      ¬ canPerceive a m

-- ── VC-DI-3: Perceptibility restoration (the remedy) ──────────────
-- Forcing a modification above δ (intervention-grade disclosure of
-- personalization) makes it perceivable — the "inequality flip on δ".
-- NOTE: this restores perceptibility, hence the *necessary* condition
-- for contestation (VC-DI-1). Whether perceived influence is in fact
-- contested depends on deliberative institutions and is deliberately
-- NOT formalized here — the remedy is necessary, not proven sufficient.

axiom vc_di_3 :
    ∀ (a : Agent) (m : Modification),
      (perceptibilityThreshold a).val < (modificationMagnitude m).val →
      canPerceive a m

-- ── Theorem DI-A: sub-threshold ⇒ non-contestable ────────────────
-- The core derived result of the inversion (proved, not assumed).
-- Model-checked as a DTMC in `formal/prism/MediatedChannel.sm` (PRISM): while the
-- steering amplitude stays below the perceptibility threshold it reaches the
-- manifold with probability 1 and is never contested (DI-A); lowering the
-- threshold below the amplitude — the DI-B disclosure remedy — flips
-- contestability. See `obsidian/SCORE/methodology/ModelCheckedDynamics.md`.

theorem di_subthreshold_noncontestable :
    ∀ (a : Agent) (m : Modification),
      modificationMagnitude m ≤ perceptibilityThreshold a →
      ¬ canContest a m := by
  intro a m h_sub h_contest
  exact (vc_di_2 a m h_sub) (vc_di_1 a m h_contest)

-- ── Theorem DI-B (capstone): platform steering is non-contestable ─
-- Composes VC-IL-2 (market paper: a platform with π² can find a
-- sub-threshold modification for any first-order target) with Theorem
-- DI-A. This is the formal content of "same root, second inversion":
-- the FA machinery of the first paper yields the democratic harm of the
-- second. For any platform with second-order perception and any target
-- without it, there is a modification the target cannot contest.

theorem di_platform_steering_noncontestable :
    ∀ (platform : Agent), HasSecondOrderPerception platform →
    ∀ (target : Agent), ¬ HasSecondOrderPerception target →
    ∃ (m : Modification), ¬ canContest target m := by
  intro platform h_platform target h_target
  obtain ⟨m, h_sub⟩ := vc_il_2 platform h_platform target h_target
  exact ⟨m, di_subthreshold_noncontestable target m h_sub⟩


-- ════════════════════════════════════════════════════════════════
-- §22b. THE PROVENANCE ROUTE — VC-DI-4 (added 2026-09-12)
-- §22 defeats contestation through *amplitude*: the steering sits below δ, so it
-- cannot be perceived, so it cannot be contested (DI-A), and the remedy is to push
-- it above δ (VC-DI-3).
--
-- VC-DI-3's own note already concedes that remedy is "necessary, not proven
-- sufficient", and attributes the residue to "deliberative institutions" — a
-- contingent, sociological gap. This section records a *second* occupant of that
-- gap which is not sociological and not fixable by stronger institutions: content
-- bearing no telos has no party to the contest (SC-G-23, `LossFunctionContent`:
-- "not correctable — no telos, and no party to the contest").
--
-- The two routes are independent. DI-A's is a claim about magnitude; this one is a
-- claim about provenance, and `di_disclosure_insufficient` below exhibits a
-- modification that is fully perceptible and still non-contestable — so restoring
-- perceptibility cannot be the whole remedy.
--
-- Vault: morphisms/IncorporationAsymmetry.md (§ "The deliberation inversion")
-- Status: developing (2026-09-12). As in §22, axioms are design constraints and the
-- theorems are proved from them.
-- ════════════════════════════════════════════════════════════════

-- ── VC-DI-4: Contestability requires a telos-bearing counterparty ──
-- The second necessary condition, alongside VC-DI-1. To contest is to challenge,
-- answer, or hold to account — which presupposes something that *bears* a telos to
-- be held to account. This is the contestation-side reading of the Σ/Ω content
-- contrast in Sigma.lean §25, and it is deliberately stated as a *necessary*
-- condition only: like VC-DI-1 it says what contestation requires, never what
-- suffices for it.

axiom vc_di_4 :
    ∀ (a : Agent) (m : Modification),
      canContest a m → IsTelosBearing (modificationContent m)

-- ── Theorem DI-C: loss-function content is non-contestable ────────
-- Derived, exactly as DI-A is derived from VC-DI-1 + VC-DI-2: here from VC-DI-4
-- plus the §25 disjointness. Note what is absent from the statement — any
-- hypothesis about magnitude. This holds at every amplitude.

theorem di_lossfunction_noncontestable :
    ∀ (a : Agent) (m : Modification),
      IsLossFunction (modificationContent m) →
      ¬ canContest a m := by
  intro a m h_lf h_contest
  exact (telos_lossfunction_disjoint _ h_lf) (vc_di_4 a m h_contest)

-- ── Theorem DI-D: the disclosure remedy is not sufficient ─────────
-- The payoff. VC-DI-3 restores perceptibility by forcing a modification above δ.
-- For loss-function content that leaves it *perceptible and still non-contestable*,
-- which is a counterexample to reading VC-DI-3 as a complete remedy rather than as
-- the necessary condition its own note says it is.
--
-- This does not weaken DI-A or DI-B: both remain true on the amplitude route. It
-- bounds the *remedy*, not the results.

theorem di_disclosure_insufficient :
    ∀ (a : Agent) (m : Modification),
      (perceptibilityThreshold a).val < (modificationMagnitude m).val →
      IsLossFunction (modificationContent m) →
      canPerceive a m ∧ ¬ canContest a m := by
  intro a m h_supra h_lf
  exact ⟨vc_di_3 a m h_supra, di_lossfunction_noncontestable a m h_lf⟩


end SCORE
