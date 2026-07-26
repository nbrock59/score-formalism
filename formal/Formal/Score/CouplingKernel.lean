import Mathlib

set_option linter.unusedVariables false
set_option linter.style.whitespace false

/-!
# SCORE.CouplingKernel

The coupling graph's edge-formation rule is a **kernel**, not a constant edge
probability: `link(i,j)` depends on `overlap(B₂ᵢ, B₂ⱼ)`, a function of node
attributes. So the governing percolation result is the *inhomogeneous* random
graph theorem (Bollobás–Janson–Riordan 2007), whose criticality condition is
`‖T_κ‖ = 1` — the operator norm of the kernel — rather than Erdős–Rényi's
`mean degree = 1`.

This module supplies the **finite-population** kernel apparatus and proves the
one result that is SCORE's own rather than imported: **subadditivity of the
criticality statistic across the five coupling-weight dimensions**, together
with the tightness witness that makes the corresponding early-warning claim
non-vacuous.

## What is proved vs. imported

* **Proved here.** `spectralNorm_sum_le` (subadditivity), `spectralNorm_smul`,
  `spectralNorm_sum_const` (the bound is *attained* on proportional families),
  and `exists_dimensionwise_subcritical_jointly_supercritical` (the witness).
  These are facts about operator norms; no percolation theory is involved.
* **Imported, not proved.** `bjr_phase_transition` — the giant-component
  characterisation itself. Mathlib has no giant-component theory and no
  multitype branching processes; formalizing BJR is a research programme, not
  a SCORE work item. It is declared as an axiom so that every downstream
  claim's dependence on an imported classical result is visible to
  `#print axioms` rather than silently assumed in prose.

## The SCORE consequence

`no_giant_of_dimensionwise_budget` is a *safety certificate*: if the
per-dimension criticality statistics sum to at most 1, the basin has no giant
component. It is checkable from per-dimension measurements alone.

Its converse fails, and `exists_dimensionwise_subcritical_jointly_supercritical`
proves it fails: **every dimension can be subcritical while the basin is
supercritical.** `spectralNorm_sum_const` locates the worst case — the bound is
attained exactly when the dimensions are *proportional*, i.e. when the same
agents overlap in the same pattern across geographic, professional, origin,
diaspora and institutional coupling. Correlated coupling dimensions are the
dangerous configuration, and measuring each dimension separately is precisely
the practice that misses it.

Note that `IsCouplingKernel` requires symmetry and non-negativity but *not* a
zero diagonal: BJR kernels carry no diagonal restriction (zero-diagonal is a
graph-simplicity convention, not part of the kernel formalism). None of the
norm results below depend on `IsCouplingKernel` at all — it is stated so that
`sum` and non-negative `smul` closure can be checked, and so the witness family
is visibly a legitimate member of the class.

See vault: `obsidian/SCORE/emergence/mechanism/CouplingKernel.md`,
`obsidian/sources/Erdos-Renyi.md`,
`obsidian/SCORE/emergence/mechanism/Manifold.md`,
`obsidian/SCORE/agents/CouplingWeightVector.md`.
-/

namespace SCORE

open Finset

-- ════════════════════════════════════════════════════════════════
-- §CK1. KERNELS AND THE CRITICALITY STATISTIC
-- A coupling kernel over a finite agent population is a symmetric
-- non-negative matrix. Its criticality statistic is the L2 operator norm
-- of the induced endomorphism of Euclidean space -- for a symmetric
-- non-negative kernel this is the Perron-Frobenius leading eigenvalue.
-- ════════════════════════════════════════════════════════════════

/-- A coupling kernel over a finite agent population `V`. `κ i j` is the
    coupling propensity between agents `i` and `j` — in SCORE, a decreasing
    function of the distance between their B₂ manifolds. -/
abbrev CouplingKernel (V : Type*) [Fintype V] := Matrix V V ℝ

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {D : Type*}

/-- Well-formedness: symmetric and non-negative. Deliberately *not* requiring a
    zero diagonal — see the module docstring. -/
def IsCouplingKernel (κ : CouplingKernel V) : Prop :=
  κ.IsSymm ∧ ∀ i j, 0 ≤ κ i j

/-- The endomorphism of Euclidean space induced by a kernel: SCORE's `T_κ`. -/
noncomputable def kernelOp (κ : CouplingKernel V) :
    EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) κ

/-- The criticality statistic `‖T_κ‖`. This is what replaces mean coupling
    density: two basins with equal mean density can have different
    `spectralNorm`, hence sit on opposite sides of the phase transition. -/
noncomputable def spectralNorm (κ : CouplingKernel V) : ℝ := ‖kernelOp κ‖

/-- Above the transition. -/
def Supercritical (κ : CouplingKernel V) : Prop := 1 < spectralNorm κ

/-- At or below the transition. -/
def Subcritical (κ : CouplingKernel V) : Prop := spectralNorm κ ≤ 1

theorem spectralNorm_nonneg (κ : CouplingKernel V) : 0 ≤ spectralNorm κ :=
  norm_nonneg _

-- ════════════════════════════════════════════════════════════════
-- §CK2. WELL-FORMEDNESS IS PRESERVED
-- So that a family of per-dimension kernels sums to a kernel.
-- ════════════════════════════════════════════════════════════════

omit [DecidableEq V] in
theorem IsCouplingKernel.add {κ₁ κ₂ : CouplingKernel V}
    (h₁ : IsCouplingKernel κ₁) (h₂ : IsCouplingKernel κ₂) :
    IsCouplingKernel (κ₁ + κ₂) :=
  ⟨h₁.1.add h₂.1, fun i j => add_nonneg (h₁.2 i j) (h₂.2 i j)⟩

omit [DecidableEq V] in
theorem IsCouplingKernel.smul {c : ℝ} (hc : 0 ≤ c) {κ : CouplingKernel V}
    (h : IsCouplingKernel κ) : IsCouplingKernel (c • κ) := by
  refine ⟨?_, fun i j => mul_nonneg hc (h.2 i j)⟩
  ext i j
  simpa [Matrix.transpose_apply] using congrArg (fun M => c * M i j) h.1.eq

omit [DecidableEq V] in
theorem IsCouplingKernel.sum {s : Finset D} {κ : D → CouplingKernel V}
    (h : ∀ d ∈ s, IsCouplingKernel (κ d)) :
    IsCouplingKernel (∑ d ∈ s, κ d) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Matrix.isSymm_zero, by simp⟩
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih fun d hd => h d (Finset.mem_insert_of_mem hd))

-- ════════════════════════════════════════════════════════════════
-- §CK3. SUBADDITIVITY -- THE RESULT THIS MODULE EXISTS FOR
-- ‖T_{Σ κ_d}‖ ≤ Σ ‖T_{κ_d}‖. The kernel-to-operator map is additive,
-- so this is the triangle inequality transported along it.
-- ════════════════════════════════════════════════════════════════

/-- The kernel-to-operator map is additive over finite sums. -/
theorem kernelOp_sum (s : Finset D) (κ : D → CouplingKernel V) :
    kernelOp (∑ d ∈ s, κ d) = ∑ d ∈ s, kernelOp (κ d) :=
  map_sum (Matrix.toEuclideanCLM (𝕜 := ℝ)) κ s

/-- **Subadditivity of the criticality statistic across coupling dimensions.**

    The basin-level statistic is bounded by the sum of the per-dimension
    statistics. This is what makes per-dimension measurement usable at all:
    it yields a one-sided certificate (see `no_giant_of_dimensionwise_budget`).
    It does *not* yield the converse — see
    `exists_dimensionwise_subcritical_jointly_supercritical`. -/
theorem spectralNorm_sum_le (s : Finset D) (κ : D → CouplingKernel V) :
    spectralNorm (∑ d ∈ s, κ d) ≤ ∑ d ∈ s, spectralNorm (κ d) := by
  unfold spectralNorm
  rw [kernelOp_sum]
  exact norm_sum_le _ _

/-- Scaling a kernel scales its criticality statistic. -/
theorem spectralNorm_smul (c : ℝ) (κ : CouplingKernel V) :
    spectralNorm (c • κ) = |c| * spectralNorm κ := by
  unfold spectralNorm kernelOp
  rw [map_smul, norm_smul, Real.norm_eq_abs]

-- ════════════════════════════════════════════════════════════════
-- §CK4. THE BOUND IS ATTAINED -- PROPORTIONAL DIMENSIONS ARE THE WORST CASE
-- ════════════════════════════════════════════════════════════════

/-- **Tightness.** On a *proportional* family — every dimension a non-negative
    multiple of one shared kernel — the subadditive bound of
    `spectralNorm_sum_le` is attained exactly.

    SCORE reading: when the five coupling dimensions couple the same agents in
    the same pattern, the basin statistic is the full sum of the per-dimension
    statistics, and no cancellation protects the basin. Correlated dimensions
    are the dangerous configuration. -/
theorem spectralNorm_sum_const (s : Finset D) {c : ℝ} (hc : 0 ≤ c)
    (K : CouplingKernel V) :
    spectralNorm (∑ _d ∈ s, c • K) = s.card * (c * spectralNorm K) := by
  have h : (∑ _d ∈ s, c • K) = ((s.card : ℝ) * c) • K := by
    rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  rw [h, spectralNorm_smul, abs_of_nonneg (by positivity)]
  ring

/-- The identity kernel has criticality statistic 1. Used only to discharge
    existence in `exists_dimensionwise_subcritical_jointly_supercritical`;
    the content is carried by `spectralNorm_sum_const`, which applies to any
    kernel — including zero-diagonal ones. -/
theorem spectralNorm_one [Nonempty V] :
    spectralNorm (1 : CouplingKernel V) = 1 := by
  unfold spectralNorm kernelOp
  rw [map_one]
  exact ContinuousLinearMap.norm_id

/-- **The converse of the certificate fails.** There is a five-dimension
    family of well-formed coupling kernels, every one of them subcritical,
    whose basin-level sum is supercritical.

    This is the early-warning claim, and it is a warning about a *measurement
    practice*: confirming that each coupling dimension is separately below
    threshold does not establish that the basin is below threshold. -/
theorem exists_dimensionwise_subcritical_jointly_supercritical
    (V : Type*) [Fintype V] [DecidableEq V] [Nonempty V] :
    ∃ κ : Fin 5 → CouplingKernel V,
      (∀ d, IsCouplingKernel (κ d)) ∧
      (∀ d, Subcritical (κ d)) ∧
      Supercritical (∑ d, κ d) := by
  refine ⟨fun _ => (1 / 2 : ℝ) • (1 : CouplingKernel V), ?_, ?_, ?_⟩
  · intro d
    exact IsCouplingKernel.smul (by norm_num)
      ⟨Matrix.isSymm_one, fun i j => by
        rcases eq_or_ne i j with h | h <;> simp [Matrix.one_apply, h]⟩
  · intro d
    change spectralNorm ((1 / 2 : ℝ) • (1 : CouplingKernel V)) ≤ 1
    rw [spectralNorm_smul, spectralNorm_one]
    norm_num
  · change 1 < spectralNorm (∑ _d : Fin 5, (1 / 2 : ℝ) • (1 : CouplingKernel V))
    rw [spectralNorm_sum_const _ (by norm_num), spectralNorm_one]
    norm_num

-- ════════════════════════════════════════════════════════════════
-- §CK5. THE IMPORTED PERCOLATION RESULT
-- Declared, not proved. Mathlib has no giant-component theory. Keeping
-- this as an explicit axiom means `#print axioms` on any downstream
-- theorem shows the dependence on an imported classical result.
-- ════════════════════════════════════════════════════════════════

/-- Opaque: the coupling graph sampled from `κ` has a giant component (a
    connected component containing a positive fraction of `V`). Not defined
    here — defining it requires the percolation apparatus this module
    deliberately does not build. -/
axiom HasGiantComponent {V : Type*} [Fintype V] [DecidableEq V] :
    CouplingKernel V → Prop

/-- **Bollobás–Janson–Riordan (2007), *The phase transition in inhomogeneous
    random graphs*. Imported, not proved.**

    A giant component emerges exactly when the kernel's operator norm exceeds
    1. Erdős–Rényi is the special case `κ ≡ c`, where `‖T_κ‖ = c` and the
    condition collapses to the familiar `c = 1`.

    Consistency is immediate: interpret `HasGiantComponent` as `Supercritical`. -/
axiom bjr_phase_transition {V : Type*} [Fintype V] [DecidableEq V]
    (κ : CouplingKernel V) : HasGiantComponent κ ↔ Supercritical κ

/-- **The safety certificate.** If the per-dimension criticality statistics sum
    to at most 1, the basin has no giant component.

    Checkable from per-dimension measurements alone, and this *is* the sound
    direction — unlike the per-dimension maximum, which is not
    (`exists_dimensionwise_subcritical_jointly_supercritical`). -/
theorem no_giant_of_dimensionwise_budget (s : Finset D) (κ : D → CouplingKernel V)
    (h : ∑ d ∈ s, spectralNorm (κ d) ≤ 1) :
    ¬ HasGiantComponent (∑ d ∈ s, κ d) := by
  rw [bjr_phase_transition]
  exact not_lt.mpr (le_trans (spectralNorm_sum_le s κ) h)

end SCORE
