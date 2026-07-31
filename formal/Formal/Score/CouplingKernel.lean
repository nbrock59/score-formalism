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
-- §CK5. THE IMPORTED PERCOLATION RESULT -- OVER A SEQUENCE
-- Declared, not proved. Mathlib has no giant-component theory.
--
-- Retyped 2026-07-26. The first version declared
--   HasGiantComponent : CouplingKernel V -> Prop
-- over a *fixed finite* V. That was mistyped: BJR is asymptotic ("All our
-- results are asymptotic" -- BJR S3), and on a fixed V every component is
-- trivially Theta(1) of the population, so the predicate had no faithful
-- reading and the axiom asserted nothing. It is now a statement about a
-- sequence, and `HasGiantComponent` is *defined* rather than opaque.
-- ════════════════════════════════════════════════════════════════

open Filter Topology

/-- A family of finite populations indexed by scale, with population growing
    without bound.

    This is the part of BJR's **vertex space** that SCORE's statement needs.
    BJR's is richer: a ground space `(𝒮, μ)` with `μ` a Borel probability
    measure, plus a sequence of random point sets `𝐱_n` subject to
    empirical-measure convergence `ν_n(A) →ᵖ μ(A)` on every `μ`-continuity
    set. Recording that in full would require the measure-theoretic apparatus
    this module deliberately does not build; what is kept is the indexing by
    scale, which is the feature whose absence made the old axiom vacuous. -/
structure PopulationSequence where
  Pop        : ℕ → Type
  fin        : ∀ n, Fintype (Pop n)
  dec        : ∀ n, DecidableEq (Pop n)
  /-- The population grows without bound — the `n → ∞` of BJR's statement. -/
  card_atTop : Tendsto (fun n => Fintype.card (Pop n)) atTop atTop

attribute [instance] PopulationSequence.fin PopulationSequence.dec

/-- A **kernel sequence** over a population family: a kernel at each scale,
    together with the limit of its criticality statistic.

    BJR states the condition on the *limit* kernel `κ` of a graphical sequence
    `(κ_n)`; since SCORE only ever consumes `‖T_κ‖`, the limit is recorded at
    the level of the statistic. `norm_tendsto` is what a graphical sequence
    buys you, assumed rather than derived. -/
structure KernelSequence (P : PopulationSequence) where
  kernel       : ∀ n, CouplingKernel (P.Pop n)
  /-- `lim_n ‖T_{κ_n}‖` — BJR's `‖T_κ‖` for the limit kernel. -/
  limitNorm    : ℝ
  norm_tendsto : Tendsto (fun n => spectralNorm (kernel n)) atTop (𝓝 limitNorm)

namespace KernelSequence

variable {P : PopulationSequence}

/-- Above the transition, in the limit. -/
def Supercritical (K : KernelSequence P) : Prop := 1 < K.limitNorm

/-- At or below the transition, in the limit. -/
def Subcritical (K : KernelSequence P) : Prop := K.limitNorm ≤ 1

/-- Opaque: the order of the largest component of the graph sampled from
    `K.kernel n`. SCORE does not model the sampling, so this is the one place
    the probabilistic layer is abstracted away — BJR's conclusions hold *whp*,
    and that quantifier is not represented here. -/
axiom largestComponentOrder : KernelSequence P → ℕ → ℕ

/-- **Giant component**, asymptotically: the largest component eventually
    contains at least a fixed positive fraction of the population.

    This is BJR's `C₁ = Θ(n)`. Unlike the superseded opaque predicate this has
    content — it is a genuine `Θ(n)` lower bound along the sequence, and is not
    satisfied by every kernel. -/
def HasGiantComponent (K : KernelSequence P) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop,
    c * (Fintype.card (P.Pop n) : ℝ) ≤ (largestComponentOrder K n : ℝ)

/-- Sanity check that the retype bought something. The superseded
    `HasGiantComponent` was an opaque `Prop` pinned only by the axiom, so it had
    no consequences of its own. This one does: a giant component forces the
    largest component to be eventually non-empty, derived from the definition
    without appeal to `bjr_phase_transition`. -/
theorem HasGiantComponent.eventually_pos (K : KernelSequence P)
    (h : K.HasGiantComponent) : ∀ᶠ n in atTop, 0 < largestComponentOrder K n := by
  obtain ⟨c, hc, hev⟩ := h
  have hcard : ∀ᶠ n in atTop, 0 < Fintype.card (P.Pop n) :=
    P.card_atTop.eventually_gt_atTop 0
  filter_upwards [hev, hcard] with n hn hcn
  have : (0 : ℝ) < c * (Fintype.card (P.Pop n) : ℝ) :=
    mul_pos hc (by exact_mod_cast hcn)
  exact_mod_cast this.trans_le hn

end KernelSequence

/-- **Bollobás–Janson–Riordan (2007), *The phase transition in inhomogeneous
    random graphs*, RSA 31(1):3–122, Theorem 3.1. Imported, not proved.**

    A giant component emerges exactly when the limiting operator norm exceeds
    1. Erdős–Rényi is the special case `κ ≡ c`, where `‖T_κ‖ = c` and the
    condition collapses to the familiar `c = 1`.

    **What this statement abstracts, and should not be mistaken for.** BJR's
    Theorem 3.1 requires a graphical *sequence* `(κ_n)` on a vertex space, and
    concludes `C₁ = Θ(n)` **whp**, with the sharper `C₁/n →ᵖ ρ(κ)` under
    quasi-irreducibility, where `ρ(κ)` is the survival probability of a
    multi-type Poisson Galton–Watson process. Neither the probability space nor
    `ρ(κ)` is represented here. So this axiom is *weaker and coarser* than
    Theorem 3.1 — it is the corollary SCORE consumes, not the theorem.

    Note also that `‖T_κ‖` is an **operator norm**, not in general an attained
    eigenvalue; the two coincide when `T_κ` is compact (`∬κ² < ∞`, BJR
    Prop. 17.3) or under BJR (3.11). See `BJRDischarge.md` § 2.

    Consistency: interpret `largestComponentOrder K n := Fintype.card (P.Pop n)`
    when `K.Supercritical` and `0` otherwise. -/
axiom bjr_phase_transition {P : PopulationSequence} (K : KernelSequence P) :
    K.HasGiantComponent ↔ K.Supercritical

/-- **The safety certificate, over a sequence.** If the per-dimension limiting
    criticality statistics sum to at most 1, the basin has no giant component.

    `J` is *given* as the dimension-wise sum rather than constructed: the sum of
    kernel sequences is not canonically a kernel sequence, because `‖T_{Σκ_d}‖`
    need not converge just because each `‖T_{κ_d}‖` does. Taking convergence of
    the sum as a hypothesis is the honest form.

    Checkable from per-dimension measurements alone, and this *is* the sound
    direction — unlike the per-dimension maximum, which is not
    (`exists_dimensionwise_subcritical_jointly_supercritical`). -/
theorem no_giant_of_dimensionwise_budget {P : PopulationSequence} {D : Type*}
    (s : Finset D) (K : D → KernelSequence P) (J : KernelSequence P)
    (hJ : ∀ n, J.kernel n = ∑ d ∈ s, (K d).kernel n)
    (hbudget : ∑ d ∈ s, (K d).limitNorm ≤ 1) :
    ¬ J.HasGiantComponent := by
  rw [bjr_phase_transition]
  have hsum : Tendsto (fun n => ∑ d ∈ s, spectralNorm ((K d).kernel n)) atTop
      (𝓝 (∑ d ∈ s, (K d).limitNorm)) :=
    tendsto_finset_sum _ fun d _ => (K d).norm_tendsto
  have hle : J.limitNorm ≤ ∑ d ∈ s, (K d).limitNorm := by
    refine le_of_tendsto_of_tendsto' J.norm_tendsto hsum fun n => ?_
    rw [hJ n]
    exact spectralNorm_sum_le s (fun d => (K d).kernel n)
  exact not_lt.mpr (hle.trans hbudget)

-- ════════════════════════════════════════════════════════════════
-- §CK6. THE FINITE-TYPE CONTRACT -- PLANTED PARTITION
-- The closed forms `src/score/coupling.py` returns as theory constants,
-- proved against `spectralNorm` (BJR Mechanism Amendment Proposal §6,
-- "hoist" row, 2026-07-31): the Python generator/estimator and these
-- theorems are the two faces of the same finite-type kernel. `B` blocks
-- of equal measure 1/B with within-intensity `w` and between-intensity
-- `b` induce the type-level operator matrix with diagonal `w/B` and
-- off-diagonal `b/B`; its operator norm is the Perron value
-- `(w + (B-1)·b)/B`. The `b = w` slice is Erdős–Rényi, where the value
-- collapses to the mean-coupling scalar -- the validity domain of
-- rung-1 summaries like `Core.lean`'s `aggregateLocalWeight`.
-- ════════════════════════════════════════════════════════════════

/-- Coordinates of the operator: `T_κ` acts by row-times-vector. -/
theorem kernelOp_apply_coord (κ : CouplingKernel V) (x : EuclideanSpace ℝ V)
    (i : V) : kernelOp κ x i = ∑ j, κ i j * x j := rfl

/-- The kernel-to-operator map is additive (binary form of `kernelOp_sum`). -/
theorem kernelOp_add (κ₁ κ₂ : CouplingKernel V) :
    kernelOp (κ₁ + κ₂) = kernelOp κ₁ + kernelOp κ₂ :=
  map_add (Matrix.toEuclideanCLM (𝕜 := ℝ)) κ₁ κ₂

/-- The all-ones kernel: unit coupling propensity between every pair. -/
def onesKernel (V : Type*) [Fintype V] : CouplingKernel V :=
  Matrix.of fun _ _ => (1 : ℝ)

omit [DecidableEq V] in
theorem onesKernel_isCouplingKernel : IsCouplingKernel (onesKernel V) :=
  ⟨by ext i j; simp [onesKernel], fun _ _ => zero_le_one⟩

/-- The criticality statistic of the all-ones kernel is the population size:
    attained on the constant vector, bounded above by Cauchy–Schwarz. -/
theorem spectralNorm_onesKernel [Nonempty V] :
    spectralNorm (onesKernel V) = (Fintype.card V : ℝ) := by
  classical
  have hB0 : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  have happly : ∀ (x : EuclideanSpace ℝ V) (i : V),
      kernelOp (onesKernel V) x i = ∑ j, x j := by
    intro x i
    rw [kernelOp_apply_coord]
    simp [onesKernel]
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ hB0.le fun x => ?_
    have hsq : ‖kernelOp (onesKernel V) x‖ ^ 2
        ≤ ((Fintype.card V : ℝ) * ‖x‖) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      have hcs : (∑ j, x j) ^ 2 ≤ (Fintype.card V : ℝ) * ∑ j, (x j) ^ 2 := by
        simpa using
          sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j : V => x j)
      calc ∑ i, (kernelOp (onesKernel V) x i) ^ 2
          = (Fintype.card V : ℝ) * (∑ j, x j) ^ 2 := by
            simp [happly x, Finset.sum_const, nsmul_eq_mul]
        _ ≤ (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) * ∑ j, (x j) ^ 2) :=
            mul_le_mul_of_nonneg_left hcs hB0.le
        _ = ((Fintype.card V : ℝ) * ‖x‖) ^ 2 := by
            rw [mul_pow, EuclideanSpace.real_norm_sq_eq]; ring
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq
  · -- attained on the constant vector
    set u : EuclideanSpace ℝ V := (WithLp.toLp 2) (fun _ : V => (1 : ℝ)) with hu
    have hui : ∀ i : V, u i = 1 := fun _ => rfl
    have hunorm : ‖u‖ = Real.sqrt (Fintype.card V : ℝ) := by
      rw [EuclideanSpace.norm_eq]
      simp [hui]
    have hupos : 0 < ‖u‖ := by
      rw [hunorm]
      exact Real.sqrt_pos.mpr hB0
    have hTu : kernelOp (onesKernel V) u = (Fintype.card V : ℝ) • u := by
      ext i
      rw [happly u i]
      simp [hui]
    have h := (kernelOp (onesKernel V)).le_opNorm u
    rw [hTu, norm_smul, Real.norm_eq_abs, abs_of_nonneg hB0.le] at h
    exact le_of_mul_le_mul_right h hupos

/-- The finite-type planted-partition kernel over a `B = |V|`-type ground
    space of equal block measures: within-intensity `w`, between-intensity
    `b`, so the type-level operator entry is `w/B` on the diagonal and `b/B`
    off it. `src/score/coupling.py::planted_partition_intensities` samples
    graphs from exactly this kernel. -/
noncomputable def plantedPartitionKernel (V : Type*) [Fintype V] [DecidableEq V]
    (w b : ℝ) : CouplingKernel V :=
  Matrix.of fun i j =>
    if i = j then w / (Fintype.card V : ℝ) else b / (Fintype.card V : ℝ)

theorem plantedPartitionKernel_isCouplingKernel {w b : ℝ}
    (hw : 0 ≤ w) (hb : 0 ≤ b) :
    IsCouplingKernel (plantedPartitionKernel V w b) := by
  constructor
  · ext i j
    by_cases h : i = j <;> simp [plantedPartitionKernel, h, eq_comm]
  · intro i j
    dsimp [plantedPartitionKernel]
    split <;> positivity

/-- Decomposition into the two kernels whose norms are already known. -/
theorem plantedPartitionKernel_eq (w b : ℝ) :
    plantedPartitionKernel V w b
      = ((w - b) / (Fintype.card V : ℝ)) • (1 : CouplingKernel V)
        + (b / (Fintype.card V : ℝ)) • onesKernel V := by
  ext i j
  rcases eq_or_ne i j with h | h
  · subst h
    simp only [plantedPartitionKernel, onesKernel, Matrix.of_apply, if_true,
      Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul]
    ring
  · simp only [plantedPartitionKernel, onesKernel, Matrix.of_apply, if_neg h,
      Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne h, smul_eq_mul]
    ring

/-- **The finite-type contract.** For `0 ≤ b ≤ w` the criticality statistic
    of the planted-partition kernel is its Perron value `(w + (B-1)·b)/B`:
    bounded above by subadditivity over the decomposition, attained on the
    constant vector. This is the closed form
    `src/score/coupling.py::planted_partition_spectral_norm` returns; the
    generator and the estimator meet in this equation. -/
theorem spectralNorm_plantedPartition [Nonempty V] {w b : ℝ}
    (hb : 0 ≤ b) (hbw : b ≤ w) :
    spectralNorm (plantedPartitionKernel V w b)
      = (w + ((Fintype.card V : ℝ) - 1) * b) / (Fintype.card V : ℝ) := by
  classical
  have hB0 : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  have hBne : (Fintype.card V : ℝ) ≠ 0 := hB0.ne'
  have hwb : (0 : ℝ) ≤ w - b := sub_nonneg.mpr hbw
  -- the row sum every coordinate of the constant vector sees
  have hrow : ∀ i : V, ∑ j, plantedPartitionKernel V w b i j
      = (w + ((Fintype.card V : ℝ) - 1) * b) / (Fintype.card V : ℝ) := by
    intro i
    have hsplit : ∑ j, plantedPartitionKernel V w b i j
        = w / (Fintype.card V : ℝ)
          + ((Fintype.card V : ℝ) - 1) * (b / (Fintype.card V : ℝ)) := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
      have h1 : plantedPartitionKernel V w b i i = w / (Fintype.card V : ℝ) := by
        simp [plantedPartitionKernel]
      have h2 : ∑ j ∈ Finset.univ.erase i, plantedPartitionKernel V w b i j
          = ((Fintype.card V : ℝ) - 1) * (b / (Fintype.card V : ℝ)) := by
        have hval : ∀ j ∈ Finset.univ.erase i, plantedPartitionKernel V w b i j
            = b / (Fintype.card V : ℝ) := by
          intro j hj
          have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
          simp [plantedPartitionKernel, hij]
        rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul,
            Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
            Nat.cast_sub Fintype.card_pos, Nat.cast_one]
      rw [h1, h2]
    rw [hsplit, add_div, mul_div_assoc]
  refine le_antisymm ?_ ?_
  · -- subadditive upper bound over the decomposition
    rw [plantedPartitionKernel_eq]
    have hadd : spectralNorm
        (((w - b) / (Fintype.card V : ℝ)) • (1 : CouplingKernel V)
          + (b / (Fintype.card V : ℝ)) • onesKernel V)
        ≤ spectralNorm (((w - b) / (Fintype.card V : ℝ)) • (1 : CouplingKernel V))
          + spectralNorm ((b / (Fintype.card V : ℝ)) • onesKernel V) := by
      unfold spectralNorm
      rw [kernelOp_add]
      exact norm_add_le _ _
    refine hadd.trans ?_
    rw [spectralNorm_smul, spectralNorm_smul, spectralNorm_one,
        spectralNorm_onesKernel,
        abs_of_nonneg (div_nonneg hwb hB0.le),
        abs_of_nonneg (div_nonneg hb hB0.le)]
    have hR : w + ((Fintype.card V : ℝ) - 1) * b
        = (w - b) + (Fintype.card V : ℝ) * b := by ring
    rw [mul_one, div_mul_cancel₀ _ hBne, hR, add_div,
        mul_div_cancel_left₀ _ hBne]
  · -- attained on the constant vector
    set lam : ℝ := (w + ((Fintype.card V : ℝ) - 1) * b) / (Fintype.card V : ℝ)
      with hlam
    have hlam0 : 0 ≤ lam := by
      have h1 : (1 : ℝ) ≤ (Fintype.card V : ℝ) := by
        exact_mod_cast Fintype.card_pos
      have hnum : (0 : ℝ) ≤ w + ((Fintype.card V : ℝ) - 1) * b := by nlinarith
      exact div_nonneg hnum hB0.le
    set u : EuclideanSpace ℝ V := (WithLp.toLp 2) (fun _ : V => (1 : ℝ)) with hu
    have hui : ∀ i : V, u i = 1 := fun _ => rfl
    have hunorm : ‖u‖ = Real.sqrt (Fintype.card V : ℝ) := by
      rw [EuclideanSpace.norm_eq]
      simp [hui]
    have hupos : 0 < ‖u‖ := by
      rw [hunorm]
      exact Real.sqrt_pos.mpr hB0
    have hTu : kernelOp (plantedPartitionKernel V w b) u = lam • u := by
      ext i
      rw [kernelOp_apply_coord]
      have hcoord : ∑ j, plantedPartitionKernel V w b i j * u j
          = ∑ j, plantedPartitionKernel V w b i j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hui j, mul_one]
      rw [hcoord, hrow i]
      simp [hui]
    have h := (kernelOp (plantedPartitionKernel V w b)).le_opNorm u
    rw [hTu, norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam0] at h
    exact le_of_mul_le_mul_right h hupos

/-- **Rung-1 collapse -- the validity domain of scalar summaries.** On the
    homogeneous slice `b = w = c` (the Erdős–Rényi slice: every intensity
    equal), the spectral statistic *is* the mean-coupling scalar `c`. This is
    exactly where density summaries like `Core.lean`'s `aggregateLocalWeight`
    read criticality correctly; off this slice the general value
    `(w + (B-1)·b)/B` decouples from mean density
    (`exists_dimensionwise_subcritical_jointly_supercritical` is the
    multi-dimension face of the same decoupling). -/
theorem spectralNorm_plantedPartition_er_slice [Nonempty V] {c : ℝ}
    (hc : 0 ≤ c) :
    spectralNorm (plantedPartitionKernel V c c) = c := by
  have hB0 : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [spectralNorm_plantedPartition hc le_rfl, div_eq_iff hB0.ne']
  ring

end SCORE
