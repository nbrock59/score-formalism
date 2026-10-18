import Formal.Score.Core

/-!
# SCORE.CoreModel — a concrete model of Core's opaque spine (D3)

`Core.lean` posits eight opaque carrier types (nine until 2026-10-18, when `Event`
became a structure) and asserts axioms over them. Nothing showed
those axioms were **jointly satisfiable**, and an inconsistent axiom set makes every
theorem resting on it vacuously true — 179 theorems build, and that fact alone does not
distinguish "proved" from "proved from a contradiction".

This module exhibits a model: concrete types, concrete definitions, and each axiom
re-stated about them and proved. If it compiles, Core's opaque spine is consistent.

## Why a parallel module rather than an instantiation

A Lean `axiom` is opaque and cannot be instantiated. So a model is necessarily a separate
structure whose shape mirrors the axioms — the correspondence is by inspection, name for
name, which is why every theorem below is named after the axiom it models.

## What this DOES and does not establish

* **Does**: Core's carrier axioms and the Prop-axioms stated purely over them are jointly
  satisfiable. No contradiction hides in that set.
* **Does not**: say the axioms are *right*. A model shows consistency, never adequacy.
* **Out of scope**: `studentDominated_subcritical`. It quantifies over `CouplingKernel`
  and `Subcritical` — real Mathlib-backed structures, not opaque carriers — so its
  satisfiability is a question about spectral norms rather than about carrier choice, and
  a model of the opaque spine cannot speak to it. Recorded rather than silently skipped.

## The result worth reading: which axioms survive a ONE-POINT model

The interesting output is not "consistent" but **which axioms force the model to be
bigger than a single point**. An axiom satisfied by the trivial model constrains nothing;
that is the shape `Core.lean` deleted `rhythmLowersSeedSize` for ("trivially satisfiable
… a vacuous axiom laundering an untested hypothesis").

Collapse every carrier to `Unit`, every predicate to `True`, `perceptDist` to `0`, and:

| axiom | one-point model |
|---|---|
| `stratificationConstraint` | **satisfied** — `IsStable ≡ True` discharges it |
| `perceptDist_nonneg/_self/_comm` | **satisfied** — `0` is a pseudometric |
| `inscription_carried` | **satisfied** — the single mark carries everything |
| `carrier_multiply_realizable` | **FAILS** — needs two distinct marks |
| `mark_without_content` | **FAILS** — needs a mark carrying nothing |
| `mark_localized` | **FAILS** — needs a second world state, where the mark is absent |
| `event_localized` | *a theorem* (events are changes of state); a one-point world has no events |

Only `carrier_multiply_realizable`, `mark_without_content` and `mark_localized` have content
in this sense. The first two were added 2026-09-12 with exactly that job: they are what makes
B₃ "realized without being reduced" say something. `mark_localized` (2026-10-18) makes marks
features of **one** world. Events need no axiom: `Event` is a structure (a change of world
state), so the model below builds it from `World` rather than choosing it. The rest
are satisfiable by a structure that asserts nothing — which is not a defect (a
pseudometric axiom *should* admit the zero metric) but is worth knowing before treating
any of them as an empirical commitment.

`ModelIsNonTrivial` below records this as a checked fact rather than a claim in prose.
-/

namespace SCORE.CoreModel

-- ════════════════════════════════════════════════════════════════
-- §M1. CARRIERS — concrete choices for Core's eight opaque types
-- Each is the smallest type that keeps the axioms below satisfiable.
-- `B1Mark` is `Fin 3` and not `Unit` because §M3 forces it; see the header.
-- `World` is `Bool` and not `Unit` because `mark_localized` forces two states.
-- `Event` is not chosen here: Core defines it from `World` (a change of state); see §M5.
-- ════════════════════════════════════════════════════════════════

abbrev Agent := Fin 2
abbrev World := Bool
abbrev InscriptionContent := Bool
abbrev CognitiveState := Bool
abbrev SigmaActor := Unit
abbrev B1Mark := Fin 3
abbrev Region := Unit
abbrev Percept := Unit

-- ════════════════════════════════════════════════════════════════
-- §M2. THE STRATIFICATION CONSTRAINT
-- `IsStable ≡ True` satisfies it. That is the point of the table in the
-- header: this axiom does not force the model to be anything.
-- ════════════════════════════════════════════════════════════════

def IsStable (_ : Stratum) : Prop := True

theorem stratificationConstraint :
    ∀ (s : Stratum) (h : 0 < s.val), IsStable s → IsStable (s.predecessor h) := by
  intro _ _ _; trivial

-- ════════════════════════════════════════════════════════════════
-- §M3. B₁ REALIZATION — the axioms that DO force structure
-- Mark 0 and mark 1 both carry `true`; mark 2 carries nothing.
-- Two distinct carriers of one content, and one mark that is mere matter.
-- ════════════════════════════════════════════════════════════════

def carriedBy (c : InscriptionContent) (m : B1Mark) : Prop :=
  (c = true ∧ (m = 0 ∨ m = 1)) ∨ (c = false ∧ m = 0)

/-- Totality: no B₃ token without a B₁ realization. -/
theorem inscription_carried : ∀ c, ∃ m, carriedBy c m := by
  intro c; cases c
  · exact ⟨0, Or.inr ⟨rfl, rfl⟩⟩
  · exact ⟨0, Or.inl ⟨rfl, Or.inl rfl⟩⟩

/-- Multiple realizability — the Rosetta case. UNSATISFIABLE at one point. -/
theorem carrier_multiply_realizable :
    ∃ (c : InscriptionContent) (m₁ m₂ : B1Mark),
      m₁ ≠ m₂ ∧ carriedBy c m₁ ∧ carriedBy c m₂ :=
  ⟨true, 0, 1, by decide, Or.inl ⟨rfl, Or.inl rfl⟩, Or.inl ⟨rfl, Or.inr rfl⟩⟩

/-- B₁ necessary, not sufficient: some marks are mere patterned matter.
    UNSATISFIABLE at one point. -/
theorem mark_without_content : ∃ m : B1Mark, ∀ c, ¬ carriedBy c m := by
  refine ⟨2, ?_⟩
  intro c h
  rcases h with ⟨_, h2 | h2⟩ | ⟨_, h2⟩ <;> exact absurd h2 (by decide)

/-- Marks are present in the `true` state and absent from the `false` one. -/
def markIn (_ : B1Mark) (w : World) : Prop := w = true

/-- Marks are localized in the world. UNSATISFIABLE in a one-point world. -/
theorem mark_localized : ∀ m : B1Mark, (∃ w : World, markIn m w) ∧ (∃ w : World, ¬ markIn m w) :=
  fun _ => ⟨⟨true, rfl⟩, ⟨false, by simp [markIn]⟩⟩

/-- Realization without reduction, derived here exactly as in `Core.lean`. -/
theorem b3_not_reducible_to_carrier :
    ¬ (∀ (c : InscriptionContent) (m₁ m₂ : B1Mark),
         carriedBy c m₁ → carriedBy c m₂ → m₁ = m₂) := by
  intro h
  obtain ⟨c, m₁, m₂, hne, h₁, h₂⟩ := carrier_multiply_realizable
  exact hne (h c m₁ m₂ h₁ h₂)

-- ════════════════════════════════════════════════════════════════
-- §M4. MORPHISMS AND THE DEPTH GATE
-- Definitional axioms: a model needs only SOME total function of the right
-- type. That they are easy to satisfy is the content of calling them
-- `definitional` rather than `empirical`.
-- ════════════════════════════════════════════════════════════════

def SufficientDepth (_ : Agent) : Prop := True

def perception (_ : World) (_ : Agent) : CognitiveState := true
def action (_ : Agent) (_ : CognitiveState) (w : World) : World := w
def inscribe (_ : Agent) (cs : CognitiveState) : InscriptionContent := cs
def incorporate (ic : InscriptionContent) (_ : Agent) : CognitiveState := ic
def inscribeB1Ref (_ : Agent) (cs : CognitiveState) : InscriptionContent := cs
def inscribeB2Ref (a : Agent) (_ : SufficientDepth a) (cs : CognitiveState) :
    InscriptionContent := cs

/-- The normative change chain composes in the model, as it does in `Core.lean`. -/
theorem normativeChangeChain (a : Agent) (cs : CognitiveState) (w : World) :
    ∃ w' : World, w' = action a (incorporate (inscribe a cs) a) w :=
  ⟨_, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- §M5. PERCEPT AND ITS PSEUDOMETRIC
-- The zero metric satisfies all three laws. Worth noticing: these axioms
-- admit a model in which every percept is at distance 0 from every other,
-- i.e. in which the perceptual-bifurcation claim has no content. They
-- constrain `perceptDist` to be a pseudometric and nothing more.
-- ════════════════════════════════════════════════════════════════

/-- Core's `Event`, rebuilt over this model's `World`: a change of state. Not a modelling
    choice (Core defines it), so it is mirrored, not chosen. -/
structure Event where
  before : World
  after : World
  changes : before ≠ after

def perceptualFilter (_ : Event) (_ : CouplingWeightVector) : Percept := ()
def perceptDist (_ _ : Percept) : ℝ := 0


theorem perceptDist_nonneg : ∀ p q, 0 ≤ perceptDist p q := by
  intro _ _; unfold perceptDist; norm_num
theorem perceptDist_self : ∀ p, perceptDist p p = 0 := by intro _; rfl
theorem perceptDist_comm : ∀ p q, perceptDist p q = perceptDist q p := by intro _ _; rfl

-- ════════════════════════════════════════════════════════════════
-- §M6. NON-TRIVIALITY, AS A CHECKED FACT
-- The header claims the B₁-realization axioms force a model with at least
-- two marks and a contentless one. Rather than assert that, exhibit it.
-- ════════════════════════════════════════════════════════════════

/-- The model's mark type is genuinely larger than a point, and it has to be:
    `carrier_multiply_realizable` needs two distinct marks carrying one content, and
    `mark_without_content` needs a third carrying none. A one-point model satisfies
    every other axiom in this file and fails exactly these two. -/
theorem ModelIsNonTrivial :
    (∃ m₁ m₂ : B1Mark, m₁ ≠ m₂) ∧ (∃ m : B1Mark, ∀ c, ¬ carriedBy c m) :=
  ⟨⟨0, 1, by decide⟩, mark_without_content⟩

/-- And the collapse is not available: no one-point mark type can satisfy both. Stated
    over an arbitrary `Subsingleton` carrier so it is a fact about the axioms, not about
    `Fin 3`. -/
theorem no_one_point_model {M : Type} [Subsingleton M]
    (cb : InscriptionContent → M → Prop)
    (h_multi : ∃ (c : InscriptionContent) (m₁ m₂ : M), m₁ ≠ m₂ ∧ cb c m₁ ∧ cb c m₂) :
    False := by
  obtain ⟨_, m₁, m₂, hne, _, _⟩ := h_multi
  exact hne (Subsingleton.elim m₁ m₂)

end SCORE.CoreModel
