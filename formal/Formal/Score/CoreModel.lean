import Formal.Score.Core

/-!
# SCORE.CoreModel — a concrete model of Core's opaque spine (D3)

`Core.lean` posits seven opaque carrier types (nine until 2026-10-18, when `Event`
and `B1Mark` became structures) and asserts axioms over them. Nothing showed
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
| `b1_has_own_dynamics` | **FAILS** — a one-point world's only step is the identity |
| `event_localized`, `mark_localized` | *theorems* (defined over `World`) |

Only `carrier_multiply_realizable`, `mark_without_content` and `b1_has_own_dynamics` have
content in this sense. The first two were added 2026-09-12 with exactly that job: they are
what makes B₃ "realized without being reduced" say something. `b1_has_own_dynamics`
(2026-10-18) says B₁ changes with no agent in it. Events and marks need no axiom: both are
structures built from `World` (a real transition; a feature made by one), so the model below
mirrors them rather than choosing them. The rest
are satisfiable by a structure that asserts nothing — which is not a defect (a
pseudometric axiom *should* admit the zero metric) but is worth knowing before treating
any of them as an empirical commitment.

`ModelIsNonTrivial` below records this as a checked fact rather than a claim in prose.
-/

namespace SCORE.CoreModel

-- ════════════════════════════════════════════════════════════════
-- §M1. CARRIERS — concrete choices for Core's seven opaque types
-- Each is the smallest type that keeps the axioms below satisfiable.
-- `World` is `Fin 3` with a cyclic step: §M3 needs three distinct marks, and a mark is made
-- by an event, so the world needs three distinct transitions. `Event` and `B1Mark` are not
-- chosen here: Core defines both from `World`; see §M1b.
-- ════════════════════════════════════════════════════════════════

abbrev Agent := Fin 2
abbrev World := Fin 3
abbrev InscriptionContent := Bool
abbrev CognitiveState := Bool
abbrev SigmaActor := Unit
abbrev Region := Unit
abbrev Percept := Unit

-- ════════════════════════════════════════════════════════════════
-- §M1b. B₁ DYNAMICS, EVENTS AND MARKS — Core's § 4d, mirrored
-- The step cycles 0 → 1 → 2 → 0, so every state moves: `b1_has_own_dynamics` holds, and it
-- FAILS in a one-point world. `action` is the identity (agents change nothing here), so every
-- event in this model is natural, which is exactly what Core now permits.
-- ════════════════════════════════════════════════════════════════

def b1Step (w : World) : World := w + 1

/-- B₁ changes on its own. UNSATISFIABLE in a one-point world. -/
theorem b1_has_own_dynamics : ∃ w : World, b1Step w ≠ w := ⟨0, by decide⟩

def action (_ : Agent) (_ : CognitiveState) (w : World) : World := w

def Transition (w w' : World) : Prop :=
  w' = b1Step w ∨ ∃ (a : Agent) (cs : CognitiveState), w' = action a cs w

/-- Core's `Event`, mirrored over this model's `World`. -/
structure Event where
  before : World
  after : World
  changes : before ≠ after
  transition : Transition before after

/-- Core's `B1Mark`, mirrored: a feature made by an event. -/
structure B1Mark where
  madeBy : Event
  feature : World → Prop
  present : feature madeBy.after
  absent : ¬ feature madeBy.before

theorem step_ne (i : World) : i ≠ b1Step i := by revert i; decide

/-- The natural event starting at `i`, and the mark it makes (the state `i + 1` holding). -/
def stepEvent (i : World) : Event := ⟨i, b1Step i, step_ne i, Or.inl rfl⟩
def mk (i : World) : B1Mark := ⟨stepEvent i, fun w => w = b1Step i, rfl, step_ne i⟩

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
-- The marks made at states 0 and 1 both carry `true`; the one made at 2 carries nothing.
-- Two distinct carriers of one content, and one mark that is mere matter.
-- ════════════════════════════════════════════════════════════════

def carriedBy (c : InscriptionContent) (m : B1Mark) : Prop :=
  (c = true ∧ (m.madeBy.before = 0 ∨ m.madeBy.before = 1)) ∨
    (c = false ∧ m.madeBy.before = 0)

/-- Totality: no B₃ token without a B₁ realization. -/
theorem inscription_carried : ∀ c, ∃ m, carriedBy c m := by
  intro c; cases c
  · exact ⟨mk 0, Or.inr ⟨rfl, rfl⟩⟩
  · exact ⟨mk 0, Or.inl ⟨rfl, Or.inl rfl⟩⟩

theorem mk_ne : mk 0 ≠ mk 1 := by
  intro h
  have h' := congrArg (fun m : B1Mark => m.madeBy.before) h
  exact absurd h' (by decide)

/-- Multiple realizability — the Rosetta case. UNSATISFIABLE at one point. -/
theorem carrier_multiply_realizable :
    ∃ (c : InscriptionContent) (m₁ m₂ : B1Mark),
      m₁ ≠ m₂ ∧ carriedBy c m₁ ∧ carriedBy c m₂ :=
  ⟨true, mk 0, mk 1, mk_ne, Or.inl ⟨rfl, Or.inl rfl⟩, Or.inl ⟨rfl, Or.inr rfl⟩⟩

/-- B₁ necessary, not sufficient: some marks are mere patterned matter.
    UNSATISFIABLE at one point. -/
theorem mark_without_content : ∃ m : B1Mark, ∀ c, ¬ carriedBy c m := by
  refine ⟨mk 2, ?_⟩
  intro c h
  rcases h with ⟨_, h2 | h2⟩ | ⟨_, h2⟩ <;> exact absurd h2 (by decide)

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
-- `action` is defined in §M1b, because `Transition` (and so `Event`) needs it.
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
  ⟨⟨mk 0, mk 1, mk_ne⟩, mark_without_content⟩

/-- And the collapse is not available: no one-point mark type can satisfy both. Stated
    over an arbitrary `Subsingleton` carrier so it is a fact about the axioms, not about
    this model's marks. -/
theorem no_one_point_model {M : Type} [Subsingleton M]
    (cb : InscriptionContent → M → Prop)
    (h_multi : ∃ (c : InscriptionContent) (m₁ m₂ : M), m₁ ≠ m₂ ∧ cb c m₁ ∧ cb c m₂) :
    False := by
  obtain ⟨_, m₁, m₂, hne, _, _⟩ := h_multi
  exact hne (Subsingleton.elim m₁ m₂)

end SCORE.CoreModel
