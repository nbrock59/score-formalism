/-
  SCORE_B3_Context.lean — structural sketch (Lean 4 core, no Mathlib)

  B₃ as a context-tracking structure. Every inscription is a pair
  ⟨context, content⟩. A context is other inscriptions (recursion inside B₃)
  and/or anchors (exits from B₃ into B₁/B₂ via the morphisms).

  Design claims encoded here:
  1. B₃ cannot ground itself: every chain must reach an anchor (Gödel, structurally).
  2. Well-foundedness is kind-dependent: formal/descriptive/procedural
     inscriptions must be acyclic; constitutive ones may be cyclic, and are
     then sustained as fixed points of collective incorporation.
  3. "In force" is a greatest fixed point: a cycle stays in force while all
     its anchors hold, and collapses together when one lapses (a bank run).
  4. Dogma = content still incorporated after its context has lapsed.
  5. Failures are kept as nogoods (anchor bundles + reason) for
     Duhem–Quine triangulation, after de Kleer's ATMS.

  Standalone: intended to be mapped onto the Filter/morphism structure of
  POLARIS_Ontology.lean later, not to replace it.
-/

namespace SCORE.B3Context

/-- How content follows from context. -/
inductive Kind where
  | formal        -- derived (proof)
  | descriptive   -- observed (word-to-world)
  | constitutive  -- enacted (world-to-word; may be circular)
  | procedural    -- carried out (tested by working)
  deriving DecidableEq, Repr

/-- Where a context chain leaves B₃, typed by the morphism it rides on. -/
inductive Anchor where
  | perceived (condition : String)   -- B₁ → B₂ (perception)
  | accepted  (community : String)   -- B₃ → B₂ (incorporation / acceptance)
  | enacted   (outcome : String)     -- B₂ → B₁ (action succeeded)
  deriving DecidableEq, Repr

abbrev InscId := Nat

structure Inscription where
  id      : InscId
  kind    : Kind
  content : String
  anchors : List Anchor   -- direct exits from B₃
  deps    : List InscId   -- context drawn from other inscriptions
  deriving Repr

structure Store where
  items : List Inscription

/-- A world state: which anchors currently hold. Supplied from B₁/B₂. -/
abbrev AnchorState := Anchor → Bool

def Store.lookup (s : Store) (i : InscId) : Option Inscription :=
  s.items.find? (·.id == i)

def iter {α : Type} (f : α → α) : Nat → α → α
  | 0,     a => a
  | n + 1, a => iter f n (f a)

/-! ### Grounding (least fixed point): does the inscription touch B₁/B₂ at all? -/

def groundedStep (s : Store) (g : InscId → Bool) : InscId → Bool := fun i =>
  match s.lookup i with
  | none   => false
  | some x => !x.anchors.isEmpty || (!x.deps.isEmpty && x.deps.all g)

/-- Start from "nothing grounded" and propagate outward from anchors. -/
def grounded (s : Store) : InscId → Bool :=
  iter (groundedStep s) (s.items.length + 1) (fun _ => false)

/-! ### In force (greatest fixed point): do all anchors and dependencies still hold? -/

def inForceStep (s : Store) (w : AnchorState) (g : InscId → Bool)
    (v : InscId → Bool) : InscId → Bool := fun i =>
  match s.lookup i with
  | none   => false
  | some x => g i && x.anchors.all w && x.deps.all v

/-- Start from "everything in force" and strike out what loses support.
    Cycles whose anchors all hold survive (self-sustaining institutions);
    one lapsed anchor anywhere in a cycle collapses the whole cycle. -/
def inForce (s : Store) (w : AnchorState) : InscId → Bool :=
  iter (inForceStep s w (grounded s)) (s.items.length + 1) (fun _ => true)

/-! ### Well-foundedness: circularity is an error except for constitutive kinds -/

def reaches (s : Store) : Nat → InscId → InscId → Bool
  | 0,        _,   _   => false
  | fuel + 1, src, tgt =>
    match s.lookup src with
    | none   => false
    | some x => x.deps.any (fun d => d == tgt || reaches s fuel d tgt)

def circular (s : Store) (i : InscId) : Bool :=
  reaches s s.items.length i i

/-- Inscriptions whose justification is circular but whose kind forbids it. -/
def illFounded (s : Store) : List InscId :=
  (s.items.filter (fun x => x.kind != .constitutive && circular s x.id)).map (·.id)

/-! ### Dogma and structural age -/

/-- B₂ uptake: which inscriptions a population is currently incorporating. -/
abbrev Uptake := InscId → Bool

def dogma (s : Store) (w : AnchorState) (u : Uptake) (i : InscId) : Bool :=
  u i && !(inForce s w i)

/-- (dogmatic, incorporated): share of active content resting on lapsed context. -/
def structuralAge (s : Store) (w : AnchorState) (u : Uptake) : Nat × Nat :=
  let inc := s.items.filter (fun x => u x.id)
  ((inc.filter (fun x => dogma s w u x.id)).length, inc.length)

/-! ### Failure record (ATMS-style nogoods) -/

/-- A recorded failure: the whole assumption bundle, plus why (blameless). -/
structure Nogood where
  bundle : List Anchor
  reason : String

/-- Triangulation: how many recorded failures implicate this anchor. -/
def suspicion (ngs : List Nogood) (a : Anchor) : Nat :=
  (ngs.filter (fun n => n.bundle.contains a)).length

/-! ### Worked example -/

def demo : Store := ⟨[
  ⟨1, .formal,       "Peano axioms",               [.accepted "mathematicians"], []⟩,
  ⟨2, .formal,       "a theorem of arithmetic",    [],                           [1]⟩,
  ⟨3, .formal,       "Euclid's axioms",            [.accepted "mathematicians"], []⟩,
  ⟨4, .descriptive,  "physical space is Euclidean",[.perceived "space is flat"], [3]⟩,
  ⟨5, .constitutive, "this currency has value",    [.accepted "market"],         [6]⟩,
  ⟨6, .constitutive, "prices quoted in currency",  [],                           [5]⟩,
  ⟨7, .formal,       "bubble A (proves B)",        [],                           [8]⟩,
  ⟨8, .formal,       "bubble B (proves A)",        [],                           [7]⟩
]⟩

/-- After Einstein: flat space no longer holds; everything else does. -/
def postEinstein : AnchorState
  | .perceived "space is flat" => false
  | _                          => true

/-- A bank run on top of that. -/
def bankRun : AnchorState
  | .accepted "market" => false
  | a                  => postEinstein a

/-- A population still teaching Euclid as physics. -/
def uptake : Uptake := fun i => i ∈ [1, 2, 4, 5, 6]

#eval [1,2,3,4,5,6,7,8].map (fun i => (i, inForce demo postEinstein i))
-- expect: 4 lapsed; 5,6 sustained by their cycle; 7,8 ungrounded
#eval [5,6].map (fun i => (i, inForce demo bankRun i))
-- expect: both collapse together
#eval illFounded demo                        -- expect [7, 8]; 5,6 permitted
#eval structuralAge demo postEinstein uptake -- expect (1, 5): Euclid-as-physics
#eval suspicion
  [⟨[.perceived "space is flat", .accepted "mathematicians"], "Mercury perihelion"⟩,
   ⟨[.perceived "space is flat"], "starlight bending, 1919"⟩]
  (.perceived "space is flat")               -- expect 2

/-! ### Theorems to state later (left open, per the staged approach)
  * grounding: inForce s w i = true → grounded s i = true
  * cycle collapse: if i, j lie on a common cycle, lapsing any anchor on it
    removes both from force
  * the iteration bound (|items| + 1) reaches the fixed point
-/

end SCORE.B3Context
