import Formal.Score.Core

/-!
# Penrose P1 — how the two formal encodings close the domain trichotomy

QUARANTINED EXPLORATION SANDBOX (`formal/explore/penrose/`). Nothing in the spine imports
this file, and nothing here is a SCORE commitment. Thread note:
`obsidian/explorations/penrose/Penrose-P1-PlatonicCommitment.md` § "The formal encodings".

The P1 question is whether SCORE *denies* a Platonic realm or merely *does not commit*. The
two formal layers already answer a narrower question differently: whether the classification
into domains closes at three.

* **Lean closes it.** `SCORE.Domain` is an inductive type with exactly three constructors, so
  every domain is one of the three (`domain_closed`) and there are exactly three
  (`domain_card`). A fourth domain is not expressible without editing `Core.lean`.
* **OWL does not.** `score-core.owl` makes `B1_Objective`, `B2_Subjective` and
  `B3_Inscription` pairwise disjoint subclasses of `Domain` but states no covering axiom, so
  under the open-world assumption a fourth disjoint `Domain` subclass is consistent. That half
  is checked by HermiT, not here: `../owl/p1-fourth-domain.owl` (expect consistent) and its
  control `../owl/p1-fourth-domain-covered.owl` (expect inconsistent).

Neither layer encodes the *denial of abstracta* itself. Lean's closure is a closure of the
domain classification; it says nothing about objects that are not domains. So the denial
lives in prose only, and P1's candidate repair (keep three domains, drop the denial) is
compatible with both encodings as they stand.

No SCORE or sandbox axioms. `#print axioms` (2026-10-17): `domain_closed` uses `propext`;
`domain_card` uses `propext` and `Quot.sound`. Both are Lean built-ins.
-/

namespace ExplorePenrose.P1

open SCORE

/-- Every SCORE domain is one of the three. Closure by construction of the inductive. -/
theorem domain_closed (d : Domain) :
    d = .Objective ∨ d = .Subjective ∨ d = .Inscription := by
  cases d <;> simp

/-- Sandbox-local `Fintype` instance; the spine does not derive one. -/
instance : Fintype Domain :=
  ⟨{.Objective, .Subjective, .Inscription}, by intro d; cases d <;> simp⟩

/-- There are exactly three domains. -/
theorem domain_card : Fintype.card Domain = 3 := by
  decide

end ExplorePenrose.P1
