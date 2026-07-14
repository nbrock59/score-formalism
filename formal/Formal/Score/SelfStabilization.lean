import Formal.Score.Core

set_option linter.unusedVariables false
set_option linter.style.whitespace false

/-!
# SCORE.SelfStabilization

Abstract self-stabilization predicate + Dijkstra 1974 K-state ring reference
case. Anchors the SCORE orthodoxy positioning against Dijkstra 1974
(Communications of the ACM 17(11), 643–644): distributed control produces
global order under purely local rules on a graph. Provides a peer-agnostic
predicate any SCORE peer can instantiate to assert within-basin
self-stabilization of its HOA maintenance mechanism.

See vault: `obsidian/sources/Dijkstra-Edsger.md`,
`obsidian/SCORE/emergence/mechanism/HOA.md`,
`obsidian/SCORE/emergence/mechanism/Hysteresis.md`.

OWL anchors: `score-core#SelfStabilizationProperty`,
`score-core#WithinBasinConvergence`, `score-core#hasStabilizationProperty`.
-/

namespace SCORE

-- ════════════════════════════════════════════════════════════════
-- §SS1. ABSTRACT SELF-STABILIZATION PREDICATE
-- Dijkstra 1974: from any initial state and under any adversarial schedule,
-- the system reaches a legitimate state in finite time. Parametric over
-- state, move relation, legitimate predicate, and basin — so that both the
-- Dijkstra 1974 original (Basin ≡ True) and the SCORE within-basin variant
-- (Basin ≡ inHysteresisWindow) instantiate the same definition.
-- ════════════════════════════════════════════════════════════════

/-- Abstract self-stabilization: from every state satisfying the basin
    predicate, every infinite move-sequence eventually reaches a legitimate
    state. Dijkstra 1974's original property is the special case
    `Basin ≡ (fun _ => True)` (global stabilization). SCORE's HOA
    maintenance is the case `Basin ≡ inHysteresisWindow` (within-basin
    stabilization; global guarantee is lost outside the basin —
    see `Hysteresis.md`). -/
def SelfStabilizingWithin {State : Type}
    (Basin      : State → Prop)
    (Legitimate : State → Prop)
    (Moves      : State → State → Prop) : Prop :=
  ∀ s, Basin s →
    ∀ trace : ℕ → State,
      trace 0 = s →
      (∀ i, Moves (trace i) (trace (i+1))) →
      ∃ n, Legitimate (trace n)

/-- The Dijkstra 1974 original property: global self-stabilization
    (every state converges, not just basin states). -/
def GloballySelfStabilizing {State : Type}
    (Legitimate : State → Prop)
    (Moves      : State → State → Prop) : Prop :=
  SelfStabilizingWithin (fun _ => True) Legitimate Moves

/-- Abstract *maintenance* predicate — the sibling of `SelfStabilizingWithin`.
    If a state satisfies `Property` and the basin is preserved through every
    step of a trace, then `Property` is preserved through every step. Distinct
    from convergence: convergence promises "eventually Property from any basin
    state"; maintenance promises "always Property from a Property∧basin state
    whose trace stays in basin." The two coincide for Dijkstra 1974's original
    setting (Basin ≡ True and property invariant under moves) but diverge for
    hysteretic systems where basin states without Property cannot spontaneously
    acquire it (the second stable equilibrium of a bistable region). This is
    the shape SCORE's HOA within-basin theorem actually takes — see
    `Formal/Score/HOAMaintenance.lean` and `obsidian/sources/Dijkstra-Edsger.md`. -/
def MaintainedWithin {State : Type}
    (Basin    : State → Prop)
    (Property : State → Prop)
    (Moves    : State → State → Prop) : Prop :=
  ∀ s, Property s → Basin s →
    ∀ trace : ℕ → State,
      trace 0 = s →
      (∀ i, Moves (trace i) (trace (i+1))) →
      (∀ i, Basin (trace i)) →
      ∀ i, Property (trace i)

/-- Abstract maintenance with a *per-step preservation premise* — the honest
    sibling of `MaintainedWithin` for systems where the property's preservation
    across a move requires more than staying in basin. The extra `Preserves :
    State → State → Prop` premise names what the move must additionally
    satisfy for `Property` to carry over (e.g., an autocatalytic feedback
    loop being engaged for the transition; the "acts on the environment"
    mechanism of Hysteresis.md § "Aggregate-weight hysteresis"). The bare
    `MaintainedWithin` overreaches for such systems — it implicitly assumes
    every basin-preserving move preserves the property, which is not so
    when the basin admits a second stable equilibrium below the property
    threshold. See `Formal/Score/HOAMaintenance.lean` for the HOA instance
    (`HOAMaintainedWithin` uses this variant with `Preserves := feedbackEngaged`). -/
def MaintainedWithinIfPreserved {State : Type}
    (Basin     : State → Prop)
    (Property  : State → Prop)
    (Moves     : State → State → Prop)
    (Preserves : State → State → Prop) : Prop :=
  ∀ s, Property s → Basin s →
    ∀ trace : ℕ → State,
      trace 0 = s →
      (∀ i, Moves (trace i) (trace (i+1))) →
      (∀ i, Basin (trace i)) →
      (∀ i, Preserves (trace i) (trace (i+1))) →
      ∀ i, Property (trace i)

-- ════════════════════════════════════════════════════════════════
-- §SS2. DIJKSTRA 1974 K-STATE RING (Construction 1, p. 643)
-- N+1 finite-state machines on a ring, each holding a value in [0, K).
-- Bottom machine (position 0) bumps S := (S+1) mod K when its left
-- neighbor (position N; the top) equals its own state. Every other
-- machine copies its left neighbor's state when it differs.
--
-- Dijkstra's flagged CRUCIAL FINDING: identical machines cannot
-- self-stabilize. The bottom's rule differs from the interior's;
-- symmetry-breaking is essential. Diagnostic for SCORE: agent
-- heterogeneity along CouplingWeightVector / LifeCyclePhase /
-- ManifoldShape axes is the analogous symmetry-breaker.
-- ════════════════════════════════════════════════════════════════

/-- A configuration of a Dijkstra K-state ring with N+1 machines. -/
structure DijkstraRing (N K : ℕ) where
  /-- State of each machine, indexed by ring position. -/
  state : Fin (N+1) → Fin K
  /-- Note 1 (p. 644): K > N is sufficient with a central daemon. -/
  wide  : N < K

/-- The bottom machine (position 0) has a privilege iff its left neighbor
    (position N — ring wrap) equals its own state. -/
def DijkstraRing.bottomPriv {N K : ℕ} (c : DijkstraRing N K) : Prop :=
  c.state (Fin.last N) = c.state 0

/-- An interior machine (position i > 0) has a privilege iff its left
    neighbor (position i-1) differs from its own state. -/
def DijkstraRing.interiorPriv {N K : ℕ} (c : DijkstraRing N K)
    (i : Fin (N+1)) (hi : 0 < i.val) : Prop :=
  c.state ⟨i.val - 1, by omega⟩ ≠ c.state i

/-- Dijkstra's chosen legitimate predicate (p. 643): exactly one machine
    has a privilege. -/
axiom DijkstraLegitimate {N K : ℕ} : DijkstraRing N K → Prop

/-- The move relation: the (central-daemon-selected) enabled machine
    fires, per Construction 1's transition rules. -/
axiom DijkstraMove {N K : ℕ} : DijkstraRing N K → DijkstraRing N K → Prop

/-- Dijkstra 1974's headline result (Construction 1, K > N, central daemon):
    the K-state ring is *globally* self-stabilizing. Asserted as a
    reference-case axiom; the paper's proof is the canonical reference and
    is not re-derived in Lean. Serves as the existence witness that
    `SelfStabilizingWithin` is inhabited under a well-known construction. -/
axiom dijkstraRingSelfStabilizes {N K : ℕ} :
    GloballySelfStabilizing (@DijkstraLegitimate N K) (@DijkstraMove N K)

-- ════════════════════════════════════════════════════════════════
-- §SS3. HOA within-basin self-stabilization (planned)
-- SCORE-specific claim: HOA maintenance is self-stabilizing WITHIN the
-- hysteresis basin. Below the dissolution threshold the property is lost
-- (Dijkstra 1974's global-convergence guarantee does not survive the
-- boundary). Requires the Hysteresis lean-planned predicates
-- (hysteresisWindow / formationThreshold / dissolutionThreshold) before
-- the theorem can be stated concretely; recorded here as a planned target.
-- ════════════════════════════════════════════════════════════════

-- Hook 3 negative theorem (`hoaFragilityHomogeneous`) — Dijkstra's
-- "identical machines cannot self-stabilize" applied to SCORE — is now
-- formalized in `Score/HOAMaintenance.lean` §HM22. See vault:
-- `obsidian/SCORE/emergence/mechanism/AgentHomogeneityFragility.md`.

end SCORE
