import Formal.Score.Core
import Formal.Score.HOAMaintenance

set_option linter.unusedVariables false
set_option linter.style.whitespace false

/-!
# SCORE.Agora

AGORA peer: the captured-correction impossibility lemma (SS13), the
legal-precedent network binding (SS17), and the maintenance-bridge
(§HM-Bridge) restating SS13 in the population/predicate vocabulary of
`HOAMaintenance` (Hook 3, §HM22) with an honest delta comment on why
the two are analogous but not formally reducible at this tier.
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


-- ════════════════════════════════════════════════════════════════
-- §HM-Bridge. AGORA MAINTENANCE-BRIDGE — restating SS13 in the
-- population/predicate vocabulary of Hook 3 (`HOAMaintenance` §HM22).
--
-- Purpose: make visible in Lean the correspondence between AGORA's SS13
-- `captured_correction_needs_independent_node` impossibility lemma and
-- the abstract `hoaFragilityHomogeneous` fragility theorem, WITHOUT
-- overclaiming a formal reduction that does not hold at this tier.
--
-- What lands here:
--   1. `AgoraCorrectingNode` opaque type + `nodeFloorOf` association
--      axiom — the AGORA-side analog of §HM22's `Agent` +
--      `agentCouplingWeightVector`.
--   2. `PopulationCorrectingNodeCaptured` predicate — the AGORA-side
--      sibling of §HM22's `PopulationCouplingHomogeneous`, structurally
--      parallel but scoped to a functional role (correcting nodes)
--      rather than the whole agent population.
--   3. `populationCaptured_reachableMismatch_nonzero` — a trivial
--      reformulation of SS13 in the new vocabulary, giving Hook-3-shaped
--      access to the AGORA impossibility.
--
-- What does NOT land here (deliberately):
--
-- A formal derivation of SS13 from `hoaFragilityHomogeneous`. Both
-- capture the intuition "uniformity along a specific axis prevents the
-- maintenance mechanism from operating", but at different formal levels:
--
--   * `captured_correction_needs_independent_node` is a POINT-LEVEL
--     ARITHMETIC BOUND: `nodeFloor > 0 → reachableMismatch ≠ 0`. A
--     single-state claim about what a given node configuration can
--     achieve.
--
--   * `hoaFragilityHomogeneous` is a TRACE-LEVEL DYNAMICS CLAIM:
--     `PopulationCouplingHomogeneous s → ∀ trace ∀ i, ¬ feedbackEngaged`.
--     A statement about how a homogeneous population's history must
--     evolve.
--
-- A reduction would require either
--   (a) a *partial-homogeneity* variant of Hook 3 predicating over a
--       functional role (correcting nodes) rather than all agents, or
--   (b) an abstract *structural-fragility* theorem that both impossi-
--       bility claims are instances of.
-- Neither exists at this tier; both are candidate future formalizations.
-- Until then, the correspondence is REAL but DOCUMENTED, not DERIVED.
--
-- Spec-side counterpart: `core/agora/AGORA_Interface_Contracts.md`
-- §6 (SCORE Maintenance Machinery Mapping). Cross-ref: `agora:CapturedCorrec-
-- tionUpdate` (OWL), Hook 3 (SC-G-58, `AgentHomogeneityFragility`).
-- ════════════════════════════════════════════════════════════════

/-- AGORA-side opaque type for the correcting-node role. Analog of the
    `Agent` type consumed by §HM22's `agentCouplingWeightVector`. -/
axiom AgoraCorrectingNode : Type

/-- Each AGORA correcting node has a `nodeFloor` in the reals (the
    residual mismatch it *cannot* correct below — its own drift).
    Analog of §HM22's `agentCouplingWeightVector`. -/
axiom nodeFloorOf : AgoraCorrectingNode → ℝ

/-- **Population-side captured predicate.** All correcting nodes in a
    given set are captured: their floors are all at least a common
    positive `floor`. Sibling of §HM22's `PopulationCouplingHomogeneous`
    (structurally parallel; scoped to the correcting-node role rather
    than the whole agent population). -/
def PopulationCorrectingNodeCaptured
    (floor : ℝ) (nodes : Set AgoraCorrectingNode) : Prop :=
  0 < floor ∧ ∀ n ∈ nodes, floor ≤ nodeFloorOf n

/-- **Bridge restatement of SS13.** For a captured population of
    correcting nodes, every node's reachable mismatch is nonzero — no
    route to zero exists among the captured nodes. Trivial lift of SS13
    over `PopulationCorrectingNodeCaptured`, giving the AGORA
    impossibility a Hook-3-shaped statement (population predicate →
    universal impossibility over its members). -/
theorem populationCaptured_reachableMismatch_nonzero
    {floor : ℝ} {nodes : Set AgoraCorrectingNode}
    (h : PopulationCorrectingNodeCaptured floor nodes) :
    ∀ n ∈ nodes, reachableMismatch (nodeFloorOf n) ≠ 0 :=
  fun n hn => captured_correction_needs_independent_node h.1 (h.2 n hn)


-- ════════════════════════════════════════════════════════════════
-- §HM-Bridge-2. PATH (1) VALIDATION EXPERIMENT
--
-- Attempt to derive SS13 (`captured_correction_needs_independent_node`)
-- from Hook 3 (`hoaFragilityHomogeneous`) via specialization of
-- `AgoraCorrectingNode` over the abstract `Agent` type.
--
-- Purpose: run the actual generalization test — "either the reduction
-- goes through, or it fails at a specific place that names the missing
-- structure." This is the machine-checkable answer to the question
-- "does the abstract HOA-maintenance machinery correctly generalize
-- AGORA's existing formalization?"
--
-- Result: the specialization goes through cleanly at the TYPE level,
-- but the reduction attempt is *vacuous* at the PROOF level — SS13's
-- proof does not invoke Hook 3 at any point because SS13 is a
-- point-level ARITHMETIC bound while Hook 3 is a trace-level DYNAMICS
-- claim. The correspondence at the intuitive level ("role uniformity
-- → impossibility") does NOT lift to formal reduction.
--
-- Informative outcome: the mapping-table row §6.1 for `SS13 ↔ Hook 3`
-- in `AGORA_Interface_Contracts.md` is downgraded from "sibling" to
-- "same intuitive family, different formal shape; reduction attempted
-- and shown INAPPLICABLE." A candidate future theorem — SS13-dyn, a
-- trace-level dynamics claim about `CapturedCorrectionUpdate` sequences
-- under a role-scoped restoration intervention — WOULD be a genuine
-- Hook-3 generalization candidate, but does not currently exist in
-- AGORA's formalization.
-- ════════════════════════════════════════════════════════════════

namespace SS13FromHook3Experiment

/-- **Specialization step 1** — a role predicate over the abstract
    `Agent` type. AGORA's correcting nodes are literally the abstract
    agents that satisfy this predicate. -/
axiom IsCorrectingNode : Agent → Prop

/-- **Specialization step 2** — `AgoraCorrectingNode` as a subtype of
    the abstract `Agent`. The type-level specialization goes through
    cleanly; the abstract machinery does not obstruct it. -/
def AgoraCorrectingNodeSpec : Type := { a : Agent // IsCorrectingNode a }

/-- **First gap discovery** — `nodeFloor` has no natural analog in the
    abstract machinery. Hook 3 knows only `agentCouplingWeightVector`;
    AGORA must add `agentMismatchFloor` as new peer-specific data on
    every abstract Agent. This is a *specialization-added-data* gap,
    not a fundamental incompatibility: the abstract machinery does not
    forbid the projection, it simply does not supply it. -/
axiom agentMismatchFloor : Agent → ℝ

noncomputable def nodeFloorOfSpec (n : AgoraCorrectingNodeSpec) : ℝ :=
  agentMismatchFloor n.1

/-- **Reduction attempt** — for a captured specialized-population, the
    reachable mismatch through any node is nonzero. If the abstract
    machinery generalizes AGORA at this hook, this should close via
    `hoaFragilityHomogeneous`. -/
theorem specialization_captured_reachable_nonzero
    {floor : ℝ} {nodes : Set AgoraCorrectingNodeSpec}
    (h : 0 < floor) (hcap : ∀ n ∈ nodes, floor ≤ nodeFloorOfSpec n) :
    ∀ n ∈ nodes, reachableMismatch (nodeFloorOfSpec n) ≠ 0 := by
  -- **Second gap discovery** (in-proof). To invoke `hoaFragilityHomogeneous`
  -- we would need:
  --   (a) a state `s : HOAState r` populated with these nodes,
  --   (b) a proof that `PopulationCorrectingNodeCaptured` (role-scoped,
  --       mismatch-floor axis) implies `PopulationCouplingHomogeneous`
  --       (whole-population, coupling-weight axis) for that `s`,
  --   (c) a bridge from `¬ feedbackEngaged c s s'` (a move-sequence
  --       property) to `reachableMismatch ≠ 0` (a node-arithmetic
  --       property).
  -- None of (a)-(c) is available. And the goal collapses to a trivial
  -- arithmetic proof that BYPASSES Hook 3 entirely (`nodeFloor > 0` is
  -- arithmetically `≠ 0`; no dynamics, no traces, no populations, no
  -- maintenance mechanism):
  intro n hn
  unfold reachableMismatch
  exact (lt_of_lt_of_le h (hcap n hn)).ne'

/-!
### Experimental conclusion

The proof of `specialization_captured_reachable_nonzero` above:

  * uses no lemma from `HOAMaintenance.lean`;
  * uses no state, region, trace, or move-sequence structure;
  * uses no `PopulationCouplingHomogeneous` hypothesis;
  * uses no `hoaFragilityHomogeneous` invocation;
  * is closed by the same one-line arithmetic that proves the
    non-specialized SS13.

The Path (1) experiment therefore *falsifies* the claim that Hook 3
generalizes SS13 as currently formalized. The two theorems capture
different notions of "role-uniformity → impossibility":

  * SS13: **static arithmetic** — captured nodes have positive floors,
    and a positive floor is arithmetically nonzero.
  * Hook 3: **dynamic feedback disengagement** — homogeneous
    populations cannot fire the maintenance mechanism across a trace
    of moves.

A future theorem SS13-dyn (trace-level, about `CapturedCorrectionUpdate`
sequences failing to reach zero under a role-scoped restoration
intervention) would be a genuine Hook 3 generalization candidate,
requiring the partial-homogeneity Hook 3 variant flagged in
§HM-Bridge (candidate (a)). SS13-dyn does not currently exist in
AGORA's formalization; introducing it is future work.

Path (1) verdict on the abstract machinery: it does not generalize
SS13, and the reason is not "an axiom is missing" but "the theorems
operate at different semantic levels." Fixing this requires either
adjustment on the AGORA side (formulate SS13-dyn) or on the abstract
side (formulate a POINT-level static-fragility theorem that Hook 3
would specialize to). The one-directional intuition that Hook 3 is
"the more general form" was wrong.
-/

-- ────────────────────────────────────────────────────────────────
-- M3 witness (post-M2 multi-stratum extension, 2026-07-14)
--
-- After M2 (`Core.lean` §3 gained `Constituent = AAgent | SigmaAgent`;
-- `HOAMaintenance.lean` §HM1 retyped `HOAState.agents : List Constituent`;
-- Hook 3 population predicates rewritten as A-actor-scoped filters over
-- `Constituent.AAgent`), the Path (1) verdict must be unchanged: the
-- typing fix is orthogonal to the direction-of-formalization mismatch.
--
-- This is that verification, made explicit at the Lean level: for every
-- captured correcting node, we exhibit BOTH (a) the M2-provided
-- `Constituent.AAgent` lift required to populate an HOAState, AND
-- (b) the SS13 conclusion (reachable mismatch nonzero). The proof of (b)
-- is `specialization_captured_reachable_nonzero` unchanged --- no Hook 3
-- invocation, no HOAState machinery, no consultation of the Constituent
-- structure to close. The Constituent lift is a witness that M2's typing
-- is real machinery available to the peer bridge, not a required input
-- to the SS13 arithmetic.
-- ────────────────────────────────────────────────────────────────

/-- **M3 witness: SS13 verdict survives multi-stratum extension.** For every
    captured correcting node, we exhibit the `Constituent.AAgent` lift M2
    provides for populating `HOAState` AND the SS13 nonzero-reachable-
    mismatch conclusion. The proof of the SS13 conclusion is
    `specialization_captured_reachable_nonzero` unchanged; the lift is
    `rfl`. Together: M2's typing plays no role in SS13's proof, confirming
    that the multi-stratum extension is orthogonal to the direction-of-
    formalization mismatch documented in the M3-preceding sections. -/
theorem multistratum_captured_reachable_nonzero
    {floor : ℝ} {nodes : Set AgoraCorrectingNodeSpec}
    (h : 0 < floor) (hcap : ∀ n ∈ nodes, floor ≤ nodeFloorOfSpec n) :
    ∀ n ∈ nodes,
      ∃ c : Constituent,
        c = Constituent.AAgent n.1 ∧
        reachableMismatch (nodeFloorOfSpec n) ≠ 0 := by
  intro n hn
  refine ⟨Constituent.AAgent n.1, rfl, ?_⟩
  exact specialization_captured_reachable_nonzero h hcap n hn

end SS13FromHook3Experiment


-- ════════════════════════════════════════════════════════════════
-- §PS-U2. AGORA U2 SPECIALIZATION --- InstitutionalMaintainingCommunity
-- as an A-actor-scoped HOAState (Present-Domain → Present-Formal)
--
-- The HM Specialization Audit (`core/agora/AGORA_HM_Specialization_Audit.md`
-- §1) rated U2 as Present-Domain because AG-G-02
-- (`agora:InstitutionalMaintainingCommunity` refining SC-G-25 HOA / SC-G-26
-- HumanCommunity) named the HOA analog at the glossary + OWL layer but no
-- Lean specialization instantiated §HM's `HOAState` machinery. This
-- section is that specialization, made possible by the M2 multi-stratum
-- extension (`Core.lean` §3 `Constituent = AAgent | SigmaAgent`;
-- `HOAMaintenance.lean` §HM1 `HOAState.agents : List Constituent`).
--
-- The specialization encodes AGORA's Sigma-actor-sustained-by-A-actor-HOA
-- framing: an `AgoraMaintainingCommunity r` is exactly an `HOAState r`
-- whose agents field is `Constituent.AAgent`-constrained (role-occupant
-- nodes are individual A-actors, not Σ-actors). Distinct from ATLAS's
-- `DeterrenceBasin` (Σ-actor-typed) which would use `Constituent.SigmaAgent`.
--
-- Everything §HM provides on HOAState (Basin, effectiveDissolution,
-- AutocatalyticCombine, ...) is inherited via the `.toHOAState` projection.
-- Downstream AGORA-specific facts (institutional-health composition, the
-- A5 CapturedCorrectionUpdate dynamics, ...) can now be stated over
-- `AgoraMaintainingCommunity` and use the abstract §HM machinery
-- underneath.
-- ════════════════════════════════════════════════════════════════

/-- **AGORA's `InstitutionalMaintainingCommunity` as an HOAState subtype**
    (AG-G-02, refining SC-G-25 HOA). An HOA state whose entire population
    is A-actor role occupants --- captured by the subtype constraint that
    every constituent in the `agents` list is a `Constituent.AAgent`. -/
def AgoraMaintainingCommunity (r : Region) : Type :=
  { s : HOAState r //
    ∀ c ∈ s.agents, ∃ a : Agent, c = Constituent.AAgent a }

/-- Extract the underlying `HOAState`; the §HM machinery (Basin,
    effectiveDissolution, autocatalytic feedback, ...) applies via this
    projection. -/
def AgoraMaintainingCommunity.toHOAState {r : Region}
    (mc : AgoraMaintainingCommunity r) : HOAState r := mc.1

/-- **A-actor constraint witness.** Every constituent of an AGORA
    maintaining community is a `Constituent.AAgent` --- the direct
    formalization of the AG-G-02 framing that institutional
    role-occupants are individual A-actors. Follows immediately from
    the subtype constraint. -/
theorem AgoraMaintainingCommunity.agents_are_AAgent {r : Region}
    (mc : AgoraMaintainingCommunity r) :
    ∀ c ∈ mc.toHOAState.agents, ∃ a : Agent, c = Constituent.AAgent a :=
  mc.2

/-- **Coupling homogeneity lifts trivially to the AGORA specialization.**
    An `AgoraMaintainingCommunity` inherits Hook 3's population predicates
    through its projection to `HOAState`. This witness makes explicit that
    the M2 A-actor-scoped filter over `Constituent.AAgent` is exactly the
    correct scoping for AGORA (whose maintaining community is
    A-actor-typed by construction), and Hook 3's fragility results apply
    without any additional AGORA-specific plumbing. -/
theorem AgoraMaintainingCommunity.populationCouplingHomogeneous_iff_agents
    {r : Region} (mc : AgoraMaintainingCommunity r) :
    PopulationCouplingHomogeneous mc.toHOAState ↔
      ∀ a₁ a₂ : Agent,
        Constituent.AAgent a₁ ∈ mc.toHOAState.agents →
        Constituent.AAgent a₂ ∈ mc.toHOAState.agents →
        agentCouplingWeightVector a₁ = agentCouplingWeightVector a₂ :=
  Iff.rfl


-- ════════════════════════════════════════════════════════════════
-- §PS-U1. AGORA U1 SPECIALIZATION --- InstitutionalMaintainingCommunity
-- self-stabilization (Present-Domain → Present-Formal)
--
-- The HM Specialization Audit (`AGORA_HM_Specialization_Audit.md` §1)
-- rated AGORA's U1 as Present-Domain: the vocabulary layer named
-- self-stabilization (`InstitutionalMaintainingCommunity` sustaining
-- constitutional B₃; alignment functional A measuring deviation;
-- Core-promoted `FitnessCriterion` via POLARIS∩ETHOS) but no Lean
-- specialization of `SelfStabilizingWithin` existed.
--
-- The specialization is a peer-scoped abbrev over `SelfStabilization.lean`'s
-- polymorphic `SelfStabilizingWithin`, parameterized on the AGORA U2 type
-- `AgoraMaintainingCommunity`. Concrete Basin/Legitimate/Moves choices
-- (the A3 InstitutionalHealthScore threshold as Legitimate; A5
-- CapturedCorrectionUpdate as Moves; "no capture yet" as Basin) are
-- peer-specific work and Q4 BIND, reserved for future PRs. The alias
-- establishes the Present-Formal binding at the type layer.
--
-- Companion `MaintainedWithin` / `MaintainedWithinIfPreserved` (the
-- maintenance variants in `SelfStabilization.lean`) apply symmetrically;
-- omitted here to keep the U1 upgrade minimal but available under the
-- same alias pattern if a future PR needs them.
-- ════════════════════════════════════════════════════════════════

/-- **AGORA U1: self-stabilization of the maintaining community.**
    Peer-scoped abbrev for `SCORE.SelfStabilizingWithin` on
    `AgoraMaintainingCommunity`. Concrete Basin/Legitimate/Moves are
    peer-specific / Q4 BIND. -/
def AgoraMaintainingCommunity.stabilizesWithin {r : Region}
    (Basin      : AgoraMaintainingCommunity r → Prop)
    (Legitimate : AgoraMaintainingCommunity r → Prop)
    (Moves      : AgoraMaintainingCommunity r → AgoraMaintainingCommunity r → Prop) : Prop :=
  SelfStabilizingWithin Basin Legitimate Moves


-- ════════════════════════════════════════════════════════════════
-- §PS-U4. AGORA U4 SPECIALIZATION --- autocatalytic feedback +
-- B₃-substrate prosthetic (Present-Domain → Present-Formal)
--
-- The HM Specialization Audit (`AGORA_HM_Specialization_Audit.md` §1)
-- rated AGORA's U4 as Present-Domain: `DoctrinalCorpus` (AG-G-12) is
-- the central B₃-substrate; role-occupant nodes carrying manifold
-- positions m_i via role templates R IS the autocatalytic maintenance
-- loop (manifolds shape role behavior → role behavior maintains
-- constitutional B₃ → B₃ shapes future role templates). Vocabulary
-- complete. But `Score/Agora.lean` §17 specializes DoctrinalCorpus as a
-- `Core.DoctrinalNetwork`, NOT as §HM's `AutocatalyticCombine` or
-- `B3SubstratePolicy`. The Core-level specialization exists; the §HM-
-- level specialization did not.
--
-- This section binds §HM's `HOAState.weight` and `closes_hysteresis_gap`
-- machinery to `AgoraMaintainingCommunity` via peer-scoped wrappers.
-- The wrappers make explicit that any concrete autocatalytic-combine
-- operator (chosen by A3/A5 peer work) can be applied to AGORA's
-- maintaining community through its `.toHOAState` projection, and the
-- load-bearing `closes_hysteresis_gap` axiom carries through.
-- ════════════════════════════════════════════════════════════════

/-- **AGORA U4: autocatalytic weight of the maintaining community.**
    The aggregate observable weight of an AGORA maintaining community
    under a chosen autocatalytic-combine operator, delegated to
    `HOAState.weight` via the peer's `.toHOAState` projection. -/
def AgoraMaintainingCommunity.autocatalyticWeight {r : Region}
    (c : AutocatalyticCombine) (mc : AgoraMaintainingCommunity r) : ℝ :=
  HOAState.weight c mc.toHOAState

/-- **AGORA U4: hysteresis gap closes for the maintaining community.**
    The load-bearing autocatalytic axiom lifts through the peer's
    projection: if the maintaining community's substrate is at least
    dissolution and its loop endowment meets the engagement threshold,
    the community's autocatalytic weight is at least formation. Direct
    specialization of `AutocatalyticCombine.closes_hysteresis_gap`. -/
theorem AgoraMaintainingCommunity.autocatalytic_closes_gap {r : Region}
    (c : AutocatalyticCombine) (mc : AgoraMaintainingCommunity r)
    (hs : (dissolutionThreshold r).val ≤ mc.toHOAState.substrate.val)
    (he : c.engagementThreshold r ≤ mc.toHOAState.loopEndowment.val) :
    (formationThreshold r).val ≤ mc.autocatalyticWeight c :=
  c.closes_hysteresis_gap r
    mc.toHOAState.substrate mc.toHOAState.loopEndowment hs he


-- ════════════════════════════════════════════════════════════════
-- §PS-U7. AGORA U7 SPECIALIZATION --- L2 GenerationalRenewalMove
-- (Present-Domain → Present-Formal)
--
-- The HM Specialization Audit (`AGORA_HM_Specialization_Audit.md` §1)
-- rated AGORA's U7 as Present-Domain: AGORA's §6.1 mapping table
-- explicitly names MortalityBoundary Condition 5 (interpretive tradition
-- supplying an independent standard) ↔ L2 GenerationalRenewalMove and
-- A5 CapturedCorrectionUpdate ↔ L1 MemberTurnoverMove + failed L2. Peer
-- has explicitly named the L1/L2 correspondences. But no Lean
-- specialization of §HM25--§HM28 slow-move types existed. This section
-- binds the load-bearing L2 slow-move to `AgoraMaintainingCommunity` via
-- a peer-scoped wrapper. L1 MemberTurnoverMove, L3 PathAMove, and L4
-- CoInscriptionMove are similarly available under the same pattern and
-- are natural follow-ups; L2 is chosen here because it is the mapping-
-- table's load-bearing slow-move for the AGORA/§HM correspondence.
-- ════════════════════════════════════════════════════════════════

/-- **AGORA U7: L2 generational-renewal slow-move on the maintaining
    community.** Peer-scoped wrapper for `GenerationalRenewalMove` on
    `AgoraMaintainingCommunity`, delegated via `.toHOAState`. Named
    `generationalRenewal` (dropping the abstract's `Move` suffix) to
    avoid the dot-notation shadowing pattern that would otherwise
    conflate the peer method with the abstract axiom. -/
def AgoraMaintainingCommunity.generationalRenewal {r : Region}
    (a b : AgoraMaintainingCommunity r) : Prop :=
  GenerationalRenewalMove a.toHOAState b.toHOAState

/-- **AGORA U7: renewal maintains ceiling.** The §HM26
    `generationalRenewalMove_maintains_ceiling` axiom lifts through the
    peer's projection: successful generational inscription in the
    maintaining community preserves (or grows) the ceiling residue.
    The formal counterpart of AGORA's MortalityBoundary Condition 5 ---
    the interpretive tradition supplying an independent standard renews
    the ceiling across generations of role-occupants (§6.1). -/
theorem AgoraMaintainingCommunity.generationalRenewal_maintains_ceiling
    {r : Region} (a b : AgoraMaintainingCommunity r) :
    a.generationalRenewal b →
      a.toHOAState.ceilingResidue.val ≤ b.toHOAState.ceilingResidue.val :=
  generationalRenewalMove_maintains_ceiling _ _


-- ════════════════════════════════════════════════════════════════
-- §PS-U3U6. AGORA U3 + U6 SPECIALIZATION --- SS13 as instance of the
-- §HM30 point-level attenuation family (Awkward → Present-Formal)
--
-- The HM Specialization Audit (`AGORA_HM_Specialization_Audit.md` §1)
-- rated AGORA's U3 (hysteresis) and U6 (Hook 3 homogeneity fragility)
-- BOTH as Awkward, sharing the same root cause: direction-of-formalization
-- mismatch (AGORA formalizes maintenance OUTCOMES arithmetically via SS13;
-- §HM formalizes maintenance MECHANISMS via trace dynamics). Path (1)
-- experiment (PR #449, `SS13FromHook3Experiment` above) confirmed
-- SS13 does not reduce to Hook 3 through the multi-stratum extension
-- alone.
--
-- The audit synthesis (§4 direction-of-formalization mismatch as
-- family-wide finding; §5.4 New-abstract-candidate PointAttenuationLemma
-- 5/5 peers) proposed the fix: add a POINT-level companion machinery to
-- §HM that peer central lemmas can specialize. `HOAMaintenance.lean`
-- §HM30 delivers that companion (`point_fragility_positive_floor`,
-- `point_attenuation_monotone`, `point_attenuation_antitone`).
--
-- This section makes explicit that AGORA's SS13 is an instance of
-- `point_fragility_positive_floor`. The witness upgrades AGORA U3 AND
-- U6 from Awkward (SS13 does not specialize §HM's trace-level machinery)
-- to Present-Formal (SS13 specializes §HM30's point-level
-- point_fragility_positive_floor). Both U3 and U6 resolve via the same
-- witness because they shared the same root cause; adding point-level
-- machinery to §HM addresses both simultaneously.
--
-- The Path (1) finding stands unchanged --- SS13 still does not reduce
-- to Hook 3 (trace-level) through any means. What changes is that SS13
-- now DOES specialize §HM machinery (the point-level companion), so the
-- Awkward verdict is no longer accurate.
-- ════════════════════════════════════════════════════════════════

/-- **AGORA U3 + U6 Present-Formal witness.** SS13
    (`captured_correction_needs_independent_node`) is an instance of the
    §HM30 point-level attenuation family
    (`point_fragility_positive_floor`). The proof is `rfl` at the
    theorem level --- SS13's arithmetic content IS
    `point_fragility_positive_floor` applied to (floor, nodeFloor)
    followed by `unfold reachableMismatch`. -/
theorem ss13_as_pointFragility {floor nodeFloor : ℝ}
    (hfloor : 0 < floor) (hcap : floor ≤ nodeFloor) :
    reachableMismatch nodeFloor ≠ 0 := by
  unfold reachableMismatch
  exact point_fragility_positive_floor hfloor hcap


-- ════════════════════════════════════════════════════════════════
-- §PS-HM31. AGORA InstitutionalHealthScore as §HM31 CompositeMeasure
-- instance (audit synthesis §5.4 CompositeSigmaActorHealthScore 3-peer
-- echo).
--
-- AG-G-04 InstitutionalHealthScore is a distribution-valued composite
-- H = Φ_align × Φ_correction × Φ_independence. This section constructs
-- a `CompositeMeasure` instance over `AgoraMaintainingCommunity` whose
-- three factors are peer-scoped opaque functions (Q4 BIND) matching
-- the AG-G-04 decomposition. Scalar-valued at this tier;
-- distribution-valued lifting is future peer work.
-- ════════════════════════════════════════════════════════════════

/-- **Φ_align factor** of AGORA's InstitutionalHealthScore. Alignment
    of role-occupant manifold positions with the RoleTemplateSet.
    Q4 BIND (concrete values are peer-specific data). -/
axiom agoraPhiAlign {r : Region} : AgoraMaintainingCommunity r → ℝ

/-- **Φ_correction factor** of AGORA's InstitutionalHealthScore.
    Correction-capability of the maintaining community's independent
    nodes. Q4 BIND. -/
axiom agoraPhiCorrection {r : Region} : AgoraMaintainingCommunity r → ℝ

/-- **Φ_independence factor** of AGORA's InstitutionalHealthScore.
    Node-independence readout (distinct from the SS13 arithmetic floor).
    Q4 BIND. -/
axiom agoraPhiIndependence {r : Region} : AgoraMaintainingCommunity r → ℝ

/-- **AGORA InstitutionalHealthScore as §HM31 CompositeMeasure
    instance.** H = Φ_align × Φ_correction × Φ_independence lifts to
    `CompositeMeasure.value` on the peer's U2 type. -/
noncomputable def agoraInstitutionalHealthScore {r : Region} :
    CompositeMeasure (AgoraMaintainingCommunity r) :=
  { arity := 3,
    factor := ![agoraPhiAlign, agoraPhiCorrection, agoraPhiIndependence] }


end SCORE
