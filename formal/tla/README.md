# formal/tla — model-checked SCORE dynamics (TLC)

A third formalism alongside the OWL ontology and the Lean spine, for the part of
SCORE that is **dynamical**: concrete transition systems whose temporal
behaviour (convergence, maintenance, liveness) the Lean layer states abstractly
but leaves as axioms or bounded-reference cases. TLC model-checks those systems
exhaustively for small parameters and produces counterexamples when a property
fails. Methodology note: `obsidian/SCORE/methodology/ModelCheckedDynamics.md`.

The division of labour is deliberate:

| | Lean (`Formal/Score/`) | TLC (`formal/tla/`) |
|---|---|---|
| Scope | unbounded, general (∀ N, K, …) | bounded instances (fixed N, K) |
| Dynamics | often **axiomatized** (e.g. `dijkstraRingSelfStabilizes`) | **executed** exhaustively |
| On failure | a proof gap | a concrete **counterexample trace** |

## Ring.tla — Dijkstra 1974 self-stabilizing ring

The Dijkstra K-state ring (Comm. ACM 17(11), 643–644), Construction 1. It is the
reference case that `Formal/Score/SelfStabilization.lean` (SS2) formalizes and
whose stabilization it records as the axiom `dijkstraRingSelfStabilizes` ("the
paper's proof … is not re-derived in Lean"). This model discharges that axiom
for bounded (N, K), and exhibits the symmetry-breaking finding that grounds
`obsidian/…/AgentHomogeneityFragility.md`.

Two rings, one module:

- **Heterogeneous** (Construction 1: a distinguished "bottom" machine, rule
  differs from the interior) — **self-stabilizes**.
- **Homogeneous** (every machine identical) — **cannot** self-stabilize.

## Running

Needs Java + `tla2tools.jar` (see `../../tla`-style setup, or
`obsidian/…/ModelCheckedDynamics.md`). Let `$jar = "$HOME\tools\tla2tools.jar"`.

```powershell
# Heterogeneous ring: ConvergesHet == <>[]LegitimateHet  HOLDS
java -cp $jar tlc2.TLC -config Ring.cfg    Ring.tla
#   -> Model checking completed. No error has been found. (27 states)

# Homogeneous ring: identical machines cannot stabilize
java -cp $jar tlc2.TLC -config RingHom.cfg Ring.tla
#   -> Error: Deadlock reached.  s = (0:>0 @@ 1:>0 @@ 2:>0)
#      (all-equal: zero privileges, illegitimate, no escape)
```

`N = 2, K = 3` (three machines, values 0..2, K > N per Dijkstra Note 1) gives a
27-configuration state space checked in well under a second. Raising N, K
scales as K^(N+1); the qualitative results are parameter-independent for K > N.

## What this pins down

- **Self-stabilization is now machine-checked, not axiomatized**, for the
  bounded ring: from *every* one of the 27 initial configurations, under a
  fair central daemon, the ring reaches and stays legitimate (exactly one
  privilege). Lean keeps the general ∀-statement; TLC supplies exhaustive
  evidence for the concrete instance the Lean axiom stands in for.
- **The identical-machines result is a concrete counterexample**, not a bet:
  the homogeneous ring's all-equal configuration is a reachable illegitimate
  dead end. This is the finite-state witness behind
  `AgentHomogeneityFragility.md`'s `homogeneous_no_feedback` axiom and its
  Falsifiability section.

## HOA.tla — within-basin maintenance with hysteresis

The SCORE-specific instance: `Formal/Score/HOAMaintenance.lean` §HM1–HM8,
the within-basin HOA maintenance theorem `hoaMaintainedWithin` under the
additive autocatalytic combine (`weight = substrate + endowment`, engagement
`= formation − dissolution`). Model-checked at `L=4, Formation=3,
Dissolution=2` (so `Engagement=1`), names mirroring the Lean. The distinctive
wrinkle is the **formation ≠ dissolution** hysteresis, exhibited as three
exhaustive cases at the same substrate level:

```powershell
# (1) Maintenance (§HM8) HOLDS: in-basin + feedback-engaged moves preserve HOAExists
java -cp $jar tlc2.TLC -deadlock -config HOA_Maint.cfg HOA.tla
#   -> No error has been found. (14 states)

# (2) Dissolution outside the basin: MaintInv VIOLATED (counterexample)
java -cp $jar tlc2.TLC          -config HOA_Diss.cfg  HOA.tla
#   -> Invariant MaintInv is violated.
#      State 1: substrate=2, endowment=1  ->  State 2: substrate=1  (Weight 2 < Formation)

# (3) Bistability / no spontaneous formation HOLDS
java -cp $jar tlc2.TLC -deadlock -config HOA_Bist.cfg HOA.tla
#   -> No error has been found. (unformed equilibrium: substrate=2, endowment=0)
```

What this pins down: at `substrate = Dissolution = 2`, a **formed** HOA is
maintained (case 1) while an **unformed** structure at the same substrate never
forms (case 3) — the history-dependent bistable region of `Hysteresis.md`
("the outcome depends on history, not on current conditions alone"), and
dropping below the dissolution threshold dissolves it (case 2). This discharges
`hoaMaintainedWithin` (§HM8) for the discretized additive combine, and turns
the formation ≠ dissolution asymmetry into three exhaustively-checked cases.
The §HM14/HM17 basin-extension mechanisms (B₃-substrate, composite) are not
modelled here; the §HM11 ceiling-residue extension is `HOAExt.tla` below.

## HOAExt.tla — ceiling-residue basin extension (§ 3.2)

`HOAMaintenance.lean` §HM9–HM11 + the canonical **additive × linear** discharge
(§HM18–HM19: `additiveLinearResidueAugmented` + `hoaMaintainedExtendedDerived`).
Ceiling residue (Path-A structural manifold-overlap deepening) adds a third
state dimension that **lowers the substrate a formed HOA needs**, extending the
maintenance basin *below* the formal dissolution floor. Names mirror the Lean:
`ExtWeight = substrate + endowment + residue`,
`EffDissolution = max(0, Dissolution − residue)`,
`ExtendedBasin = substrate ≥ EffDissolution`. Same `L=4, Formation=3,
Dissolution=2`; three cases:

```powershell
# (1) Extended maintenance (§HM11/§HM19 discharge) HOLDS
java -cp $jar tlc2.TLC -deadlock -config HOAExt_Maint.cfg  HOAExt.tla
#   -> No error has been found. (107 states)

# (2) Strict extension: maintained BELOW the formal dissolution floor
java -cp $jar tlc2.TLC          -config HOAExt_Strict.cfg HOAExt.tla
#   -> Invariant NeedsFullBasin is violated: substrate=0, endowment=0, residue=3
#      (HOAExists with ZERO substrate, held up entirely by ceiling residue)

# (3) Bounded / conditional extension: eroding residue dissolves the HOA
java -cp $jar tlc2.TLC          -config HOAExt_Bound.cfg  HOAExt.tla
#   -> Invariant MaintInv is violated (e.g. residue 3->2 drops ExtWeight < Formation)
```

What this pins down: the ceiling-residue mechanism **strictly** extends the
basin (`basin_implies_extendedBasin`) — a formed HOA persists at `substrate = 0`,
far below the formal `Dissolution = 2`, sustained by accumulated Path-A residue
(Hysteresis.md § 3.2). The extension is exhaustively maintenance-preserving
(case 1), reaches below the formal floor (case 2), and is conditional on
keeping the residue (case 3). This discharges `hoaMaintainedExtendedDerived`
for the additive × linear pair. The §HM17 composite extension remains
axiomatized; the §HM14 B₃-substrate extension is `HOAB3.tla` below.

## HOAB3.tla — B₃-substrate prosthetic extension (§ 3.3)

`HOAMaintenance.lean` §HM12–HM14 + the canonical **additive × linear-floored**
discharge (§HM20–HM21: `additiveLinearFlooredB3Augmented` +
`hoaMaintainedFormalExtendedDerived`). The sibling of `HOAExt.tla`: formal B₃
substrate (constitution, bylaws, roles) also lowers the substrate a formed HOA
needs (`ExtWeight = substrate + endowment + b3`), **but its effective
dissolution is floored** — `EffDissolution = max(IrreducibleMin, Dissolution −
b3)` — so it can never reach zero. That floor is the § 3.3 distinguishing
feature ceiling residue lacks. Same `L=4, Formation=3, Dissolution=2`, with
`IrreducibleMin=1`; three cases:

```powershell
# (1) Formal-extended maintenance (§HM14/§HM21 discharge) HOLDS
java -cp $jar tlc2.TLC -deadlock -config HOAB3_Maint.cfg  HOAB3.tla
#   -> No error has been found. (93 states)

# (2) Strict extension: maintained below the formal dissolution floor
java -cp $jar tlc2.TLC          -config HOAB3_Strict.cfg HOAB3.tla
#   -> Invariant NeedsFullBasin is violated: substrate=1, endowment=0, b3=2

# (3) The irreducible floor (§ 3.3 "not infinite") HOLDS
java -cp $jar tlc2.TLC -deadlock -config HOAB3_Floor.cfg  HOAB3.tla
#   -> No error has been found. (every maintained HOA has substrate >= IrreducibleMin)
```

What this pins down, and the contrast with `HOAExt.tla`: the B₃ layer strictly
extends the basin below the formal dissolution floor (case 2, `substrate=1`),
**but floors at `IrreducibleMin = 1`** (case 3 holds) — where ceiling residue's
analogous `NeedsFullBasin` was violated at `substrate = 0`. "A formal structure
rejected by all informal networks is paper without power" (`bounded_below_by_irreducible`,
§HM12), model-checked. This discharges `hoaMaintainedFormalExtendedDerived` for
the additive × linear-floored pair.

## HOAComp.tla — composite basin extension (§ 3.2 ⊕ § 3.3)

`HOAMaintenance.lean` §HM15–HM17: the composite of ceiling residue and B₃
substrate. **Unlike §HM11/§HM14, the §HM17 preservation rule is still axiomatic
in Lean** (`hoaPreservedByCompositelyExtendedBasinMove_ifFeedbackEngaged`) —
because the composition shape is unsettled (Hysteresis.md open question #2, with
three peer-selectable candidates). So this model is *ahead* of the Lean. The
state carries both extension fields; `ExtWeight = substrate + endowment +
residue + b3`; the three §HM16 compositions are `CompMin = min(EffC, EffB)`,
`CompAdd = max(0, EffC + EffB − Dissolution)`, `CompMul = (EffC·EffB) ÷ Dissolution`.
Same `L=4, Formation=3, Dissolution=2, IrreducibleMin=1`; three cases:

```powershell
# (1) Composite maintenance (additive-reductions) HOLDS -- evidence the §HM17 axiom is dischargeable
java -cp $jar tlc2.TLC -deadlock -config HOAComp_Maint.cfg   HOAComp.tla
#   -> No error has been found. (585 states)

# (2) Composition comparison HOLDS -- the three shapes ordered (open question #2)
java -cp $jar tlc2.TLC -deadlock -config HOAComp_Compare.cfg HOAComp.tla
#   -> No error has been found. (625 states, full space): all three <= min(EffC,EffB); add,mul <= min

# (3) Floor loss -- FlooredAtIrreducible VIOLATED for the composite
java -cp $jar tlc2.TLC          -config HOAComp_Floor.cfg    HOAComp.tla
#   -> Invariant FlooredAtIrreducible is violated: substrate=0, residue=1, b3=2
```

What this pins down, three things the Lean does not give: (1) exhaustive
evidence the axiomatic §HM17 preservation rule is **dischargeable** for the
additive-reductions composition (parallel to §HM19/§HM21); (2) a machine-checked
**comparison** of the three candidate compositions — all bounded above by
`min(EffC, EffB)` (`bounded_above_by_min`, §HM15), with additive and
multiplicative strictly more permissive — concretely informing open question #2;
and (3) the **floor is lost** — composing the floorless ceiling mechanism with
the floored B₃ mechanism removes the irreducible floor (`substrate = 0` reachable
and maintained), where B₃ alone held it (`HOAB3_Floor.cfg`). Exact multiplicative
maintenance needs rational arithmetic, so `CompMul` is used only in the
comparison; that is the one modelling boundary here.

## LifeCycle.tla — A-actor life-cycle (Core.lean `LifeCyclePhase`)

The individual life-cycle Childhood → Student → Householder → Retirement (encoded
`0..3`), with `coupling` the local (HOA-relevant) coupling weight. Core.lean has
the phase enum, `hasSponsorship`, and `localCouplingAccumulates`; the transition
dynamics are unformalized. `L=3`; two cases:

```powershell
java -cp $jar tlc2.TLC -deadlock -config LifeCycle_Mono.cfg    LifeCycle.tla
#   -> No error (10 states): Monotone HOLDS -- phase and coupling never decrease,
#      and coupling accumulates only in the settled (phase>=2) phases.
java -cp $jar tlc2.TLC -deadlock -config LifeCycle_Sponsor.cfg LifeCycle.tla
#   -> NoPeakSponsor VIOLATED: trace to the peak-coupling Retirement SPONSOR
#      (the HOA-attractor-maintaining agent), via the accumulation phases.
```

## SigmaLifeCycle.tla — Σ-actor life-cycle (Sigma.lean §29 `SigmaLifeCyclePhase`)

The collective life-cycle Formation → Maturity → Crossover → Death → Reinvention
as a **closure-driven** state machine over a dual layer: a `formal` (B₃, higher
stratum) and an `informal` (B₂, lower stratum) layer, closure being their mutual
maintenance (`FormalInformalClosure.md` § "Lifecycle derivation"). Sigma.lean has
only the phase enum; the dynamics are here. `L=3, Theta=2`; three cases:

```powershell
java -cp $jar tlc2.TLC -deadlock -config SigmaLifeCycle_Strat.cfg SigmaLifeCycle.tla
#   -> No error (25 states): Stratification HOLDS -- a live (Maturity) closure
#      requires BOTH layers stable; the formal (higher stratum) is live only on a
#      stable informal (lower stratum). "Higher strata only on stable lower strata."
java -cp $jar tlc2.TLC -deadlock -config SigmaLifeCycle_Shell.cfg SigmaLifeCycle.tla
#   -> No error (25 states): ReinventionNeedsShell HOLDS -- reinvention only within
#      a surviving formal shell (informal-collapse death), never after formal
#      dissolution (IBM-under-Gerstner).
java -cp $jar tlc2.TLC -deadlock -config SigmaLifeCycle_Reach.cfg SigmaLifeCycle.tla
#   -> NeverReinvents VIOLATED: TLC emits the full trajectory Formation -> Maturity
#      -> Crossover -> Death (informal collapse; formal shell persists) ->
#      Reinvention. The co-inscription gate (formal rises only after informal>=Theta)
#      is visible in the trace -- stratification in action.
```

What these pin down: the **stratification constraint** ([[SO-NS-Stratification]]) —
model-checked as a global invariant of the Σ-actor closure — and the two
mechanisms that carry it (co-inscription gating; live closure requiring both
layers), plus the shell-dependence of reinvention that distinguishes the two
death pathways. The A-actor model contributes the monotone phase progression and
the phase-gating of coupling accumulation that produces the Retirement sponsor —
the agent role that maintains the HOA attractors of the earlier pilots.
