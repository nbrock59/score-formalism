# formal/prism — probabilistic model-checked SCORE dynamics (PRISM)

The **quantitative** rung of the model-checking layer. Where `formal/tla` (TLC)
and `formal/spin` (SPIN) answer *qualitative* questions on the SCORE dynamics —
does it converge, is it maintained, can it deadlock — a probabilistic model
checker answers the questions POLARIS's early-warning mission actually asks:
with what **probability** does an HOA dissolve within a horizon, what is the
**expected time** to the discontinuity, and does the **critical-slowing-down**
premise behind [[SpectralEarlyWarningIndicator|SEWI]] hold on a generative
model. Methodology + scope: `obsidian/SCORE/methodology/ModelCheckedDynamics.md`
("Probabilistic model checking (PRISM/Storm)").

The division of labour extends the TLA table:

| | Lean (`Formal/Score/`) | TLC / SPIN | PRISM (`formal/prism/`) |
|---|---|---|---|
| Question | general theorem | qualitative reachability / liveness | **quantitative** probability / time |
| Answer | proof (∀) | holds / counterexample trace | a **number** (risk, expected time) |
| Reaches | theory spine | theory dynamics | the **measurement layer** (SEWI, Segments) |

## The one new governance constraint — the pre-registration lock

Unlike every TLC/SPIN pilot, this layer touches the empirical measurement side,
so it carries a caveat they did not. SEWI's thresholds (Warning 1.5 / Critical
1.8), the `create_rhythm` β = 0.005 dosing, and the `ψ_s` validity flag (0.3)
are **locked pre-registered parameters** (`validation/pre-registration/`);
changing them needs the §7 amendment protocol. **The rates in these models are
illustrative structural parameters — never a redefinition of a locked number.**
Model ① is structural validation of the early-warning *shape* (does critical
slowing down precede dissolution), not a calibrated threshold/dosing claim. Per
[[SemanticSeepage]] the map from POLARIS's continuous/spectral dynamics to a
discrete CTMC is a flagged abstraction, not an identity.

## HOADissolution.sm — stochastic HOA dissolution + early warning (CTMC)

Model ① of the scope note: the **probabilistic lift of `formal/tla/HOA.tla`**
(Lean: `Formal/Score/HOAMaintenance.lean` §HM1–HM8). Discretization mirrors
`HOA.tla` exactly (`substrate, endowment ∈ 0..L`; `L=4, Formation=3,
Dissolution=2, Engagement=1`; `Weight = substrate + endowment`); the
nondeterministic ±1 `HOAMove` becomes a **race of exponential transitions** —
the stochastic microdynamics the Lean leaves as `axiom HOAMove`:

- **intrinsic decay** — mass-action erosion (rate `decay × level`). `decay` is
  the **slow control parameter** swept for the early-warning experiment: rising
  `decay` = rising structural stress on the basin.
- **autocatalytic feedback** — the §HM6 loop replenishes (rate `grow`): engaged
  endowment regrows substrate, an in-basin substrate regrows endowment. The
  mutual substrate↔endowment autocatalysis that makes a formed HOA persist.
- **exogenous shock** — an occasional larger drop (rate `shock`): the external
  stress event the early-warning layer exists to anticipate.

`RESIDUE` (const) is the §HM11 ceiling-residue extension of `formal/tla/HOAExt.tla`
lifted to CTMC form — accumulated Path-A residue lowers the effective dissolution
floor (`EffDissolution = max(0, Dissolution − RESIDUE)`), so a residue-endowed
HOA must erode further before it dissolves ([[DynamicFailureSets]]).

Per-experiment constants (`INIT_S`, `INIT_E`, `ABSORB`, `RESIDUE`, `decay`) are
**undefined in the model and passed on the command line**, the way each
`formal/tla/*.cfg` declares its `Init`. `ABSORB=1` makes dissolution absorbing
(first-passage: probability, expected time); `ABSORB=0` leaves the chain
reflecting (for the recovery experiment).

## Running

PRISM 4.10.1 (Java; the JRE is already installed for TLC). The Windows
`bin/prism.bat` sets `PRISM_DIR=..` relatively, so invoke it **from its own
`bin/` directory** with absolute paths to the model/properties. Let
`$PRISM = "C:\Program Files\prism-4.10.1\bin\prism.bat"`,
`$M`/`$P` the absolute paths to `HOADissolution.sm` / `HOADissolution.csl`.

```powershell
# (A) EARLY-WARNING DOSE-RESPONSE — dissolution risk + timescale vs stress.
#     P1 P[dissolve<=T], P2 E[time to dissolve], P3 survival. Healthy formed start.
& $PRISM $M $P -property 1 -const decay=0.2:0.2:1.0,T=10,ABSORB=1,INIT_S=3,INIT_E=2,RESIDUE=0
#   -> decay 0.2..1.0 : P[dissolve<=10] = 0.399, 0.895, 0.993, 0.99978, 0.999995
& $PRISM $M $P -property 2 -const decay=0.2:0.2:1.0,ABSORB=1,INIT_S=3,INIT_E=2,RESIDUE=0
#   -> E[time to dissolution] = 19.82, 4.67, 2.33, 1.51, 1.11   (timescale COLLAPSE)

# (B) CRITICAL SLOWING DOWN — recovery gets harder as stress rises.
#     P4 P[recover<=T before dissolving]. Perturbed-but-alive start (weight=4).
& $PRISM $M $P -property 4 -const decay=0.2:0.2:1.0,T=10,ABSORB=1,INIT_S=2,INIT_E=2,RESIDUE=0
#   -> P[recover<=10] = 0.758, 0.506, 0.330, 0.223, 0.158   (recovery slows = CSD)

# (b) CEILING RESIDUE (§HM11) — residue lengthens lifetime / lowers dissolution.
& $PRISM $M $P -property 2 -const RESIDUE=0:1:2,decay=0.4,ABSORB=1,INIT_S=3,INIT_E=2
#   -> E[time to dissolution] = 4.67, 5.23, 5.38   (RESIDUE 0,1,2)

# (E) HYSTERESIS CONTRAST — spontaneous formation from an unformed-window start.
#     Non-absorbing chain (ABSORB=0), P5 read as P[form]. See scope boundary below.
& $PRISM $M $P -property 5 -const decay=0.2:0.2:1.0,ABSORB=0,INIT_S=2,INIT_E=0,RESIDUE=0
#   -> P[form<=10] = 0.560, 0.276, 0.123, 0.057, 0.029
```

## What this pins down

The three payoffs the scope note names for model ①:

- **(c) the SEWI early-warning premise — validated, and the headline.** As the
  stress control parameter rises toward the feedback rate, the expected
  time-to-dissolution **collapses** (19.8 → 1.1) and the within-horizon
  dissolution probability rises to near-certainty — the characteristic timescale
  diverging away from the bifurcation and collapsing at it. Independently, the
  within-horizon **recovery** probability from a perturbed state falls
  monotonically (0.76 → 0.16): recovery slows as the transition nears. That
  slowing recovery is exactly the leading indicator (rising variance /
  autocorrelation) SEWI operationalizes — here computed directly on a generative
  model, not assumed. This is the first pilot to reach POLARIS's actual mission.
- **(b) the §HM11 ceiling-residue extension — quantified.** Accumulated Path-A
  residue strictly lengthens expected lifetime (4.67 → 5.38 as RESIDUE 0→2 at
  fixed stress) and lowers dissolution probability. The TLC model
  (`HOAExt.tla`) showed the basin *extends*; PRISM says *by how much* in
  probability/time.
- **(a) the hysteresis asymmetry — partial, with an honest boundary.** The model
  captures the maintenance-basin side cleanly: a formed structure at
  `substrate = Dissolution` is basin-attracted (recovers with prob 0.76 at low
  stress) while dissolution is a first-passage over a barrier. But it does **not**
  reproduce a *stable unformed equilibrium* — with unconstrained stochastic
  feedback, an unformed-window structure still climbs and forms (prob 0.56 at low
  stress). `HOA.tla` case 3 got bistability only by *constraining* moves to stay
  disengaged; a stochastic chain needs an explicit **nucleation barrier**
  (formation gated on a threshold, not on the linear feedback of maintenance) to
  hold the unformed state. **This is now closed** by the refinement
  `HOANucleation.sm` (below).

## Scope boundary — what this does and does not add

- **Bounded, illustrative, structural.** Like TLC/SPIN, PRISM checks a concrete
  bounded instance (`L=4`), not an unbounded proof. The rates are illustrative
  (governance note above); the *shape* of the results — timescale collapse,
  slowing recovery, residue-extended lifetime — is the claim, not the specific
  numbers.
- **Does not touch the locked pre-registered parameters.** No SEWI threshold,
  β dosing, or ψ_s flag is redefined, computed, or calibrated here.
- **A stable unformed equilibrium** (full bistability) is not in *this* CTMC —
  it is the refinement `HOANucleation.sm` (next section). The **intervention MDP**
  built on top of this state is model ②, `InterventionMDP.nm` below.

## HOANucleation.sm — HOA bistability with a nucleation barrier (model ① refinement)

Closes model ①'s hysteresis payoff (a). Model ①'s endowment feedback grew on the
linear `inbasin` condition, so an unformed structure climbed and **formed for
free** (P ≈ 0.56) — no stable unformed equilibrium. The one change here: the
autocatalytic loop reinforces itself **only once already nucleated** — both feedback
transitions are gated on `maintained` (= in-basin *and* engaged), not on `inbasin`.
Below the threshold, only a weak exploratory `seed` (random coupling attempts,
`seed < decay`) pushes up against mass-action decay. The result is a genuine
**double-well**: the unformed state is a metastable attractor, and formation is a
rare **barrier crossing** rather than a free climb — the bistability `HOA.tla` case 3
asserts, now run on a generative stochastic chain. (Non-absorbing: the first-passage
times *between* the wells are the metastability signature.)

```powershell
# BARRIER CONTROL — seed (barrier height) sets the formation rate. Unformed floor start.
& $PRISM $Mn $Pn -property 1 -const grow=1.0,seed=0.05:0.05:0.20,INIT_S=0,INIT_E=0,T=10
#   P[form<=10] -> 0.026, 0.134, 0.299, 0.475   (vs model ①'s 0.56 with NO barrier)
& $PRISM $Mn $Pn -property 2 -const grow=1.0,seed=0.05:0.05:0.20,INIT_S=0,INIT_E=0
#   mean time to nucleation -> 530, 100, 43, 25   (barrier height as a timescale)

# BISTABILITY (canonical seed=0.10) — both wells metastable, formation ≠ dissolution.
& $PRISM $Mn $Pn -property 2 -const grow=1.0,seed=0.10,INIT_S=0,INIT_E=0   # nucleation time -> 100.3
& $PRISM $Mn $Pn -property 3 -const grow=1.0,seed=0.10,INIT_S=4,INIT_E=2   # dissolution time -> 11.1
& $PRISM $Mn $Pn -property 4 -const grow=1.0,seed=0.10,INIT_S=0,INIT_E=0   # steady-state P[formed] -> 0.107
```
(`$Mn`/`$Pn` = absolute paths to `HOANucleation.sm` / `HOANucleation.csl`.)

### What this pins down — payoff (a), delivered

- **A stable unformed equilibrium now exists.** Spontaneous formation from the
  unformed floor collapses from model ①'s **0.56** to **0.026** at a high barrier
  (`seed=0.05`) — a ~22× reduction — and the mean time to nucleate stretches to
  **~530** time units. The unformed state is a genuine metastable attractor, not
  a way-station on a free climb.
- **The barrier height is the control.** Sweeping `seed` moves formation
  probability monotonically (0.026 → 0.475) and the nucleation timescale across an
  order of magnitude (530 → 25). This is exactly the knob `create_rhythm` turns in
  the theory — priming the manifold *lowers the nucleation barrier* — connecting
  this CTMC to model ②'s sequencing result.
- **Genuine bistability: formation ≠ dissolution, both rare.** At `seed=0.10` the
  mean time to nucleate (100.3) is ~9× the mean time to dissolve (11.1): both
  wells are metastable, formation is the rarer transition, and the steady-state
  formed-occupancy (0.107) matches the dwell-time ratio (11.1/100.3 ≈ 0.11) — the
  internal-consistency signature of a two-well system. Model ① gave the
  dissolution well only; this adds the second well `HOA.tla` case 3 demands.

### Scope boundary (nucleation refinement)

- **Illustrative, structural, bounded.** `seed`, `grow`, `decay` are ordinal
  placeholders; the claim is the *shape* — a tunable barrier producing two stable
  wells with formation ≠ dissolution — not the numbers. No locked pre-registered
  parameter is touched.
- **A minimal barrier, not a mechanism menu.** The nucleation gate is the single
  `maintained` threshold; richer nucleation (an explicit critical-seed size,
  heterogeneous seeds, or `create_rhythm` as an on-model barrier-lowering action)
  is left open — the last of these is the natural bridge to model ②.

## InterventionMDP.nm — intervention-policy MDP (model ②, → Segment 7)

Model ② of the scope note, and the first pilot to reach **Segment 7** (the
intervention design layer). It puts model ①'s HOA state underneath as the
**environment** — the `substrate`/`endowment` coupling state and its autocatalytic
maintenance — and layers the intervention operators of [[InterventionClasses]] on
top as MDP **actions** with activation-energy **costs**. The MDP nondeterminism
is the intervention *policy*; PRISM computes the **optimal** one (`Rmin`, `Pmax`)
and thereby **checks the theory's own claims** rather than assuming them. Actions
alternate with an environment turn (`turn` flag) that runs model ①'s dynamics — a
formed+engaged HOA self-maintains (regrows), everything else erodes.

- `create_rhythm` (cost Low) — somatic channel, sets `prepared`, which raises
  `create_node`'s success probability (the sequencing principle).
- `create_edge` (cost Medium) — partial bypass, raises substrate.
- `create_node` (cost High) — the crystallization snap, but lands reliably only
  on a **prepared** manifold or a **retirement** target (`PHASE=1`); otherwise
  fully perceptually filtered.
- `dissolve` (subtractive `dissolve_node`) — its leverage is indexed by the
  *target's state*, not operator depth: cheap against a nascent structure, dear
  against a self-maintaining one, because the environment regrows the latter.

Per-experiment consts (`PHASE`, `ALLOW_RHYTHM`, `INIT_S`, `INIT_E`) are passed on
the CLI. The objective label `established` = a **self-sustaining** (maintained)
HOA, not a transient weight blip.

```powershell
# (1) SEQUENCING — create_rhythm before create_node lowers expected cost.
#     Rmin{cost} to establish, from a nascent structure, householder phase:
& $PRISM $M2 $P2 -property 2 -const PHASE=0,ALLOW_RHYTHM=1,INIT_S=1,INIT_E=0   # -> 4.57
& $PRISM $M2 $P2 -property 2 -const PHASE=0,ALLOW_RHYTHM=0,INIT_S=1,INIT_E=0   # -> 20.00
#   rhythm enabled is ~4.4x cheaper — the optimal policy primes then nodes.

# (2) LIFE-CYCLE SPONSOR — retirement-phase targets cost less (no rhythm):
& $PRISM $M2 $P2 -property 2 -const PHASE=0,ALLOW_RHYTHM=0,INIT_S=1,INIT_E=0   # -> 20.00 (householder)
& $PRISM $M2 $P2 -property 2 -const PHASE=1,ALLOW_RHYTHM=0,INIT_S=1,INIT_E=0   # ->  5.56 (retirement)

# (3) ASYMMETRIC LEVERAGE — prevention << dissolution. Rmin{cost} to suppress:
& $PRISM $M2 $P2 -property 3 -const PHASE=0,ALLOW_RHYTHM=0,INIT_S=2,INIT_E=0   # -> 3.57 (nascent / prevention)
& $PRISM $M2 $P2 -property 3 -const PHASE=0,ALLOW_RHYTHM=0,INIT_S=4,INIT_E=2   # -> 7.57 (maintained / dissolution)
```
(`$M2`/`$P2` = absolute paths to `InterventionMDP.nm` / `InterventionMDP.pctl`.)

### What this pins down — the three theory claims, derived not assumed

- **Sequencing ([[InterventionClasses]] "Sequencing principle") — confirmed.**
  With `create_rhythm` available the optimal policy's expected activation energy
  to establish a self-sustaining HOA is **4.57 vs 20.0** without it (~4.4×). The
  cheap somatic prep that raises `create_node`'s hit rate beats brute-forcing the
  expensive node unprepared — PRISM *derives* the rhythm-before-node ordering from
  cost-minimization. (The differential is itself the proof the optimal policy
  sequences that way.) Establishment is achievable with probability 1 (`Pmax=1`)
  yet not automatic (`Pmin=0`).
- **Life-cycle sponsor ([[LifeCyclePhases]]) — confirmed.** A retirement-phase
  target costs **5.56 vs 20.0** for a householder (~3.6×): the sponsor's
  established local coupling lets `create_node` land without priming.
- **Asymmetric leverage ([[Hysteresis]] "Interventional consequence") —
  confirmed, directionally.** Suppressing a nascent, not-yet-maintaining structure
  costs **3.57**; dissolving a formed, self-maintaining HOA costs **7.57**
  (~2.1×), because the subtractive action must outpace autocatalytic regrowth
  while the target stays maintained. Prevention < dissolution, as Hysteresis
  predicts. The ratio is modest — regrowth only fights back while the target
  remains maintained — an honest bound, not a tuned headline. This is the
  subtractive family's *state-indexed* cost ([[InterventionClasses]] VC-1 key
  finding) made quantitative.

### Scope boundary (model ②)

- **Illustrative, structural, bounded** — as everywhere in this layer. The costs
  and probabilities are ordinal placeholders; the **claim is the ordering** the
  optimal policy reproduces (rhythm<node sequencing, retirement<householder,
  prevention<dissolution), not the specific numbers. **No locked pre-registered
  parameter** (the `create_rhythm` β=0.005 dosing, SEWI thresholds, ψ_s flag) is
  redefined or calibrated.
- **Additive family + one subtractive operator.** Model ② has only
  `dissolve_node` on the subtractive side; the **full subtractive family** is the
  extension `HOASubtractive.nm` (next section). The B₃-mediated channel (the other
  unworked cell of [[InterventionClasses]]'s 2×2) is still not modelled.
  `create_edge`-before-`create_node` in infrastructure-severed sub-communities is
  representable but not separately exercised here.
- **A cost-free `wait` was deliberately omitted** — it is a zero-reward loop that
  makes `Rmin` ill-posed (a policy could stall forever at zero cost), and waiting
  only ever lets the environment erode the objective.

## HOASubtractive.nm — the subtractive intervention family (model ② extension)

Extends model ② to the **full subtractive family** of [[InterventionClasses]]
"The subtractive family" (VC-1): `disrupt_rhythm`, `sever_edge`, `dissolve_node`.
It checks that family's key finding — **the additive activation-energy ordering
(rhythm < edge < node) does not survive negation**. The additive family is ordered
by *what you build*; the subtractive family by *what the target has accumulated* —
the three [[Hysteresis]] persistence mechanisms in window-width order:
autocatalytic weight < ceiling residue ([[CeilingResidue]], §HM11) < B₃ formal
prosthetic ([[B3SubstrateProsthetic]], §HM14, floored, "paper without power").

The target carries all three as state (`s`+`e` autocatalytic, `residue`, `b3`);
the operators act on the same three primitives, negated. `disrupt_rhythm` is
**rhythm-class**: it bypasses the perceptual filter in *both* polarities
(`only_rhythm_class_bypasses_filter`), so it lands reliably (P=0.95); `dissolve_node`
is filter-**resisted** (defensive mobilization, P=0.60). A **load-bearing B₃
prosthetic re-staffs the informal loop** on the environment turn — the formal
structure regenerates the endowment — so `disrupt_rhythm` is undone until B₃ is
ground below its floor. That is why a B₃-backed node is "very hard to kill."
Operator costs are deliberately **near-flat** (there is no rhythm<edge<node cost
order to encode — `activationEnergy` is `none` on this family).

```powershell
# HEADLINE (VC-1): Rmin{cost} to SUPPRESS, indexed by the TARGET's persistence.
& $PRISM $Ms $Ps -property 1 -const INIT_S=4,INIT_E=2,INIT_RES=0,INIT_B3=0,ALLOW_DR=1,ALLOW_SE=1,ALLOW_DN=1  # autocatalytic-only -> 5.15
& $PRISM $Ms $Ps -property 1 -const INIT_S=4,INIT_E=2,INIT_RES=2,INIT_B3=0,ALLOW_DR=1,ALLOW_SE=1,ALLOW_DN=1  # + ceiling residue  -> 6.25
& $PRISM $Ms $Ps -property 1 -const INIT_S=4,INIT_E=2,INIT_RES=0,INIT_B3=3,ALLOW_DR=1,ALLOW_SE=1,ALLOW_DN=1  # + B3 prosthetic    -> 7.43

# ORDERING DOES NOT SURVIVE NEGATION: which single operator SUFFICES (Pmax) depends on the target.
& $PRISM $Ms $Ps -property 2 -const INIT_S=4,INIT_E=2,INIT_RES=0,INIT_B3=0,ALLOW_DR=1,ALLOW_SE=0,ALLOW_DN=0  # disrupt only -> 1.0 (suffices)
& $PRISM $Ms $Ps -property 2 -const INIT_S=4,INIT_E=2,INIT_RES=0,INIT_B3=0,ALLOW_DR=0,ALLOW_SE=1,ALLOW_DN=0  # sever only   -> 0.0 (fails!)
& $PRISM $Ms $Ps -property 2 -const INIT_S=4,INIT_E=2,INIT_RES=2,INIT_B3=0,ALLOW_DR=1,ALLOW_SE=1,ALLOW_DN=0  # no node, residue target -> 0.0
```
(`$Ms`/`$Ps` = absolute paths to `HOASubtractive.nm` / `HOASubtractive.pctl`.)

### What this pins down — VC-1, made quantitative

- **Dissolution cost is indexed by accumulated persistence, not operator depth.**
  Min expected activation energy to suppress the *same* formed HOA rises
  **5.15 (autocatalytic-only) → 6.25 (+ceiling residue) → 7.43 (+B₃ prosthetic)** —
  the Hysteresis window-width order. The operator costs are near-flat, so the
  ordering comes entirely from the target's composition. A composite (residue +
  B₃) target also costs 7.43: `dissolve_node` clears residue as *collateral* while
  grinding the prosthetic, so the prosthetic is the binding constraint — the
  residue adds nothing once you are already dismantling the formal structure.
- **The additive ordering does not survive negation.** Which single operator
  *suffices* depends on the target, not on rhythm<edge<node: against an
  autocatalytic-only target `disrupt_rhythm` alone suppresses (Pmax=1 — kill the
  loop, decay finishes) while `sever_edge` alone **fails** (Pmax=0 — it cannot
  disengage the loop, so the substrate regrows). The additive-*middle* operator is
  useless where the additive-*cheapest* works. Against a residue target
  `dissolve_node` is **required** (only it erodes the residue stock); disrupt+sever
  can never finish (Pmax=0).
- **`disrupt_rhythm` bypasses the filter in both polarities.** It lands reliably
  (P=0.95, no defensive gate) where `dissolve_node` is resisted (P=0.60), and it
  is the *efficient* subtractive tool for a loose autocatalytic target — the
  all-operator optimum (5.15) beats `dissolve_node`-only (7.11) by leaning on the
  cheap rhythm-class disruptor. This is `only_rhythm_class_bypasses_filter` (the
  polarity-independent successor to the additive-only theorem) shown on-model.

### Scope boundary (subtractive extension)

- **Illustrative, structural, bounded.** Costs/probabilities are ordinal; the
  claim is the *ordering by target persistence* and the *sufficiency pattern*, not
  the numbers. No locked pre-registered parameter is touched.
- **Co-present channel only.** Still the additive/subtractive × co-present cell;
  the **B₃-mediated channel** (the other axis of [[InterventionClasses]]'s 2×2)
  remains unworked — the last open extension in this family.
- **`composite ≥ B₃` is a tie here**, an artifact of `dissolve_node` doing double
  duty (grinding B₃ and eroding residue in one hit); a model that separated those
  teardowns would make the composite strictly dearest.

## AgentLearning.sm — Path-A/B agent-learning dynamics (model ③, → Segment 1)

Model ③, connecting **Segment 1** (the HistoricalSlice learning dynamics) and the
Brock (2026) computational baseline it validates against. A DTMC over an agent's
position on the honor(System I)↔dignity(System II) ethical axis
([[AgentResponseMechanism]] "Path A and Path B"; Segment 1 §§3.2–3.3, 4.5):

- **Path A** (organic vector `u`) — the durable, structural channel. Moves toward
  the dignity attractor at rate `α_A·κ`, where organic plasticity `κ` **decays
  with age**. Low-pass, monotone, and *not reachable by inscription* (the organic
  manifold cannot be deformed by Path B).
- **Path B** (inscribed vector `w`) — the fast, fragile channel. Chases the
  inscription signal `SIG` at rate `α_B` with **no `κ` term** (frequency-flat,
  no plasticity decay), but reverts to `u` absent reinforcement.
- **Generational turnover** — `age` cycles the four [[LifeCyclePhases]]; at the
  top it rebirths (plasticity restored, organic base `u` transmitted), the
  **multigenerational ratchet** that carries `u` to the attractor.

The honor-topology departures (Brexit/Trump/populism) live entirely in the
inscribed `w` under an honor signal `SIG=0` — never in the organic `u`, exactly
Segment 1 §4.5's framing.

```powershell
# (1) MULTIGENERATIONAL ATTRACTOR — Finding 25: converge to dignity from ANY start.
& $PRISM $M3 $P3 -property 1 -const kdecay=0.3,INIT_U=0,INIT_W=0,SIG=0,ALLOW_INSCRIPTION=1  # -> 1.0
#   (same 1.0 for INIT_U = 1, 2, 3; expected steps to converge from deep honor ≈ 21)

# (2) PATH A DURABLE vs PATH B FRAGILE — steady-state honor occupancy.
& $PRISM $M3 $P3 -property 5 -const kdecay=0.3,INIT_U=0,INIT_W=0,SIG=0,ALLOW_INSCRIPTION=1  # -> 0.0 (organic never stays honor)
& $PRISM $M3 $P3 -property 6 -const kdecay=0.3,INIT_U=4,INIT_W=0,SIG=0,ALLOW_INSCRIPTION=1  # -> 0.64 (stated held at honor while reinforced)
& $PRISM $M3 $P3 -property 6 -const kdecay=0.3,INIT_U=4,INIT_W=0,SIG=0,ALLOW_INSCRIPTION=0  # -> 0.0  (collapses when withdrawn)

# (3) PLASTICITY-DECAY ASYMMETRY — Finding 29: Path A slows, Path B unchanged.
& $PRISM $M3 $P3 -property 2 -const kdecay=0.1:0.1:0.4,INIT_U=0,INIT_W=0,SIG=0,ALLOW_INSCRIPTION=1  # steps -> 14.8, 17.1, 21.0, 25.9
& $PRISM $M3 $P3 -property 4 -const kdecay=0.1:0.1:0.4,INIT_U=4,INIT_W=4,SIG=0,ALLOW_INSCRIPTION=1,T=20  # -> 0.747 (FLAT)
```
(`$M3`/`$P3` = absolute paths to `AgentLearning.sm` / `AgentLearning.csl`.)

### What this pins down — Segment 1 / Brock (2026) learning results

- **The multigenerational attractor (Finding 25) — confirmed.** Organic
  commitment reaches the dignity attractor with **probability 1 from every
  starting position** (deep honor to near-dignity), over an expected ~21-step
  multigenerational timescale. "Starting from any System I majority … all
  communities converge to dignity-topology dominance regardless of
  within-generation dynamics", run rather than asserted.
- **Path A durability vs Path B fragility (§§3.2–3.3) — confirmed.** The organic
  position's steady-state honor occupancy is **0.0** (behavioral commitment,
  once at dignity, is durable), while the inscribed position is held at honor
  with probability **0.64 under active inscription but collapses to 0.0 the
  moment reinforcement is withdrawn**. The inscribed channel has no steady state
  of its own — "stated positions shift while behavioral commitments remain
  inertial."
- **The plasticity-decay asymmetry (Finding 29) — confirmed, and the sharpest
  result.** As organic plasticity decays faster (`kdecay` 0.1→0.4) the expected
  time for Path A to reach the attractor **rises 14.8 → 25.9**, while Path B
  responsiveness stays **flat at 0.747 to 15 significant figures** — invariant to
  `κ` because Path B carries no plasticity term. "Path A displacement halves
  across the κ-decay range while Path B displacement is unchanged", made exact.

### Scope boundary (model ③)

- **Illustrative, structural, bounded** — as everywhere in this layer. The
  discretization of Segment 1's `S¹⁵` continuous idea vectors onto a single
  0..K axis is a flagged [[SemanticSeepage]] abstraction; the **claim is the
  qualitative shape** (probability-1 multigenerational convergence, durable/fragile
  split, κ-decay asymmetry), not the specific rates. **No locked pre-registered
  parameter** (`α_A`/`α_B`, the `φ_threshold` percolation calibration) is redefined.
- **Single-agent axis, not the full MABM.** One agent on one ethical dimension
  with a scalar inscription signal — not Brock (2026)'s multi-agent manifold on
  `S¹⁵`, the Φ percolation/crystallization dynamics, or the population network.
  Convergence here is the *within-lineage* ratchet; the population-level
  p = 0.999 result is its many-agent aggregate.


## MediatedChannel.sm — the B₃-mediated intervention channel (model ② extension)

Completes the [[InterventionClasses]] 2×2 by working its second axis: the
**B₃-mediated channel**. Models ② and `HOASubtractive` deliver interventions
through the **co-present** channel (bodies in a room — supra-threshold,
perceptible, contestable, but scale-ceilinged, [[EmbodiedCoPresence]]). The
mediated channel delivers through inscription/platform infrastructure
([[IncorporationAsymmetry]]) — a "degenerate continuous `create_rhythm`" whose
distinctive structure is **two-threshold self-masking**: sub-threshold in
*amplitude* (below the perceptibility floor `δᵢ` → imperceptible → **non-contestable**,
Theorem DI-A) and super-threshold only in *accumulated timescale* (the tiny nudge
accumulates at **low frequency**). Composed with model ③'s Path-A/B learning, the
mediated shift is durable only where plasticity is high — so its durable reach is
**cohort formation**, not persuasion of the settled.

```powershell
# SELF-MASKING + REMEDY (DI-A/DI-B): sweep the perceptibility floor δᵢ at fixed amplitude.
& $PRISM $Mc $Pc -property 1 -const amp=0.1,delta=0.15,PLASTIC=1   # sub-threshold  -> P[captured]=1.0,  P[contested]=0.0
& $PRISM $Mc $Pc -property 1 -const amp=0.1,delta=0.10,PLASTIC=1   # perceptible    -> P[captured]=0.06, P[contested]=0.94

# SPECTRAL: a short window is a high-pass filter. P[F<=T captured], sub-threshold.
& $PRISM $Mc $Pc -property 3 -const amp=0.1,delta=0.15,PLASTIC=1,T=10   # -> 0.013 (short window: ~null)
& $PRISM $Mc $Pc -property 3 -const amp=0.1,delta=0.15,PLASTIC=1,T=100  # -> 0.99  (long window: sees it)

# COHORT: durable capture needs plasticity. Steady-state S=?[captured], sub-threshold.
& $PRISM $Mc $Pc -property 4 -const amp=0.1,delta=0.15,PLASTIC=1   # young   -> 1.0
& $PRISM $Mc $Pc -property 4 -const amp=0.1,delta=0.15,PLASTIC=0   # settled -> 0.008
```
(`$Mc`/`$Pc` = absolute paths to `MediatedChannel.sm` / `MediatedChannel.csl`.)

### What this pins down — the mediated channel's three signatures

- **Self-masking ⇒ non-contestable (DI-A), and the disclosure remedy (DI-B).**
  While the steering amplitude is below `δᵢ` it reaches the manifold with
  **probability 1, never contested** (`P[contested]=0`); the instant `δᵢ` drops to
  or below the amplitude — the perceptibility-restoration remedy, i.e. disclosure —
  contestability flips (`P[contested]=0.94`, `P[captured]` collapses to 0.06). A
  sharp threshold at `δᵢ = amp`. The perceptible-case 0.0625 = (amp/(amp+p_detect))⁴
  is an exact analytic check (win the steer-vs-detect race K=4 times).
- **The spectral signature — a short window is a high-pass filter.** Sub-threshold
  capture probability rises **0.0001 → 0.013 → 0.13 → 0.75 → 0.99** across windows
  T = 4, 10, 20, 50, 100: a short-window RCT sees essentially the null while the
  effect is near-certain over a long horizon. This is why the platform-effects
  literature splits by design — short crossover studies null, low-frequency
  designs positive — as [[IncorporationAsymmetry]] predicts (the Segment-6 band).
- **Cohort formation — durable capture needs the young.** Steady-state capture is
  **1.0 for a high-plasticity (young) agent** (the shift locks, Path A) but only
  **0.008 for a settled agent** (Path-B fragile, reverts). The mediated channel
  durably captures the young and only transiently nudges the settled — the
  strong-form "owns the formation environment of the next generation"
  ([[IncorporationAsymmetry]] via [[LifeCyclePhases]]/[[MortalityBoundary]]),
  composing directly with model ③'s plasticity/κ.

### Scope boundary (mediated channel)

- **Illustrative, structural, bounded.** `amp`/`δᵢ`/`p_detect`/`p_revert` are
  ordinal; the claims are the *contestability flip at δᵢ = amp*, the *low-frequency
  ramp*, and the *plasticity-gated durability*, not the numbers. **No locked
  pre-registered parameter** (`δᵢ`, `ψ_s` flag, SEWI thresholds) is redefined.
- **Single-agent, so reach/scale is noted not modelled.** The co-present scale
  ceiling vs mediated scalability is a *population* claim; this chain models one
  steered agent and the channel's per-agent contestability/durability structure.
  The full population reach contrast and the multi-owner plurality bound
  ([[IncorporationAsymmetry]] bound ii) are left open.

With this, the [[InterventionClasses]] 2×2 is worked in all four cells (additive
and subtractive × co-present and mediated).


## MabmPercolation.sm — multi-agent Φ crystallization / percolation (model ③ → MABM)

Model ③ toward the full multi-agent MABM (Brock 2026, Part III). Model ③
(`AgentLearning.sm`) was *single-agent* — it could show the within-lineage
multigenerational ratchet but **not** the genuinely population-level object: HOA
crystallization via percolation. Segment 1 §§2.2–2.3 defines
`Φ = f_giant × ρ_cycle × w̄` and states that oral-social crystallization is a
**discontinuous percolation transition** at ε* ≈ 0.30–0.35 — "a cliff, not a
slope" (Erdős–Rényi). HOAs form where B₂ manifolds **overlap** sufficiently
([[HOA]], [[Manifold]] link-formation); `f_giant` — the fraction in the largest
connected component — is the order parameter that jumps at the threshold.

N=4 agents sit on the honor↔dignity axis (as in model ③; attractor at K=dignity).
Two agents are **coupled** (an edge) when their manifolds overlap — `|uᵢ−uⱼ| ≤ overlap`,
so `overlap` is the connectivity parameter (the graph's ε). An agent advances
toward the attractor only if it is **connected to the growing cluster** (a peer
ahead within `overlap`) or is the seed; otherwise it climbs only via rare exogenous
`noise`. The giant cluster grows down through overlapping manifolds — and can only
span the population if connectivity bridges the gaps.

```powershell
# THE PERCOLATION CLIFF (noise=0): P[F crystallized] vs connectivity. Init (0,1,3,6), gaps 1,2,3.
& $PRISM $Mp $Pp -property 3 -const overlap=1,noise=0.0,IA=0,IB=1,IC=3,ID=6   # -> 0.0
& $PRISM $Mp $Pp -property 3 -const overlap=2,noise=0.0,IA=0,IB=1,IC=3,ID=6   # -> 0.0
& $PRISM $Mp $Pp -property 3 -const overlap=3,noise=0.0,IA=0,IB=1,IC=3,ID=6   # -> 0.71  (cliff at the largest gap)

# WITHIN-HORIZON S-CURVE (noise=0.05, T=30) and TIMESCALE.
& $PRISM $Mp $Pp -property 4 -const overlap=1:1:4,noise=0.05,IA=0,IB=1,IC=3,ID=6,T=30  # -> 0.005, 0.28, 0.75, 0.94
& $PRISM $Mp $Pp -property 2 -const overlap=1:1:4,noise=0.05,IA=0,IB=1,IC=3,ID=6        # -> 148, 57, 36, 21 (steps)
```
(`$Mp`/`$Pp` = absolute paths to `MabmPercolation.sm` / `MabmPercolation.csl`.)

### What this pins down — the population-emergent percolation

- **A giant component is an emergent population object.** A single agent has no
  `f_giant`; with N coupled agents, a giant crystallized cluster forms at the
  dignity attractor — the population-scale face of model ③'s convergence and of
  Segment 1's `Φ` crystallization.
- **The crystallization cliff — discontinuous, "not a slope".** With no exogenous
  bridging (`noise=0`) crystallization is **exactly 0** below the connectivity
  threshold — the giant component provably cannot span the largest manifold gap —
  then jumps discontinuously above it (0 → 0.71 at the init (0,1,3,6) gap of 3;
  0 → 0.40 at the init (0,2,4,6) gap of 2). The **threshold location tracks the
  largest gap**: percolation is limited by the weakest link, exactly as
  Erdős–Rényi predicts. Under bridging noise the cliff appears as a steep S-curve
  in the finite-horizon probability (0.005 → 0.28 → 0.75 → 0.94 at T=30) and as a
  collapse of the crystallization timescale (148 → 21 steps).
- **Above threshold, crystallization is likely but not certain (`noise=0`).** The
  sub-unity values reflect **dynamic stranding** — fast leaders can climb past
  laggards before they connect, opening a gap and stranding them below the
  attractor. A faithful population subtlety, not a defect: static connectivity
  above threshold does not *guarantee* a spanning cluster once the nodes are
  moving.

### Scope boundary (MABM percolation)

- **A tractable stand-in, structural not calibrated.** The 1-D manifold-overlap
  graph is a PRISM-expressible abstraction of Segment 1's Erdős–Rényi
  interaction-network percolation; the claim is the **discontinuous cliff and its
  gap-limited threshold**, not the calibrated ε* ≈ 0.30–0.35 value. `Φ`'s other
  two factors (`ρ_cycle`, `w̄`) are folded into the single overlap/advance rule and
  not separately exercised. No locked pre-registered parameter (`φ_threshold`, ε*)
  is redefined.
- **N=4 is PRISM-scale; larger N is the Storm-scale target.** The full MABM —
  many agents on the `S¹⁵` manifold, the stratified Hasse crystallization
  sequence, the p=0.999 multigenerational aggregate over a real population network
  — exceeds PRISM's explicit state space and is the intended Storm continuation.


## EthosCapture.sm — ETHOS epistemic capture + critical slowing down (peer model)

The **first peer model** — a SCORE peer's dynamics model-checked, not just
core/POLARIS (closing the ETHOS cell of the coverage ledger in
[[ModelCheckedDynamics]] § "Coverage and boundaries"). ETHOS is the
epistemic-commons peer; its capture dynamics (`src/ethos/dynamics/capture.py`,
E5) are the epistemic instance of **model ①'s** early-warning structure: as
**capture pressure** rises toward a bifurcation, an epistemic community's
information health loses resilience and collapses into the
`core:PathologicalAttractor` basin, with **critical slowing down** (rising
autocorrelation) before it — the SEWI signature, since `ethos:InfosphereSpectralEWS`
is the *second filler of the same `core:SpectralEarlyWarningIndicator`* as
`polarisSEWI`. Capture attenuates self-correction (rate ∝ `1 − cap` = the ETHOS
`capturedHealth` factor κ) and strengthens erosion.

```powershell
# All four properties are MONOTONE in capture pressure `cap` (sweep 0.2..0.8):
& $PRISM $Me $Pe -property 1 -const cap=0.2:0.2:0.8,INIT_H=4,ABSORB=1,T=10  # P[collapse<=10] -> 0.17, 0.41, 0.68, 0.89
& $PRISM $Me $Pe -property 2 -const cap=0.2:0.2:0.8,INIT_H=4,ABSORB=1        # time-to-collapse -> 44.5, 17.2, 8.8, 5.4
& $PRISM $Me $Pe -property 3 -const cap=0.2:0.2:0.8,INIT_H=2,ABSORB=1,T=10  # recovery (CSD)   -> 0.71, 0.58, 0.42, 0.23
& $PRISM $Me $Pe -property 4 -const cap=0.2:0.2:0.8,INIT_H=4,ABSORB=0        # steady healthy   -> 0.85, 0.59, 0.22, 0.02
```
(`$Me`/`$Pe` = absolute paths to `EthosCapture.sm` / `EthosCapture.csl`.)

### What this pins down — the ETHOS capture claims, and the depth tie

- **Capture accelerates collapse; the early-warning lead time shrinks.** Collapse
  probability within a horizon rises **0.17 → 0.89** and the expected
  time-to-collapse falls **44.5 → 5.4** as capture pressure rises — model ①'s
  timescale collapse, epistemically typed.
- **Critical slowing down — `ethosSpectralEWS_monotone`, model-checked.** Recovery
  probability from a perturbed state falls **monotonically 0.71 → 0.23**: the
  commons self-corrects ever more slowly as capture rises (the rising-autocorrelation
  signal the spectral EWS reads). This is the model-checked face of the Lean
  monotonicity law; its executable-generator companion is
  `test_ethos/test_capture.py::test_ews_monotone_in_capture_pressure`, which guards
  the *same* monotone dose-response on `src/ethos/dynamics/capture.py` — the **depth
  tie** that connects a model-checked property to the implementation's test suite.
- **VC1 — capture cannot increase health.** Steady-state healthy-occupancy is
  monotone non-increasing in capture, collapsing **0.85 → 0.02**: the probabilistic
  face of `capture_cannot_increase_information_health` (`capturedHealth κ H = κ·H ≤ H`).

### Scope boundary (ETHOS capture)

- **Illustrative, structural, bounded** — no locked ETHOS number (ET-G quality
  weights, the M4 discriminant) redefined; the claim is the *monotone dose-response
  shape* (collapse ↑, lead time ↓, recovery ↓, health ↓ in capture), not the Q4-BIND
  calibration. Single-community scalar-pressure ramp, not the full Ω-actor
  amplification simulation.
- **A reuse of model ①, ETHOS-typed** — it is the first peer model, and the pattern
  (attenuated recovery + strengthened erosion → critical slowing down + collapse)
  transfers directly to the other peers' unchecked dynamics (AGORA manifold-update,
  ATLAS cascade) noted in the coverage ledger.
