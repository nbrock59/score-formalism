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
  hold the unformed state. That barrier is **not attempted here** — it is the
  natural refinement for a follow-up model, not a blocker for model ①.

## Scope boundary — what this does and does not add

- **Bounded, illustrative, structural.** Like TLC/SPIN, PRISM checks a concrete
  bounded instance (`L=4`), not an unbounded proof. The rates are illustrative
  (governance note above); the *shape* of the results — timescale collapse,
  slowing recovery, residue-extended lifetime — is the claim, not the specific
  numbers.
- **Does not touch the locked pre-registered parameters.** No SEWI threshold,
  β dosing, or ψ_s flag is redefined, computed, or calibrated here.
- **A stable unformed equilibrium** (full bistability) is **not** in this CTMC —
  it needs the nucleation barrier described in the (a) boundary above. The
  **intervention MDP** built on top of this state is model ②, `InterventionMDP.nm`
  below.

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
- **Additive + one subtractive operator only.** The full subtractive family and
  the B₃-mediated channel (the unworked cells of [[InterventionClasses]]'s 2×2)
  are not modelled. `create_edge`-before-`create_node` in infrastructure-severed
  sub-communities is representable but not separately exercised here.
- **A cost-free `wait` was deliberately omitted** — it is a zero-reward loop that
  makes `Rmin` ill-posed (a policy could stall forever at zero cost), and waiting
  only ever lets the environment erode the objective. Model ③ (agent-learning
  DTMC) remains the open third pilot.
