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
- **A stable unformed equilibrium** (full bistability) and the **intervention
  MDP** (model ②, reaching Segment 7) are **not** in this file — see the scope
  note's model ②/③ and the hysteresis boundary above.
