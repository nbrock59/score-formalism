# formal/spin — model-checked SCORE dynamics (SPIN)

SPIN/Promela models, the concurrency-and-liveness companion to the TLA+ models
in `../tla`. TLC (in `../tla`) is the right tool for a single state machine with
invariants; SPIN earns its place where the property is **liveness** over a loop
running in time, or the model is genuinely **concurrent** (interacting
processes). Methodology note: `obsidian/SCORE/methodology/ModelCheckedDynamics.md`.

## RevisionLoop.pml — closed-loop truth-tracking

The revision loop of `Formal/Score/RevisionLoop.lean` and
`obsidian/SCORE/emergence/mechanism/RevisionLoop.md`. The Lean encodes the
**descriptive / impossibility spine** — single-step and static:
`strict_revision_requires_resolved_claim_access` (revision requires a resolved
claim to audit against; "revision without audit is drift or capture") and the
independent-corrector requirement (`captured_correction_needs_independent_node`).
What the Lean cannot express — the loop *running over time* (a liveness property)
and the *vicarious feedback between communities* (concurrency) — is exactly what
SPIN checks.

Four communities exhibit the failure map (`err` = error magnitude; revision
reduces it toward the corrector's floor; the loops run forever):

| Community | Configuration | Outcome |
|---|---|---|
| **A** | own outcome-exposure, independent corrector | loop closes (`err → 0`) |
| **B** | vicarious (maps to A's resolved claims), independent | closes — **but only once A has resolved** |
| **C** | neither own nor vicarious access | audit never fires; error never falls |
| **D** | own-exposed but **captured** corrector | error floors above zero |

Properties (`<>[]` = eventually-always; `[]` = always):

```promela
ltl convergeA { <> [] (eA == 0)     }   // own-exposed loop closes (liveness)
ltl convergeB { <> [] (eB == 0)     }   // vicarious loop closes -- via A (concurrency)
ltl stuckC    { []    (eC == MAXERR) }  // no access -> error never falls (impossibility)
ltl flooredD  { []    (eD > 0)      }   // captured correction floors above zero
```

## Running

Needs **SPIN** (`spin.exe`) and a **C compiler** (`gcc`) — build SPIN with
`../../protocol-formal-template`-style `build-spin.ps1`, or see
`obsidian/…/ModelCheckedDynamics.md`. Liveness needs acceptance-cycle detection
(`-a`) and weak fairness (`-f`); the `[]` safety claims need neither.

```powershell
spin -a RevisionLoop.pml
gcc -O2 -o pan.exe pan.c
./pan.exe -a -f -N convergeA    # -> errors: 0   (own-exposed loop closes)
./pan.exe -a -f -N convergeB    # -> errors: 0   (vicarious loop closes)
./pan.exe -N stuckC             # -> errors: 0   (no access: error never falls)
./pan.exe -N flooredD           # -> errors: 0   (captured: floors above zero)
```

## What this pins down (and the non-vacuity checks)

The two structural impossibilities the Lean spine states, now as **liveness**
properties of the loop *running*: with resolved-claim access (own **or**
vicarious) and an independent corrector the loop closes; without access it
cannot (`stuckC`), and with a captured corrector it floors above zero
(`flooredD`). And the **concurrency** the Lean cannot state: `convergeB` holds
only because a *separate* community A resolves first and B maps to its resolved
claims (amendment 1's vicarious feedback).

Two adversarial checks confirm the liveness is not vacuous:

- Asserting `convergeC` (the no-access community converges) is **violated** —
  SPIN returns an acceptance cycle. The impossibility is real.
- Breaking A (so it never resolves) makes `convergeB` **violated** — B's
  convergence genuinely *depends on* A. The vicarious-feedback concurrency is real.

Aligned with the Lean/`SemanticSeepage` scope, this models the descriptive
impossibility spine only. The normative **gain band** (over-revision dissolves
autocatalytic closure; under-revision fossilizes — RevisionLoop.md § "The two
commitments") stays out here, exactly as it stays out of Lean, pending an
observable.
