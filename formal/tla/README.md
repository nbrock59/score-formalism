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
