# formal — the SCORE formal spine

Machine-checkable layer of SCORE. Two formalisms, kept consistent with the Obsidian
concept vault (`../obsidian/SCORE/`) by `../scripts/score_check.py`.

## Contents

| File | What |
|---|---|
| `score-core.owl` | Domain-independent SCORE ontology (IRI `http://score-theory.org/core`). Classes, properties, disjointness; reasoner-verified consistent. |
| `score-polaris.owl` | POLARIS implementation layer (IRI `http://score-theory.org/polaris`). `owl:imports` core and specializes its slots (`SEWI`/`TPRI ⊑ MeasurementModel`, `GeographicCommunity ⊑ HumanCommunity`). |
| `catalog-v001.xml` | OASIS catalog mapping the core import IRI to the local file so Protégé/HermiT resolve `owl:imports` offline. |
| `Formal/SCORE_Lean4.lean` | Lean 4 formalization of the dynamics (domains, morphisms, stratification, HOA, intervention classes). |
| `Formal.lean`, `lakefile.toml`, `lean-toolchain` | Lean project scaffolding. |
| `tla/*.tla` (+ `.cfg`) | TLA+/TLC **model-checked dynamics** (a third formalism for the dynamical layer): the Dijkstra self-stabilizing ring, the full HOA maintenance family (§HM8–HM17), and the A-/Σ-actor life-cycles. See `tla/README.md` and `obsidian/SCORE/methodology/ModelCheckedDynamics.md`. |
| `spin/*.pml` | SPIN/Promela model-checked dynamics — the concurrency + liveness companion to `tla/`. `RevisionLoop.pml` runs the revision loop's descriptive/impossibility spine (`Score/RevisionLoop.lean`) as interacting processes with `<>[]` liveness. See `spin/README.md`. |
| `prism/*.{sm,csl,nm,pctl}` | PRISM **probabilistic** model-checked dynamics — the *quantitative* rung (probability, expected time, optimal policy) the TLC/SPIN pilots do not reach. `HOADissolution.sm` (CTMC lift of `tla/HOA.tla` §HM8, validating the SEWI critical-slowing-down premise) with its bistability refinement `HOANucleation.sm` (a nucleation barrier giving a stable unformed equilibrium — `HOA.tla` case 3 on a generative chain), `InterventionMDP.nm` (intervention-policy MDP on top of it, → Segment 7, deriving the [[InterventionClasses]] sequencing/sponsor/leverage claims from the optimal policy) with its subtractive-family extension `HOASubtractive.nm` (dissolution cost indexed by target persistence, not operator depth — the VC-1 finding) and its B₃-mediated-channel extension `MediatedChannel.sm` (sub-threshold steering is non-contestable and cohort-forming — the [[IncorporationAsymmetry]] self-masking structure, completing the intervention 2×2), and `AgentLearning.sm` (Path-A/B learning DTMC, → Segment 1, confirming the multigenerational attractor and κ-decay asymmetry against the Brock 2026 baseline) with its multi-agent step `MabmPercolation.sm` (Φ crystallization as a discontinuous percolation cliff — the population-emergent object toward the full MABM). All carry the pre-registration-lock governance caveat. See `prism/README.md`. |

The layering and the core-vs-implementation decision procedure are documented in
`../obsidian/SCORE/methodology/RefinementArchitecture.md`.

## Consistency checking (automated, structural)

`scripts/score_check.py` enforces the vault↔OWL↔Lean spine — dangling wikilinks, `lean:`/
`owl:` frontmatter refs that don't resolve, OWL classes with no vault home, and **structural**
OWL layering (each impl imports core; every referenced superclass resolves). It runs in CI
(`.github/workflows/spine-check.yml`, `--strict`). It does **not** do description-logic
reasoning — that is the HermiT step below.

```
.venv/Scripts/python.exe scripts/score_check.py            # report
.venv/Scripts/python.exe scripts/score_check.py --strict   # warnings fail (CI mode)
```

## Full DL conformance (HermiT)

This verifies the real refinement contract: that **core ⊕ polaris is logically consistent**
(no implementation axiom contradicts a core axiom) and that no class is unsatisfiable.

### Automated — `scripts/score_reason.py`

Runs HermiT headlessly via `owlready2` (which bundles the HermiT jar). It needs a JRE but
finds one automatically: `JAVA_EXE`, then `PATH`, then the JRE **bundled with Protégé**
(`C:\Program Files\Protege-*\jre`). It reasons over core alone and over core+polaris and
exits non-zero on any inconsistency or unsatisfiable class. Also runs in CI
(`.github/workflows/spine-check.yml`, `dl-conformance` job, via `setup-java`).

```
pip install owlready2
.venv/Scripts/python.exe scripts/score_reason.py
```

Last verified 2026-06-03: **core consistent; core+polaris consistent, no unsatisfiable
classes** (recorded in each file's `owl:Ontology` comment).

### Interactive — Protégé

Useful for inspecting *why* something is (un)satisfiable. Run it in Protégé:

1. Open **`score-polaris.owl`** in Protégé. The `catalog-v001.xml` resolves the
   `owl:imports` of `score-core.owl`, so both layers load together. Confirm the core
   classes appear in the class hierarchy (e.g. `MeasurementModel`, `HumanCommunity`).
2. **Reasoner → HermiT**, then **Reasoner → Start reasoner**.
3. Expected result: **ontology consistent**; **no class equivalent to `owl:Nothing`**
   (nothing inferred unsatisfiable). The `SEWI`/`TPRI`/`GeographicCommunity` specializations
   should classify under their core superclasses with no contradiction.
4. Also reason over **`score-core.owl`** alone (open it directly) to confirm core itself is
   consistent independent of any implementation.

### Recording the result

A passing run is recorded in each file's `owl:Ontology` `rdfs:comment` (dated). A failing
run is a refinement-validity finding: the implementation has stopped being a valid subset of
core (see RefinementArchitecture, Q1–Q4). The structural `owl` check in `score_check.py` is
the fast guard on every commit; the `dl-conformance` job is the full reasoner check.
