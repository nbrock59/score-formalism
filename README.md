# score-formalism

Formal artifacts of the SCORE research program — Socio-Technical Constructionist Ontology
of Relational Emergence — developed by Neil A. Brock.

This repository is a release-tracked public mirror of the SCORE formal spine: the OWL 2 DL
ontologies, the Lean 4 modules, and the reasoner-conformance and validation scripts that
gate them. Development happens in a separate private repository (`nbrock59/polaris`);
this mirror carries snapshots of the shipping artifacts at each tagged release, so papers
citing "SCORE core `X` at version `v0.Y.Z`" have a public, permanent, verifiable
reference.

The papers, code releases, and companion materials of the SCORE research program are
collected at the Zenodo community
[`score-triad-brock`](https://zenodo.org/communities/score-triad-brock). Each tagged release of this
mirror auto-deposits to Zenodo with a DOI via the GitHub-Zenodo integration.

## What lives here

- `formal/score-core.owl` — the core ontology (three domains, the actor kinds, the five
  morphisms, community and attractor primitives, the refinement machinery).
- `formal/score-*.owl` — the seven implementation layers, one per peer: POLARIS, ETHOS,
  AGORA, ATLAS, NEXUS, SCORE-BAC, and Inscription-Market.
- `formal/Formal/Score.lean` and `formal/Formal/Score/*.lean` — the Lean 4 modules
  carrying the dynamical claims and theorems that fall outside description-logic
  expressiveness.
- `formal/lakefile.toml`, `formal/lean-toolchain` — the Lean project configuration
  sufficient to `lake build` the modules.
- `scripts/score_reason.py` — the HermiT-via-owlready2 reasoner-conformance check
  (`core ⊕ impl` consistency for each peer layer).
- `scripts/score_slots.py` — the cross-peer filler inventory (SHARED / LOCAL /
  UNFILLED by core slot), useful for exploratory analysis of the family's construct
  coverage.
- `.github/workflows/spine-check.yml` — the CI job that runs the reasoner conformance
  check and the Lean build on every push.

## What does not live here

The wider SCORE working environment — the concept vault, paper drafts, session notes,
validation data, private demos, and infrastructure supporting theoretical development —
lives in the private `nbrock59/polaris` repository. This mirror is deliberately the
crystallized, checkable, citable subset. Issues and pull requests filed here will be
redirected to the private repository.

## Running the checks locally

The reasoner conformance check requires Python 3.10+ and `owlready2`:

    python -m venv .venv
    .venv/Scripts/activate    # Windows
    # or: source .venv/bin/activate  # Linux/macOS
    pip install owlready2
    python scripts/score_reason.py

Expected output (one line per implementation layer, ending with a summary):

    === core + score-<impl> (refinement conformance) ===
      loaded: score-core.owl, score-<impl>.owl
      RESULT: consistent; no unsatisfiable classes

    summary: core=OK | score-agora=OK | score-atlas=OK | score-bac=OK
             | score-ethos=OK | score-inscription-market=OK | score-nexus=OK
             | score-polaris=OK

`scripts/score_slots.py` uses the Python standard library only and takes no
arguments other than optional filters; run `python scripts/score_slots.py --help` for
usage.

The wider polaris repository additionally runs structural vault-consistency,
glossary-to-formalism traceability, and mechanizable-staleness gates that require
polaris's working tree (concept vault, outreach drafts, theoretical notes). Those checks
gate the private repo and cannot be reproduced against this formalism-only mirror.

The Lean 4 modules are buildable with the Lean version pinned in `formal/lean-toolchain`.
From `formal/`:

    lake build

## Related resources

- The SCORE triad of papers and companion materials —
  [Zenodo community `score-triad-brock`](https://zenodo.org/communities/score-triad-brock).
- The private working repository, for the concept vault and paper drafts —
  `nbrock59/polaris` (access on request; the artifacts and papers are the public face
  of the program).
- The author — Neil A. Brock, Turtle Pond Group and WPI Complex Systems Laboratory.

## License

The formal artifacts in this repository are dual-licensed:

- Code — the Python scripts under `scripts/`, the Lean modules under
  `formal/Formal/`, and the CI workflow files — are released under the **MIT License**
  (`LICENSE-CODE.txt`).
- Ontologies and documentation — the `score-*.owl` files, this README, and any
  Markdown documentation — are released under
  **Creative Commons Attribution 4.0 International (CC-BY-4.0)** (`LICENSE-DOCS.txt`).

See `LICENSE.md` for the routing detail.

## Citation

When citing the formalism itself, cite the tagged release DOI from the Zenodo community.
When citing a claim about the formalism, cite the paper (Paper A, B, or C) that develops
the claim, and reference the specific release of the formalism the paper is written
against via its DOI.
