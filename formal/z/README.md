# formal/z/ — Z/CZT pilot artifact (NOT a verification layer)

One file, kept as **evidence from a closed investigation** — this directory is
*not* a sixth formal track alongside `formal/{tla,spin,prism}`, has no CI gate,
and `scripts/modelcheck_check.py` deliberately does not know about it.

## What happened (2026-07-24)

Investigated whether adding CZT-checked Z notation to the SCORE vault would
improve how the OWL/Lean spine is fed. Pilot: `hoamaint.zed`, a Z rendering of
HOA within-basin maintenance mirroring `formal/Formal/Score/HOAMaintenance.lean`
(§HM1–HM8) and `formal/tla/HOA.tla` name for name. Findings:

- **Authoring friction is low.** Type-checked on the first CZT pass (7 schemas,
  1 conjecture); the four idioms from `protocol-formal-template/z/model.zed`
  carry over cleanly; the Unicode narrative renders vault-ready.
- **The feed role fails today.** CZT's `AstToLean4Visitor` / `AstToOwlVisitor`
  emitters are unbuilt (`[future]` in the template), so a Z block is a fourth
  hand-synchronized artifact — it *adds* seams (prose↔Z, Z↔Lean, Z↔OWL) rather
  than closing the prose↔formal one.
- **OWL fit is poor** (class taxonomy vs. state-and-operation schemas), and the
  state-and-operation niche is already occupied by the model-checking layer,
  which additionally *executes* models where CZT only typechecks.

**Decision: declined for the feed role.** Full record:
`obsidian/sources/Woodcock-Davies.md` § "Where it could bear on SCORE".
The still-open thread from that note — W&D **data refinement** (retrieve
relations, simulation obligations) as the behavioral face of peer-to-core
specialization — is independent of Z-the-notation and does not require this
directory to grow.

## Revisit conditions

Reopen only if (a) the CZT→Lean/OWL emitters get built and a conformance-diff
against the hand-authored spine is designed, or (b) the refinement thread
decides it wants Z as its statement surface after all.

## Type-checking the artifact

The CZT toolchain lives in the sibling repo (`protocol-formal-template/z`,
one-off `setup-czt.ps1` — JDK 11 + Maven + CZT source build):

```powershell
& ~\Dev\protocol-formal-template\z\run-czt.ps1 -File .\hoamaint.zed            # all four narratives
& ~\Dev\protocol-formal-template\z\run-czt.ps1 -File .\hoamaint.zed -Format SUMMARY
```
