# formal/z — the Z track: refinement-calculus statements (CZT-typechecked)

**Live as of 2026-07-24** — the revisit conditions of the original pilot README fired
the same day they were written: the refinement thread adopted Z as the statement
surface for retrieve relations, and the CZT→Lean/OWL emitters are committed. Scope:

- **What this track is:** Woodcock–Davies data-refinement statements — retrieve
  relations and their initialisation/applicability/correctness obligations as
  CZT-typechecked Z, the calculus face of the behavioral edge register
  (`obsidian/SCORE/methodology/RefinementCalculus.md`,
  `…/RefinementArchitecture.md`). Z *states*; TLC *checks bounded instances*
  (`formal/tla/*Refinement*.tla`); Lean *proves*.
- **What this track is not:** a vault-wide formality (piloted and declined
  2026-07-24 — see `hoamaint.zed`, kept as that pilot's evidence artifact), and not
  a fourth invariant-checking layer beside TLA/SPIN/PRISM.

## Files

    hoamaint.zed   -- pilot evidence (HOA maintenance in Z; the declined vault-formality probe)
    hoarefine.zed  -- FIRST LIVE ARTIFACT: HOAExt => HOA retrieve relation + the three
                      W&D obligations as typed conjectures. Statuses: init (holds only
                      for formal-basin inits), correctness (bounded TLC evidence),
                      applicability (NEW -- not covered by trace inclusion; OPEN).

## Type-checking

The CZT toolchain lives in the sibling repo (`protocol-formal-template/z`; one-off
`setup-czt.ps1` — JDK 11 + Maven + CZT source build):

```powershell
& ~\Dev\protocol-formal-template\z\run-czt.ps1 -File .\hoarefine.zed -Format SUMMARY
& ~\Dev\protocol-formal-template\z\run-czt.ps1 -File .\hoarefine.zed -Format UNICODE   # vault rendering
```

Re-typecheck on every `.zed` edit. CI gating follows with the emitters (CZT is a
source build, machine-local today — a gate must skip-if-absent like
`modelcheck_run.py`'s layers).

## The emitters (committed, not yet built)

`AstToLean4Visitor` and `AstToOwlVisitor` — print visitors over CZT's type-checked
AST (`net.sourceforge.czt.print.z.AstToPrintTreeVisitor` is the extension pattern),
to be built in `protocol-formal-template/z`:

- **Lean emitter:** obligation skeletons (state schemas → structures, conjectures →
  theorem statements) for hand proof — the conformance-diff design against the
  Mathlib-idiomatic hand spine is an open design question (RefinementCalculus.md
  open question 3).
- **OWL emitter:** the DL-expressible slice — spec metadata and refinement edges
  (which spec refines which, via which retrieve relation), not predicates.

Until they land, the note ↔ `.zed` ↔ Lean/OWL seam is discipline-guarded
(typecheck-on-change + update-at-source), accepted deliberately.
