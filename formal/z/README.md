# formal/z — the Z track: refinement-calculus statements (CZT-typechecked, since 2026-08-11)

> **The "CZT-typechecked" label was hollow until 2026-08-11, and is now real.** Building the
> `make z` gate required measuring what the pipeline actually rejects. It rejected syntax
> errors and nothing else: an undeclared type (`q : NOSUCHTYPE`) and a type mismatch
> (`x : \nat` constrained by `x = \{1\}`) each reported *"OK: parsed and type-checked"* and
> exited 0.
>
> **Cause.** `CztConvert.java` obtained the AST with `sm.get(Key<Spec>)`, which dispatches
> CZT's **parse** command — the typechecker was never invoked — and then printed an
> unconditional `"OK: parsed and type-checked."` string literal on the strength of a comment
> reading *"getting the Spec at all implies a pass."* A hardcoded success message for a step
> that did not run. **Fixed** in the sibling repo (`protocol-formal-template` @ `97eefcb`,
> branch `fix/czt-actually-typecheck`): it now calls `TypeCheckUtils.typecheck(spec, sm)`,
> prints each `ErrorAnn` with file/line/column, and exits 1 on a non-empty list. All three
> constructed cases now fail.
>
> **What that immediately exposed, and this is the part that matters:**
>
> | file | first verdict under a working typechecker | now |
> |---|---|---|
> | `hoamaint.zed` | passes | passes |
> | `morphisms.zed` | **4 errors** — `InitScore` used bare decorated inclusion `Score'` | fixed, passes |
> | `hoarefine.zed` | **37 errors** — `Undeclared name: AHOA'`, `CHOA'`, `asub'`, `aend'`, `csub'`, `cend'`, `cres'` | fixed, passes |
>
> **All three now type-check** (`make z`, exit 0). One root cause behind every error: **this
> CZT build does not bind decorated schema *references*.** `\exists AHOA' \spot …` reports
> `Undeclared name: AHOA'` and then every primed component under it. Decorated names
> introduced by `\Delta` bind correctly — which is why `AMove`, `CMove` and all five
> morphism operation schemas were always clean, and why only the initialisation schema and
> the two conjectures were affected.
>
> The repair is an equivalence, not a weakening: `\exists AHOA' \spot P` becomes
> `\exists asub', aend' : \nat | asub' \leq maxlvl \land aend' \leq 2 * maxlvl \spot P`,
> inlining exactly what the decorated reference would have contributed — the components and
> the state invariant. `hoarefine.zed` still reports `conjectures=3`; **no obligation was
> dropped, and no mathematical content changed.** The idiom is recorded in that file's
> header so it is not "simplified" back.
>
> **What this cost.** `hoarefine.zed` is this track's **"FIRST LIVE ARTIFACT"**, carrying
> the retrieve relation and the three Woodcock–Davies obligations. It carried 37 type errors
> from 2026-07-24 to 2026-08-11 and was reported clean by every run in that window. The
> `init` / `correctness` / `applicability` statuses below were stated against a
> specification that had never been type-checked. They are now stated against one that has —
> which validates the statuses' *form*, not their *content*: the TLC and Lean discharge
> targets are unaffected and still owed.
>
> **The gate went dormant again, on one machine (found 2026-09-25, issue #904).** A
> `protocol-formal-template` clone three commits behind `origin/main` still carried the
> pre-fix runner. Against it `make z` reported all three files `[ok]`, including this
> README's own `NOSUCHTYPE` control and a four-line spec equating an `A` with a `B`. The
> fix was never the problem; nothing *required* the runner to contain it. `scripts/z_run.py`
> now type-checks an ill-typed-by-construction probe first and exits 2 if the runner accepts
> it. Verified both ways: the stale runner is rejected before any file is judged; the current
> runner (`5325443`) passes all three files and fails seven constructed must-fail variants.
> Also in #904: `morphisms.zed`'s `carrier` is `ITEM \rel MARK` (it was a function, which
> denied multiple realizability), and a `ReInscribe` schema was added (9 schemas).

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
