# formal/alloy — exploratory tier

Alloy 6 companion to `Formal/Score/Core.lean`. It sits between Obsidian and OWL in the stack:
Lean asks *"can I prove this?"*, while Alloy asks *"what small worlds does this allow?"*
It searches every world up to a small size and either shows you one or reports that none exists.

**Status:** exploratory. It isn't part of the Lean/OWL spine and isn't gated by `score_check.py`.
A bounded result ("none up to scope 5") is evidence, not proof.

## Getting started (about 10 minutes)

1. **Install.** Download `org.alloytools.alloy.dist.jar` (6.2 or later) from alloytools.org.
   It needs Java 17+. Double-click the jar, or run `java -jar org.alloytools.alloy.dist.jar`.
2. **Open** `score_core.als`. It's plain text, so you can also read it in VS Code or Obsidian.
3. **Run the sample world.** In the *Execute* menu, choose `Run Show`. When it reports an
   instance, click **Instance** to open the visualizer. You'll see agents, inscriptions,
   world states and communities as a graph.
4. **Get around the visualizer.**
   - *Next* shows another world that satisfies the same constraints. Clicking through
     several is the main way to explore.
   - *Theme* lets you hide fields or colour sigs. Hiding `act` and `perceive` makes the
     picture much clearer.
   - *Table* and *Tree* are alternative views of the same world.
   - *Evaluator* lets you type expressions against the current world, e.g.
     `Community.region`, `B2Ref.author`, `Inscription.*substrate`.
5. **Run everything** with *Execute → Execute All*. For a headless run, use
   `protocol-formal-template/alloy/run-alloy.ps1 -Model score_core.als`. Every command
   carries an `expect`, and the script prints PASS/FAIL against it (16/16 as of 2026-09-24).

### Reading results

| Command | Result | Meaning |
|---|---|---|
| `run P` | instance found | Your theory allows P. Look at the example. |
| `run P` | no instance | Your theory rules P out (up to the scope). |
| `check A` | no counterexample | A holds in every small world. |
| `check A` | counterexample | A fails somewhere. The visualizer shows where. |

## Results of the first run (2026-09-24, Alloy 6.2.0)

**Part A: mirrors of Lean theorems.** All six came back *no counterexample*
(`StableImpliesAllLowerStable`, `PolarizationAsBifurcation`, `GradeMonoLe`, `RegionInter`,
`SubsetDownClosure`, `DownClosureIsRegion`). That is evidence the translation is faithful.

**Part B: exploration.**

| # | Question | Result | Why it might matter |
|---|---|---|---|
| E1 | Can the doctrinal network have a cycle? | **Yes** | `grade_mono` allows cycles among equal-grade inscriptions, so `le` is a preorder rather than the "graded DAG" §14's comment describes. |
| E2 | Does a frontier determine its region uniquely? | **No:** counterexample | Two members of one equal-grade cycle each generate the same region. With `Acyclic` added, uniqueness holds (no counterexample, scope 5). This bears directly on fibration decision #2 ("store the frontier"). |
| E3 | Can a shallow agent flatten B₂-referential content into B₁-referential content? | Yes | The depth gate limits who can *produce* B₂-referential content, not who can *incorporate* it. This could be the L2→L1/L0 flattening, in formal form. |
| E4 | Can one inscription bridge two agents whose manifolds are disjoint? | Yes | B₃ is the only channel between disjoint manifolds: syncretic contact. |
| E5 | Can an inscription be orphaned, with nobody but its author able to incorporate it? | Yes (with `incorporate` partial) | Lean's `incorporate` is total. Decide whether "failure" means *undefined* or *unchanged state*. |
| E6 | Can two agents with the same coupling vector perceive the same world differently? | Yes | Core.lean's `perception` and `perceptualFilter` aren't linked. Is that intended? |
| E7 | Speculative B₃ context tracking: self-grounding contexts, and decisions resting on contexts with no shared ground | Both allowed | Nothing yet relates `restsOn` to `substrate`. That relationship is the open design question. |

E1/E2 is the one to look at first. You can either add acyclicity to `DoctrinalNetwork`, or
keep the preorder (mutual citation, co-developing doctrine) and store frontiers as
equivalence classes.

## Suggested next steps

- Try your own hypothesis. Write it as a `pred`, then `run` it to see an example world, or
  `check` it as an `assert` to hunt for counterexamples.
- Tighten or loosen facts one at a time and see which Part B results flip. The facts
  that flip results are the load-bearing ones.
- Alloy 6 supports time (`var` fields, `always`, `eventually`). A later model could run
  inscribe → incorporate → act as a trace, alongside `tla/`.
