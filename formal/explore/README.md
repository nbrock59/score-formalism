# formal/explore — the exploration sandbox

Quarantined formal work for SCORE explorations (CLAUDE.md § Explorations; protocol rule 4
in `obsidian/explorations/Explorations.md`). No core gate reads this directory, the spine
must not import it, and its Lean library is not a default lake target
(`scripts/exploration_check.py` enforces all three). Its own gate is `make explore`
(`scripts/explore_formal.py`), outside `make check`.

| Path | What |
|---|---|
| `<name>/owl/*.owl` | probe ontologies importing `score-core.owl`; each declares `expect: consistent` or `expect: inconsistent` in an `rdfs:comment` |
| `<name>/owl/catalog-v001.xml` | resolves the core import offline |
| `<name>/lean/` | the lean_lib `Explore<Name>`, declared in `formal/lakefile.toml`, not a default target; may import `Formal.Score.*` |

## Method: independence probing

Kept here when the Penrose thread that developed it (P11) closed on 2026-10-17 with no new
content. The method worked; the commitments it was run on turned out to be carried. It is
recorded so the next use starts from the lessons, not from scratch.

**The question.** For a commitment the vault states, is it *forced* by the formal layers,
*asserted* by an axiom, or does it rest on prose alone? The pattern is Saccheri and
Beltrami's: negate the claim and ask whether the result is consistent. A consistent
negation marks a place where the theory is chosen, not forced.

**Two passes.**

- **Pass A, stated axioms.** Remove an OWL axiom, assert its negation with a probe member,
  reason. Inconsistent means the axiom is entailed by the rest (redundant or doubly
  supported); consistent means independent, the expected case. Small in core (5
  `AllDisjointClasses` groups and a few `disjointWith` pairs). Not run.
- **Pass B, prose commitments.** Assert the negation of a commitment the vault states in
  prose, against core as it is. Run once (2026-10-17) on four commitments.

**Five statuses per layer:** forced (by a definition or type), asserted (an axiom, or OWL
entailment), independent (expressible; the negation is consistent), inexpressible (no
vocabulary to state it), partial (a weaker form is carried).

**Protocol.**

1. **Register before running.** Commit and push the list (five or fewer), the probes and the
   predicted statuses, and name in advance which result would count as new content. The push
   puts the order in the history.
2. **Pair every probe with a control that must flip.** A consistent result is vacuous unless a
   one-axiom variant becomes inconsistent.
3. **OWL is open-world.** An ontology with no members is consistent almost regardless, so
   every probe asserts a member for the negation to act on.
4. **Lean is closed-world.** Inductive types close by construction, so the Lean question is
   whether a commitment is forced by a type, stated as an axiom, or absent. Lean cannot show
   a negated axiom consistent without a model.
5. **Read every section that could carry the commitment, not the first that seems to.**
   The 2026-10-17 run's one candidate result came from reading `Core.lean` § 3 (`World`,
   `perception`) and missing § 8 (`Event`, `perceptualFilter`, `polarizationAsBifurcation`),
   which carried the commitment as a theorem. The error surfaced only at intake, when a Rule 2
   pre-commitment forced a deliberate re-read. Before reporting "prose-only", grep the spine
   for every type the commitment could live on.

**Results of the one run (2026-10-17):** closure of the domains at three (forced in Lean,
independent in OWL); B₃ carried by a B₁ mark (asserted in both); HOA from coupling, not
declaration (forced in Lean, inexpressible in OWL); one B₁ manifold (carried in Lean at the
event level). Probe files: `penrose/owl/p1-*.owl`, `penrose/owl/p11-*.owl`.
