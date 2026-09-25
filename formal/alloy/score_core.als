module score_core

/* ════════════════════════════════════════════════════════════════════════
   SCORE core — exploratory Alloy companion to formal/Formal/Score/Core.lean

   What this file is for:
     Lean asks "can I PROVE this?"  Alloy asks "what small worlds does this ALLOW?"
     Every abstract `axiom Foo : Type` in Core.lean becomes a finite set of atoms
     here, and the Alloy Analyzer searches every world up to a small size.

   How it is organised:
     PART A  mirrors Core.lean (§1 domains, §2 strata, §4 morphisms, §5/§7
             coupling + percept filter, §14 doctrinal network / regions).
             Its `check`s restate Lean theorems. They should all come back
             "no counterexample found" — that is evidence the translation is faithful.
     PART B  exploration. `run`s ask "is there a world where …?" and `check`s ask
             "is it really true that …?". Some of these are EXPECTED to surprise.

   Every command carries `expect 0` (no instance / no counterexample) or `expect 1`
   (instance / counterexample found), so the result is machine-checked:
       ./run-alloy.ps1 -Model score_core.als     (run-alloy.ps1 from protocol-formal-template/alloy)

   Convention: `fact` = a commitment of the theory (always on).
               `pred` = a hypothesis you can switch on inside a command.

   Status: exploratory (tier between Obsidian and OWL). Not part of the Lean/OWL
   spine; not gated by score_check.py. Bounded search: "no counterexample" means
   "none up to the stated scope", not a proof.
   ════════════════════════════════════════════════════════════════════════ */

open util/ordering[Stratum] as St
open util/ordering[Level]   as Lv


/* ─────────────────────────────  PART A  ───────────────────────────── */

-- §1  THE THREE DOMAINS — top-level sigs are disjoint by construction,
--     so B₁ / B₂ / B₃ irreducibility (domainsDistinct) comes for free.

sig World {}                          -- B₁  objective states
sig CogState {}                       -- B₂  cognitive states (manifold points)

sig Inscription {                     -- B₃  inter-subjective content
  author    : one Agent,              -- inscribe : Agent → CogState → Inscription
  source    : one CogState,
  substrate : set Inscription,        -- §14 composesFrom:  x in y.substrate  ⇔  composesFrom x y
  grade     : one Level,              -- §14 B3Level (0 signal … 5 generative framework)
  restsOn   : set Context             -- PART B, E5 only (speculative context tracking)
}

-- Referent typing of inscription (Core.lean §4, 2026-06-04).
-- Inscription is left non-abstract, as in Lean: an untyped `inscribe` also exists.
sig B1Ref extends Inscription { about : one World }   -- about world-states
sig B2Ref extends Inscription {}                      -- about the author's own B₂

sig Agent {
  state       : one CogState,                    -- current manifold position
  manifold    : some CogState,                   -- B₂ states this agent can occupy
  perceive    : World -> one CogState,           -- perception  B₁ → B₂  (total, as in Lean)
  act         : CogState -> World -> one World,  -- action      B₂ → B₁  (total, as in Lean)
  incorporate : Inscription -> lone CogState,    -- incorporation B₃ → B₂ (see note below)
  coupling    : one Coupling                     -- §5 coupling weight vector
}
-- NOTE on `incorporate`: Lean declares it total (every agent incorporates every
-- inscription into *some* state). Here it is `lone` — possibly undefined — so that
-- "recovery is possible but never guaranteed" can be explored. The pred
-- `LeanTotalIncorporation` restores the Lean reading when you want it.
pred LeanTotalIncorporation { all a: Agent, i: Inscription | one a.incorporate[i] }

sig Deep in Agent {}                  -- SufficientDepth (Lefebvre reflexive depth)

-- The depth gate: B₂-referential inscription needs sufficient depth.
-- (Lean enforces this at the type level; OWL as a GCI; here as a fact.)
fact DepthGate { all i: B2Ref | i.author in Deep }

-- POLARIS framing (not stated in Core.lean): agents are confined to their manifold.
-- Everything an agent perceives, incorporates, or inscribes from lies on it.
fact ManifoldConfinement {
  all a: Agent {
    a.state in a.manifold
    a.perceive[World]        in a.manifold
    a.incorporate[Inscription] in a.manifold
    (author.a).source        in a.manifold
  }
}

-- §2  EMERGENCE STRATA — six ordered strata; stability is downward-closed.
sig Stratum {}
sig Stable in Stratum {}
fact StratificationConstraint { all s: Stable | some St/prev[s] implies St/prev[s] in Stable }

assert StableImpliesAllLowerStable { all s: Stable | St/prevs[s] in Stable }
check StableImpliesAllLowerStable for 3 but exactly 6 Stratum, exactly 6 Level expect 0

-- §5/§7  COUPLING VECTOR AND PERCEPTUAL FILTER
-- Real-valued weights are abstracted away: a Coupling is just "a manifold position"
-- whose only job is to filter events into percepts.
sig Event {}
sig Percept {}
sig Coupling { filter : Event -> one Percept }         -- perceptualFilter

-- ε-similarity collapses to identity in a discrete model.
pred perceptuallySimilar[c1, c2: Coupling] { all e: Event | c1.filter[e] = c2.filter[e] }

assert PolarizationAsBifurcation {
  all c1, c2: Coupling |
    not perceptuallySimilar[c1, c2] implies some e: Event | c1.filter[e] != c2.filter[e]
}
check PolarizationAsBifurcation for 4 but exactly 6 Stratum, exactly 6 Level expect 0

-- §14  DOCTRINAL NETWORK AND REGIONS
sig Level {}                          -- B3Level, ordered; distinct from Stratum (precision guard)
fact GradeMono { all y: Inscription, x: y.substrate | Lv/lte[x.grade, y.grade] }

-- D.le x y  ⇔  x is a (reflexive-transitive) substrate of y
pred le[x, y: Inscription] { x in y.*substrate }

pred isRegion[R: set Inscription] {
  all x, y: Inscription | (le[x, y] and y in R) implies x in R
}
fun downClosure[gen: set Inscription]: set Inscription { gen.*substrate }

sig Community { region : set Inscription }
fact RegionsAreDownSets { all c: Community | isRegion[c.region] }

assert GradeMonoLe       { all x, y: Inscription | le[x, y] implies Lv/lte[x.grade, y.grade] }
assert RegionInter       { all R, S: set Inscription | (isRegion[R] and isRegion[S]) implies isRegion[R & S] }
assert SubsetDownClosure { all g: set Inscription | g in downClosure[g] }
assert DownClosureIsRegion { all g: set Inscription | isRegion[downClosure[g]] }

check GradeMonoLe         for 5 but exactly 6 Stratum, exactly 6 Level expect 0
check RegionInter         for 5 but exactly 6 Stratum, exactly 6 Level expect 0
check SubsetDownClosure   for 5 but exactly 6 Stratum, exactly 6 Level expect 0
check DownClosureIsRegion for 5 but exactly 6 Stratum, exactly 6 Level expect 0

-- A sample world with a bit of everything — open this one first in the visualizer.
run Show {
  some B1Ref and some B2Ref and some Community.region and some Stable
  some i: Inscription | some i.substrate
} for 3 but exactly 6 Stratum, exactly 6 Level expect 1


/* ─────────────────────────────  PART B  ───────────────────────────── */

-- E1  Is the doctrinal network really a DAG?
--     Core.lean §14 calls it "one graded DAG", but the only law is grade_mono,
--     which allows a cycle among inscriptions of EQUAL grade. Expect an instance.
run DoctrinalCycle { some x: Inscription | x in x.^substrate }
  for 3 but exactly 6 Stratum, exactly 6 Level expect 1

pred Acyclic { no x: Inscription | x in x.^substrate }

-- E2  Does a stored frontier determine its region uniquely?
--     §14 "store the frontier, derive the rest" (fibration decision #2).
pred antichain[g: set Inscription] { all disj x, y: g | not le[x, y] }

assert FrontierDeterminesRegion {
  all g1, g2: set Inscription |
    (antichain[g1] and antichain[g2] and downClosure[g1] = downClosure[g2]) implies g1 = g2
}
-- Expect a COUNTEREXAMPLE: two members of an equal-grade cycle each generate the region.
check FrontierDeterminesRegion for 3 but exactly 6 Stratum, exactly 6 Level expect 1

assert FrontierDeterminesRegionIfAcyclic {
  Acyclic implies
    all g1, g2: set Inscription |
      (antichain[g1] and antichain[g2] and downClosure[g1] = downClosure[g2]) implies g1 = g2
}
-- Expect no counterexample: with acyclicity added, the frontier is unique.
check FrontierDeterminesRegionIfAcyclic for 5 but exactly 6 Stratum, exactly 6 Level expect 0

-- E2b  The cycle-as-unit repair (B3RegionGeometry § R(C) item 2; aperture a1).
--      Instead of adding Acyclic as a law, keep the preorder and take the frontier
--      over the quotient by mutual substrate: a cycle is one unit. Represented without
--      a quotient sig, as a SATURATED set (it contains every member of each class it
--      touches) that is an antichain up to equivalence (nothing in it lies strictly
--      below anything else in it).
fun equiv: Inscription -> Inscription { { x, y: Inscription | le[x, y] and le[y, x] } }
pred saturated[g: set Inscription]      { g.equiv in g }
pred classAntichain[g: set Inscription] { all x, y: g | le[x, y] implies le[y, x] }
-- The members of R that nothing else in R lies strictly above.
fun classFrontier[R: set Inscription]: set Inscription {
  { x: R | all y: R | le[x, y] implies le[y, x] }
}

-- Uniqueness: two class-frontiers with the same region are the same set. Expect none.
assert ClassFrontierDeterminesRegion {
  all g1, g2: set Inscription |
    (saturated[g1] and saturated[g2] and classAntichain[g1] and classAntichain[g2]
       and downClosure[g1] = downClosure[g2]) implies g1 = g2
}
check ClassFrontierDeterminesRegion for 5 but exactly 6 Stratum, exactly 6 Level expect 0

-- Existence: every region is generated by its class-frontier, and that frontier is a
-- saturated class-antichain. Without this, uniqueness could hold vacuously. Expect none.
assert RegionGeneratedByClassFrontier {
  all R: set Inscription | isRegion[R] implies {
    downClosure[classFrontier[R]] = R
    saturated[classFrontier[R]]
    classAntichain[classFrontier[R]]
  }
}
check RegionGeneratedByClassFrontier for 5 but exactly 6 Stratum, exactly 6 Level expect 0

-- Positive control: the two checks above range over worlds where the frontier really
-- contains a cycle. If no such world existed they would pass for free. Expect an instance.
run CyclicClassFrontier {
  some R: set Inscription | isRegion[R] and
    some disj x, y: classFrontier[R] | x in y.^substrate and y in x.^substrate
} for 3 but exactly 6 Stratum, exactly 6 Level expect 1

-- Mutant control: drop saturation and uniqueness must fail again (the E2
-- counterexample: one member of a cycle vs another). Shows the clause does the work.
assert ClassAntichainAloneDeterminesRegion {
  all g1, g2: set Inscription |
    (classAntichain[g1] and classAntichain[g2]
       and downClosure[g1] = downClosure[g2]) implies g1 = g2
}
check ClassAntichainAloneDeterminesRegion for 3 but exactly 6 Stratum, exactly 6 Level expect 1

-- E3  Flattening. The depth gate controls who can PRODUCE B₂-referential content,
--     not who can INCORPORATE it. Can a shallow agent take in B₂-referential content
--     and re-inscribe it as B₁-referential (the L2 → L1/L0 flattening)?
run Flattening {
  some a: Agent - Deep, i: B2Ref, j: B1Ref |
    j.author = a and j.source = a.incorporate[i]
} for 3 but exactly 6 Stratum, exactly 6 Level expect 1

-- E4  Bridging. B₂ has no direct B₂→B₂ morphism. Can one inscription be taken up by
--     two agents whose manifolds share no state at all (syncretic contact via B₃)?
run BridgeAcrossDisjointManifolds {
  some disj a1, a2: Agent, i: Inscription {
    no a1.manifold & a2.manifold
    some a1.incorporate[i]
    some a2.incorporate[i]
    i.author not in a1 + a2
  }
} for 4 but exactly 6 Stratum, exactly 6 Level expect 1

-- E5  Recovery is never guaranteed. Is there a world where an inscription has
--     a mark but NO agent other than its author can incorporate it?
run OrphanedInscription {
  some i: Inscription | no (Agent - i.author).incorporate[i]
  #Agent > 1
} for 3 but exactly 6 Stratum, exactly 6 Level expect 1

-- E6  Coupling vs. perception. Core.lean has two perception stories that are not
--     linked: perception : World → Agent → CogState and
--     perceptualFilter : Event → Coupling → Percept. So two agents with the SAME
--     coupling vector may perceive the same world differently. Intended?
run SameCouplingDifferentPerception {
  some disj a1, a2: Agent, w: World |
    a1.coupling = a2.coupling and a1.perceive[w] != a2.perceive[w]
} for 3 but exactly 6 Stratum, exactly 6 Level expect 1

-- E7  (SPECULATIVE — the 2026-09 B₃ context-tracking thread, not in Core.lean)
--     Contexts are themselves inscriptions (Peano axioms, a currency regime, a legal
--     code). Other inscriptions rest on adopted contexts. Open: how does `restsOn`
--     relate to `substrate`? Nothing below decides that.
sig Context in Inscription {}

-- E7a  Can a context end up resting on itself (reflexive / Gödel-shaped grounding)?
run SelfGroundingContext { some c: Context | c in c.^restsOn }
  for 3 but exactly 6 Stratum, exactly 6 Level expect 1

-- E7b  A decision resting on two contexts that share no doctrinal ground
--      (overlap empty → maximal opacity in the anchor's 1 − overlap sense).
run DecisionAtContextIntersection {
  some i: Inscription | some disj c1, c2: i.restsOn |
    no downClosure[c1] & downClosure[c2]
} for 4 but exactly 6 Stratum, exactly 6 Level expect 1
