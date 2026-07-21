/* RevisionLoop.pml -- closed-loop truth-tracking as interacting processes,
 * model-checked with SPIN.
 *
 * SCORE traceability:
 *   - Lean  : formal/Formal/Score/RevisionLoop.lean -- the descriptive /
 *             impossibility spine (predictionAudit, hasResolvedClaimAccess,
 *             revisedError, strict_revision_requires_resolved_claim_access,
 *             no_resolved_claim_access_no_revision). Single-step and STATIC;
 *             the loop running over time, and the vicarious feedback BETWEEN
 *             communities, are unmodelled -- the liveness + concurrency gap.
 *   - vault : obsidian/SCORE/emergence/mechanism/RevisionLoop.md
 *             (§ "The candidate -- the loop, defined"; § "The two commitments";
 *              § "The failure map -- five broken arcs")
 *             obsidian/SCORE/methodology/ModelCheckedDynamics.md
 *
 * The loop: outcome-exposed B3 -> realized B1 -> prediction audit (error) ->
 * Transformation at gain -> independent correcting node. A community can only
 * run it with resolved-claim ACCESS (own outcome-exposure OR vicarious access
 * to another community's resolved claims -- amendment 1), and the corrector
 * must be INDEPENDENT of the content it tests (else mismatch floors above zero
 * -- captured_correction_needs_independent_node).
 *
 * Four communities exhibit the failure map. `err` is a community's error
 * magnitude; revision reduces it toward the corrector's floor:
 *   A -- own-exposed, independent corrector -> loop closes (err -> 0)
 *   B -- vicarious (maps to A's resolved claims), independent -> closes, but
 *        only once A has resolved: the CONCURRENCY payoff
 *   C -- neither own nor vicarious access -> audit never fires, err never falls
 *   D -- own-exposed but CAPTURED corrector -> err floors above zero
 *
 * Aligned with the Lean/SemanticSeepage scope: this models the descriptive
 * IMPOSSIBILITY spine only. The normative gain-band (over-revision dissolves
 * closure; under-revision fossilizes) stays out, exactly as it stays out of Lean.
 */

#define MAXERR 2
#define FLOORD 1        /* captured-corrector floor for D (mismatch > 0) */

byte eA = MAXERR;
byte eB = MAXERR;
byte eC = MAXERR;
byte eD = MAXERR;

/* The loops run FOREVER (the closed loop keeps predicting/auditing/revising);
 * once an error reaches its floor the community keeps cycling at that floor.
 * Continuous behaviour is what makes the <>[] liveness claims meaningful.
 *
 * A: own outcome-exposure + independent corrector. Audit fires every cycle;
 * Transformation reduces the error to zero -- the loop closes. */
active proctype CommunityA()
{
    do
    :: eA > 0  -> eA--
    :: eA == 0 -> skip     /* resolved: keep cycling at zero error */
    od
}

/* B: no own outcome-exposure. Vicarious feedback (amendment 1): it maps to
   ANOTHER community's RESOLVED claims -- here A's -- which only exist once A has
   resolved (eA == 0). Independent corrector, so it too reaches zero. B's
   liveness DEPENDS on A: the interacting-processes core. */
active proctype CommunityB()
{
    do
    :: (eA == 0) && (eB > 0) -> eB--
    :: eB == 0               -> skip
    od
}

/* C: neither own outcome-exposed B3 nor a vicarious source. The access guard is
   never satisfied, so the audit never fires and the error never falls -- the
   loop runs but "revision without audit is drift or capture." */
active proctype CommunityC()
{
    do
    :: eC > 0 -> skip      /* audit never fires: error persists, loop spins */
    od
}

/* D: own outcome-exposure, but the corrector is the node whose content is being
   tested (CAPTURED). Revision reduces the error only to a floor > 0 -- it can
   never reach zero (captured_correction_needs_independent_node). */
active proctype CommunityD()
{
    do
    :: eD > FLOORD  -> eD--
    :: eD <= FLOORD -> skip
    od
}

/* Liveness: the own-exposed loop closes (converges). */
ltl convergeA { <> [] (eA == 0) }
/* Liveness via CONCURRENCY: the vicarious loop closes -- but only because A resolved. */
ltl convergeB { <> [] (eB == 0) }
/* Impossibility (access): no resolved-claim access -> the error never falls. */
ltl stuckC    { []    (eC == MAXERR) }
/* Impossibility (independence): captured correction floors mismatch above zero. */
ltl flooredD  { []    (eD > 0) }
