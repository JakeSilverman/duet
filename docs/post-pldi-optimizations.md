# Unused optimizations for post-PLDI investigation

This branch preserves interesting experiments that are **not used in the selected
PLDI configuration**. Use `ama-pldi-2027` for the selected correctness-fix-only
implementation. Do not merge these experiments back merely because individual
examples become faster. The required quantifier polarity/integrality correction
must remain in every comparison.

## What is preserved

- `RuntimeSimplify.cheap`: affine arithmetic normalization, stable Boolean
  flattening/sorting, deduplication, constant folding and reflexive identities.
  Boolean absorption is deliberately disabled in this saved version.
- `BoundSimplify`: exact opposing-bound reductions that expose identities and
  contradictions without invoking general quantifier elimination.
- Additional cleanup before and after equality-guided elimination, at CHC path
  composition, and around array-to-arithmetic conversion. These passes can
  expose identities for each other, but equivalent syntax can still affect
  downstream abstraction and solver heuristics.
- The opt-in `-array-term-equality` prototype: reconnect eliminated fixed
  parameters to initial-state variables, normalize array-equality orientation,
  and retain unchanged arrays when projecting stores. It remains off by default
  and was not enabled in the selected official campaign.
- Quantifier, bound, compositional-cleanup and termination-equality regressions,
  plus standalone formula inspection/replay tools under `srk/test/term_profile`.
  The diagnostic programs are not part of the measured analyzer invocation.

## Why this is deferred

The latest bounds-plus-affine official experiment and the selected correction-only
run produced the same outcome on every task. Their measured CPU totals were:

| Arm | Bounds + affine | Selected correction only |
|---|---:|---:|
| AMA reachability | 271.652007s | 380.041405s |
| AMA + Singular reachability | 830.153787s | 668.590296s |
| AMA + Singular termination | 1035.594071s | 1057.181240s |

The bounds-plus-affine experiment used a narrower configuration than this full
experimental branch: its custom Boolean cleanup was disabled. The separate
full-compositional, absorption-disabled official run used 1516.807310 CPU seconds
on termination, with 135 proofs, 20 unknown, 8 errors and 2 timeouts. The selected
correction-only run used 1057.181240 seconds, with 135 proofs, 20 unknown, 9 errors
and 1 timeout. These single runs used fresh native CHCs; they are evidence of
mixed behavior, not proof that a particular rewrite caused the entire difference.

Before preservation, this source passed 238 regression-test executions (including
300 generated equivalence checks inside a compositional case), 68 saved controls
including 37 unsafe/nonterminating controls, and the recorded build. The formula
checks cover equivalence, binder scope, integer divisibility, idempotence and
fresh-symbol behavior; they do not independently certify the C frontend.

## Work to revisit after PLDI

1. Isolate cleanup combinations on frozen CHCs and intermediate formulas, with
   repeated runs. Cheap, equivalence-preserving rewrites should expose identities
   before expensive QE; measure downstream effects as well as rewrite cost.
2. Investigate Boolean absorption separately. In selected-case probes, preserving
   the redundant branch in `x<y AND (x<y OR y<x)` helped termination: absorption
   timed out twice at 90s on `substring-alloca-2`, while disabling it finished in
   52.727/52.814 CPU seconds. Cleanup itself took only 0.038315 CPU seconds over
   204 calls. The downstream cause remains unresolved; no further investigation
   or absorption re-enablement is part of this preservation commit.
3. Handle surviving temporary arrays soundly in projection. `java_Nested-alloca`
   can raise `Not_found` at `projection_with_store_elim.decon_store` when an
   intermediate array is absent from `rmap`. Some cleanup variants happen to
   eliminate that temporary; the unchecked lookup remains. Add a regression
   retaining it, then represent/project it soundly or return a controlled
   unsupported result. Never drop constraints or introduce unconstrained stand-ins.
4. Reevaluate termination equality elimination with positive and nonterminating
   controls, maintaining initial-state links, binder scopes and array semantics.

Campaign identifiers and full evidence are preserved in the PLDI results archive:
`ama-correction-only-all565-official-300s-20261111T010625Z`,
`ama-bounds-affine-all565-official-300s-20261111T000328Z`, and the earlier
absorption-disabled campaign. Six frontend comparisons remain unresolved in the
selected run; `soundness_validated=false`. No audit qualification is waived here.
