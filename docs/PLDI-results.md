# Selected AMA PLDI results

Jake selected campaign `ama-official-seahorn-tapis-all565-300s-20261112T062304Z`
on November 12, 2026. It is the soundness-correction source of commit
`f0a7259ac5e0ab58e8651404b909adbb7314ae0d` plus four production-code changes,
measured as one binary on both CHC frontends:

- `srk/src/chc.ml`: drop vacuous clauses whose matrix simplifies to `true`
  (dead branches in TAPIS-frontend CHCs previously crashed the reader).
- `srk/src/runtimeSimplify.ml`: `cheap` (from `ama-post-pldi-optimizations`)
  orders And/Or operands and linear-sum terms by a structural digest instead of
  hash-consing order (ties fall back to the internal order), normalizes affine
  sums, flattens nested And/Or, and keeps real-sorted operands real.
- `srk/src/iteration.ml`: apply `cheap` before `simplify_dda`.
- `srk/src/pmfa.ml`: in `decon_store`, an array that is not a transition array
  (e.g. a SeaHorn memory temporary) leaves its array equation unprojected
  instead of raising `Not_found`.

Later bounds, affine, compositional Boolean and extra pre-QE cleanup patches
remain excluded. Termination equality-transition optimization remains off.

SeaHorn frontend (all original tasks):

| Arm | Tasks | Proven | Unknown | Errors | Timeouts | CPU seconds |
|---|---:|---:|---:|---:|---:|---:|
| AMA reachability | 200 | 6 | 186 | 8 | 0 | 239.931668 |
| AMA + Singular reachability | 200 | 138 | 54 | 8 | 0 | 609.211373 |
| AMA + Singular termination | 165 | 138 | 21 | 5 | 1 | 1080.841828 |

Against the previous selection (`ama-correction-only-all565-official-300s-20261111T010625Z`) no reachability verdict
changed. Termination gained insertionsort-alloca-1, insertionsort-alloca-2 and
java_Nested-alloca (previously `Not_found`); twisted-alloca went from `Not_found`
to a timeout and openbsd_cstrstr-alloca-2 from a timeout to unknown.

TAPIS frontend (same binary; TAPIS e8d7d7b0 for Array84 and e8d7d7b0 plus
vector-argument-index.patch for Vector9, rewrite on; all 186 CHC sets are
clause-identical to those given to TAPIS, VAPHOR and Spacer):

| Suite | Arm | Tasks | Proven | Unknown | Errors |
|---|---|---:|---:|---:|---:|
| Array | AMA | 84 | 1 | 72 | 11 |
| Array | AMA + Singular | 84 | 50 | 23 | 11 |
| Vector | AMA | 9 | 0 | 0 | 9 |
| Vector | AMA + Singular | 9 | 0 | 0 | 9 |

All 9 Vector9 CHC systems from TAPIS are non-linear (shared procedure
summaries), which AMA does not support.

Flags: `-array-forward-signs -array-sign-annotation pruned -array-sign-cleanup`,
plus `-array-cra` for reachability or `-array-term` for termination. The
without-Singular arm adds `-array-cra-no-singular`. Formula dumps and optional
profiling are disabled. Reachability uses 300s wall/CPU soft, 310s CPU hard,
16 GB RAM, one core and worker. Termination retains its historical 300s CPU
soft/310s hard, 8 GB, one core and worker, internal limits and ILP32 frontend.
All original tasks are retained, including the approved corrected `strcat_len`.

All 108 fresh test cases and 92 control invocations passed. The independent
integrity audit verified all 565 final XML rows and unchanged inputs, candidate,
tools, harness, flags and fresh controls. 4 reachability frontend structural
comparisons remain unresolved; the original final audit remains `passed=false`.
Official selection does not resolve those comparisons or rewrite that audit.
Termination final and official audits passed. Before selection, the `pmfa.ml`
change was checked on five non-terminating mutants of affected termination
tasks: none was claimed terminating.

`soundness_validated=false`: these are raw AMA proof claims; UnknownSAT does
not establish a concrete C counterexample. C/SeaHorn translation, finite
arithmetic, overflow, memory safety and ILP32/LP64 caveats remain.

The complete archive in the local PLDI Official Results folder retains sources,
CHCs, controls, logs, provenance, timings and final XML. All 19,883 files
(1,043,923,399 bytes) were checksum-verified. The measured Linux executable SHA-256
is `b835215f317646e85a13c79a1de13fcd83cf206b1ecded4d5d3017354859617e`.
Its archive, rather than any subsequent rebuild, is the timing artifact.
