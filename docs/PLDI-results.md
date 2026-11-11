# Selected AMA PLDI results

Jake selected campaign `ama-correction-only-all565-official-300s-20261111T010625Z`
on November 10, 2026 (Los Angeles). This is the correctness-fix-only source
configuration on the earlier forward-sign baseline, with older runtime fixes
retained. Later bounds, affine, compositional Boolean, and extra pre-QE cleanup
patches are excluded. Termination equality-transition optimization remains off.

The only production-code difference from commit
`27e36d0d42a9daba843c39ecc2d5e0a673c56b75` is `srk/src/quantifier.ml`.
The 42 added quantifier regressions check semantic equivalence, including
polarity, integer divisibility, nested binders, arrays, and Boolean quantifiers.
They do not require optional optimization-specific output shapes.

| Arm | Tasks | Proven | Unknown | Errors | Timeouts | CPU seconds |
|---|---:|---:|---:|---:|---:|---:|
| AMA reachability | 200 | 6 | 186 | 8 | 0 | 380.041405 |
| AMA + Singular reachability | 200 | 138 | 54 | 8 | 0 | 668.590296 |
| AMA + Singular termination | 165 | 135 | 20 | 9 | 1 | 1057.181240 |

Every task kept its outcome versus the immediately preceding bounds-plus-affine
campaign. CPU changes were +39.90%, -19.46%, and +2.08%, respectively. These are
single attempts with fresh native CHCs, not a controlled causal timing claim.

Flags: `-array-forward-signs -array-sign-annotation pruned -array-sign-cleanup`,
plus `-array-cra` for reachability or `-array-term` for termination. The
without-Singular arm adds `-array-cra-no-singular`. Formula dumps and optional
profiling are disabled. Reachability uses 300s wall/CPU soft, 310s CPU hard,
16 GB RAM, one core and worker. Termination retains its historical 300s CPU
soft/310s hard, 8 GB, one core and worker, internal limits and ILP32 frontend.
All original tasks are retained, including the approved corrected `strcat_len`.

All 108 fresh test cases and 92 control invocations passed. The independent
integrity audit verified all 565 final XML rows and unchanged inputs, candidate,
tools, harness, flags and fresh controls. Six reachability frontend structural
comparisons remain unresolved; the original final audit remains `passed=false`.
Official selection does not resolve those comparisons or rewrite that audit.
Termination final and official audits passed.

`soundness_validated=false`: these are raw AMA proof claims; UnknownSAT does
not establish a concrete C counterexample. C/SeaHorn translation, finite
arithmetic, overflow, memory safety and ILP32/LP64 caveats remain.

The complete archive in the local PLDI Official Results folder retains sources,
CHCs, controls, logs, provenance, timings and final XML. All 16,599 files
(800,281,821 bytes) were checksum-verified. The measured Linux executable SHA-256
is `414e35a2f2c1771887ccd0dfb1546d3b83d8ec73b3f161713a61f35443ff5a40`.
Its archive, rather than any subsequent rebuild, is the timing artifact.
