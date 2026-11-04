# PR #21 projective sampling integration

The standalone PR #21 source at commit
`f4454b25d9bde057aa162ef7c9e4829dc007404e` was previously unregistered with the
repository's joint proof checker. Its two source files use namespace
`LinearInputWFSObservation`; the existing Elastica scanner assumes namespace
`Elastica` for every file in `lean/Elastica`. Copying these files there unchanged
would therefore produce missing declarations in the complete axiom audit.

The integration preserves exact original blobs under
`sources/wfs_projective_pr21_20261101/` and supplies the additive
`linear_input/lean_check/WFSProjectiveSampling.inc` adapter for the established
supplement checker. The adapter has one namespace block and uses the imports
already present in `All.lean`. The proof/configuration provenance is recorded in
`2026-11-02-wfs-projective-integration-provenance.json`.

An isolated original-source `--trust=0` run reproduced a genuine proof error:
the `rfl` alternative in `sampleKernel_iff_gcd_zero` substituted away `m`, which
was subsequently referenced in `he m`. The adapter instead names the equality
and substitutes `d`. It also combines consecutive `intro` steps and removes one
unused simp argument to satisfy the strict warning-free policy. The original
declarations and mathematical statements are otherwise retained.

The adapter proves the homogeneous WFS involution/conjugacy, the positive-period
coprimality criterion for cyclic sampling, the finite joint-sampling witness,
the arbitrary-period gcd characterization of the observation kernel, and the
0/1 observation pseudodistance laws. It does not formalize the general kernel
cardinality formula or a constructed projective quotient.

Local verification used pinned Lean 4.30.0-rc2 and the existing dependency cache.
The original source failed; the repaired 33-declaration probe used only allowed
standard axioms, and the final adapter compiled with the integration's exact
`All.lean` import list, exit code 0 and zero warnings. This is an isolated
source check, not yet the full repository integration audit. The independent
retained Python checker passed 20,790 kernel/image cases and 66,150
pseudometric triples. The final integration record supplies the complete joint
proof/audit result and its exact commit.
