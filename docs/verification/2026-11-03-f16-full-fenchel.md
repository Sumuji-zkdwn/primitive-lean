# Full 16D F16 Fenchel domain and normal-equation value (2026-11-03)

## Source and exact interpretation

New additive Lean supplement `F16FenchelFull.inc`, based on the already
verified PR #32 and the unchanged original signed left-pencil `realPencilAll t`.
The state is `EuclideanSpace ℝ (Fin 16)`, not the earlier selected 2D section.

Write `A_t = L_(e3+t e10)`, `N_t = A_t* A_t`, and
`V_t(z) = <A_t z,A_t z>/2`. With physical pairing <p,z>,
the real Fenchel score is `B_t(p,z)=<p,z>-V_t(z)`.

**Exact dual domain:** `{p : BddAbove(range(B_t(p,·)))} = range(N_t)`.
The proof uses the finite-dimensional adjoint-range identity
`range(A* A) = (ker A)^perp` and a constructive unbounded null-direction ray.

**Exact finite Fenchel value:** if `p=N_t z₀`, then
`sup_z B_t(p,z)=V_t(z₀)`, with equality attained at `z=z₀`.
Different normal-equation solutions have the same value.

The already proven matrix rank is 12 at `t=±1` and 16 otherwise. The
new theorem uses the *full* 16x16 pencil, so both singular values are
relevant, unlike the 2D PR #32 section which detects only `t=+1`.

These theorems are a pseudoinverse-free exact characterization. A later
module can identify the minimum-norm solution explicitly with the
Moore-Penrose pseudoinverse, without changing these foundational results.

## Reproduce

`python -B -X utf8 tools/verify.py --integration-only`

All new Lean modules remain additive with source-hash provenance, no
new axioms, no `sorry`, no physical-time assumptions. Status is determined
by the exact GitHub Actions head SHA; a written theorem is not a verified
proof before CI passes.
