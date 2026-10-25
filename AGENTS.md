# 原始の形式化

Independent mathematical formalization; Research is a read-only source.
Use conventional elastica notation. Distinguish definitions, additional hypotheses,
hand proofs, Lean proofs, and numerical checks. Never replace a variational derivative
by an assumed formula. Keep all dependencies pinned and record actual build results.
The initial scope is smooth planar open curves of fixed length, end positions and
end tangents, with general signed-curvature density. No automatic dynamics, convexity,
evenness, minimizer existence, or general integration of older models is assumed.

Keep the prose-to-theorem mapping and verification records current when editing.
The main theorem connects actual functional derivatives to interior equations;
do not silently strengthen its input to a minimizer or its conclusion to dynamics.

The canonical reader is 原始の形式化.md / .html, including the former linear-input
companion. Keep the proof files in their established roles: lean/Elastica and
linear_input/lean_check, with the existing names, configuration and joint checker.
The user explicitly chose reader/entry-point consolidation instead of library
migration. Use tools/verify.py as the unified orchestration entry point.
Keep explicit boundaries between general densities, quadratic specialization,
the curvature phase system, and separately chosen feedback/internal updates.
