# F16 full-parameter Gram pseudoinverse (draft verification record)

Input: the unchanged original F16 \`realPencilAll t\` in PR #33 and exact rational projectors in PR #34. PR #35 gives the singular rational formulas. This dependent proof group explicitly records the general real formula and four Penrose equations for the **Gram** matrix.

For all real t:
N_t = (t+1)^2 P+ + (t-1)^2 P- + (1+t^2) P0;
N_t^+ = inv0((t+1)^2) P+ + inv0((t-1)^2) P- + inv0(1+t^2) P0,
where inv0(0)=0 and inv0(x)=1/x otherwise.

The candidate for the original left action is A_t^+ = N_t^+ A_t^T. This must be distinguished from N_t^+. The current Lean group checks all four Gram Penrose identities and states separate partial identities for the left-action candidate. It does **not** assert the remaining left-action Penrose identities or the PR #33 quadratic dual value as verified Lean theorems.

At t=1 the null sector is P-; at t=-1 it is P+. The finite Fenchel domain is the orthogonal complement of the respective kernel (dimension 12) and the value, where finite, is one half p^T N_t^+ p; otherwise it is +infinity as an extended-real conjugate. The formula is noncontinuous in operator norm at both singular points, where the divergent coefficient is replaced by zero. This is a mathematical consequence pending a separate Lean proof of continuity statements and Fenchel coordinate transport.

CI and axiom audit on a fixed source SHA are required before claiming the present draft proof group as compiled. No geometrical or physical holonomy interpretation is used.
