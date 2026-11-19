# Explicit Moore-Penrose pseudoinverses at both F16 singular inputs

Given original 16x16 rational signed basis actions L3 and L10, take
H_+= (L3+L10)^T(L3+L10), H_-=(L3-L10)^T(L3-L10).

From the exact projectors in F16SpectralProjectors,
H_+=4P_+ + 2P_0, H_-=4P_- + 2P_0.
The explicit matrices G_+=P_+/4 + P_0/2 and
G_-=P_-/4 + P_0/2 satisfy all four Moore-Penrose equations.

All proof claims are on the actual finite 16-dimensional F16 matrix,
checked using exact rational arithmetic in Lean. The corresponding
parameter-general real formula, its field cast, and the Fenchel quadratic
value relation still need separate proofs.

Reproduce with python -B -X utf8 tools/verify.py --integration-only.
