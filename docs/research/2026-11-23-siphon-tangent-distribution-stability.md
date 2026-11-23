# E/L tangent-distribution observations: injective but unstable

Date: 2026-11-23. Companion to 2026-11-23-siphon-tangent-distribution-observability.md. Independent algebra; not a new Lean theorem.

The five-word probability observation Phi in the companion note is injective on the entire real plane. However, state identification is **not numerically stable uniformly**. It is not even locally bi-Lipschitz at the origin.

## An explicit pair invisible to the first four readings

For every t>0 define z_t=(t,-t³) and w_t=(-t,t³). The invariant I=v+u³ vanishes for both. Therefore E fixes both states; the L reading has first coordinates -t³ and +t³. Since the observation probability p(q)=1/(1+9q⁴) is even, the first **four** scalar observations (identity,E,E²,L) coincide *exactly* for z_t,w_t.

Set
\[
 C(t)=t^2(1+t^2+t^8)^2.
\]
The final (E after L) first coordinates are C(t)-t³ and C(t)+t³. The entire difference between the five signatures is the positive scalar
\[
 g(t)=p(C(t)-t^3)-p(C(t)+t^3).
\]

Elementary expansion gives two distinct asymptotic regimes:
\[
 g(t)\sim 72\,t^9\quad(t\to0^+),\qquad
 g(t)\sim \frac89\,t^{-87}\quad(t\to+\infty).
\]

At small t the input distance is 2t sqrt(1+t⁴), while the observation distance is O(t⁹). Hence the inverse on the image of Phi cannot be locally Lipschitz at the origin. At large t the input distance is asymptotic to 2t³ and diverges, while the observation difference tends to zero as O(t^-87). Hence the inverse is not uniformly continuous on the entire image.

The map is also **not an immersion at (0,0)**. Each of the five words fixes the origin and p'(0)=0, so the derivative of every probability coordinate of Phi vanishes there. Its differential has rank zero.

## Reproducible exact checks

Run python3 -m unittest discover -s tests -p 'test_siphon_e_distribution_stability.py' -v

The independent standard-library tests use Fraction throughout, check positivity of g, verify g(10)<10^-80 even though the corresponding states are more than 2000 units apart, and check the asymptotic coefficients using exact rational inequalities at t=1/100 and t=100.

## Consequence for the manifold-hypothesis discussion

The five probabilities distinguish all exact noiseless states, but without additional assumptions they provide neither a regular immersed manifold coordinate system nor a robust inverse from noisy observations. Recoverability, smooth regularity, coordinate invariance and conditioning are independent requirements. An application must separately constrain the observation range, measurement precision, noise and coordinate gauge.
