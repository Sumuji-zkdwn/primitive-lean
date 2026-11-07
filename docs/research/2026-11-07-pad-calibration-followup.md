# PAD four-layer: exact interpolation, calibration ambiguity, and three-probe local design

Date: 2026-11-07 (JST). Additive follow-up to PR #97 and PR #101. This is an **idealized finite inverse problem**, not a validated real liquid-jet PAD fit or energy-to-s calibration.

## Exact algebra (rational)

Let \`m=sum p_j\`, \`mu=sum j*p_j\`, and \`F_p(x)=sum p_j*x^j\`. Then

\`\`\`
R_p(x) := F_p(x) - m - mu*(x-1)
        = (x-1)^2 * (p2 + (x+2)*p3).
\`\`\`

For distinct \`t,s != 1\`, let \`r_x=R_p(x)/(x-1)^2\`. The coefficients are recovered by

\`\`\`
p3 = (r_s-r_t)/(s-t)
p2 = ((s+2)*r_t-(t+2)*r_s)/(s-t)
p1 = mu-2*p2-3*p3
p0 = m-mu+p2+2*p3
\`\`\`

Thus a cubic inverse problem reduces to interpolation of an affine function. The denominators show how near-coincident points and points near 1 amplify noise. The additive \`lean/PADFourLayerCalibration.lean\` proves denominator-free versions of these identities, plus exact error residuals and invisible directions.

If mass and mean are noisy, the **exact** residual error is
\`delta_R(x) = delta_F(x) - delta_m - (x-1)*delta_mu\`.

## Energy-dependent profiles defeat two-energy inversion

The common latent profile across energies is a substantive assumption. For any one probe \`t\`, the coefficient direction

\`\`\`
(-t, 1+2*t, -(2+t), 1)
\`\`\`

has zero mass, zero mean, and zero response at that probe. Different energy-specific profiles can therefore vary in distinct invisible directions even if mass and mean stay fixed.

An exact **positive rational calibration ambiguity** is independently checked in \`tools/check_pad_calibration.py\`:

\`\`\`
p=(1/4,1/4,1/4,1/4), t=1/20, s=7/20
p'=(72632349/290705272,467169097/1889584268,
    967414805/3779168536,116649375/472396067)
t'=51/1000, s'=351/1000
\`\`\`

Both have mass 1, mean 3/2, and the *same* two responses \`8421/32000\` and \`12123/32000\`; all coefficients are positive, but \`p != p'\`. Thus independently uncertain observation coordinates cannot be self-calibrated from two PAD measurements.

## Numerical model of a *shared* calibration nuisance (not physical data)

Write nominal coordinates as \`u_i in [0.05,0.95]\` and posit the illustrative mapping \`s_i(alpha)=u_i^alpha\`. At \`alpha=1\` and exact mass and mean, the unknown profile has two orthonormal coordinates and \`alpha\` is a third unknown. The Jacobian of \`F_p(u_i^alpha)\` is

\`\`\`
J_i = [(1,u_i,u_i^2,u_i^3) @ N, F'_p(u_i)*u_i*log(u_i)]
\`\`\`

where columns of \`N\` are an orthonormal basis of the mass/mean nullspace. A two-probe Jacobian is 2x3 and necessarily has a null direction. A 3x3 Jacobian can be nonsingular for suitably separated probes.

Illustrative independent probe noise SD=0.001, prior SD(alpha)=0.05, fixed first two points (0.05,0.369), no positivity projection:

| Nominal profile | 2 points alpha fixed, profile RMSE | 2 points alpha SD .05, profile RMSE | Best third point (numerical) | 3 points alpha free, profile RMSE |
|---|---:|---:|---:|---:|
| uniform | .022705 | .176202 | .819019 | .035552 |
| PR #97 p+ | .022705 | .189462 | .820001 | .037479 |
| PR #97 p- | .022705 | .162996 | .818546 | .033783 |

All-three-point joint optimization over [0.05,0.95] yields candidates:
uniform (0.0500,0.3056,0.8238); p+ (0.0500,0.3104,0.8230); p- (0.0500,0.3027,0.8258). These are **local linearized, nominal-profile-dependent numerical results**, not global optimality proofs.

With a Gaussian prior on alpha, its first-order contribution is rank-one correlated noise:
\`Sigma_eff = sigma^2 I + tau^2 v v^T\` with \`v_i = F'_p(u_i)*u_i*log(u_i)\`.
The Python checker independently cross-validates this covariance against the joint Fisher formula.

## Scope and next physical experiment

No measured eKE-to-s mapping, actual electron-water DCS, detector angular/energy response, cylinder escape geometry, true error covariance, nor common detected-depth distribution has been supplied. Real measurements need calibration of \`c2(E)\`, scattering rates, attenuation and escape, nascent \`beta0(E)\`, analyzer acceptance, normalization, separate mass/mean precision and cross-energy correlations. Measurements at different eKE may have **different detected profiles**; if so, the common-p inverse design fails.

Run \`python -B tools/check_pad_calibration.py\` from the repository root. It writes \`docs/pad_calibration_results.json\`. The Lean sidecar must be independently checked by the GitHub workflow \`.github/workflows/pad-calibration.yml\`; the Python PASS does not imply Lean success.

Relevant literature: Schild et al., JPCL 11, 1128–1134 (2020), DOI 10.1021/acs.jpclett.9b02910; Dupuy et al., PRL 130, 156901 (2023), DOI 10.1103/PhysRevLett.130.156901; Dupuy et al., Accounts Chem. Res. 56, 215–223 (2023), DOI 10.1021/acs.accounts.2c00678.
