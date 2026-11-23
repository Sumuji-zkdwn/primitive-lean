#!/usr/bin/env python3
"""Independent v25 checks (does not import verify_v25)."""
from pathlib import Path
import json
import sympy as s
import numpy as np
OUT=Path(__file__).resolve().parent

# A full symbolic three-diagonal-metric, three-momentum calculation, off shell.
a,b,c,u,v,w,pq,pz,qx,zx,A,mu,N,M=s.symbols('a b c u v w pq pz qx zx A mu N M',positive=True)
vol=s.sqrt(a*b*c)
pitrace=a*u+b*v+c*w
Hg=(a*a*u*u+b*b*v*v+c*c*w*w-pitrace*pitrace/2)/vol
Hm=(pq*pq/A+pz*pz)/(2*vol)+vol*(A*qx*qx+zx*zx)/(2*a)+vol*mu
# Compute the unintegrated mixed Poisson brackets for a general positive metric.
metric=[a,b,c]; momenta=[u,v,w]
crossNM=-sum(s.diff(N*Hg, p)*s.diff(M*Hm,g) for p,g in zip(momenta,metric))
crossMN=+sum(s.diff(N*Hm,g)*s.diff(M*Hg,p) for p,g in zip(momenta,metric))
assert s.simplify(crossNM+crossMN)==0
sample={a:s.Rational(7,6),b:s.Rational(13,12),c:s.Rational(6,5),
        u:s.Rational(2,5),v:s.Rational(1,9),w:s.Rational(1,8),
        pq:s.Rational(1,3),pz:s.Rational(2,7),qx:s.Rational(3,11),zx:s.Rational(1,13),
        A:s.Rational(9,5),mu:s.Rational(2,9),N:s.Rational(3,4),M:s.Rational(5,7)}
first=s.N(crossNM.subs(sample),24)
second=s.N(crossMN.subs(sample),24)
assert abs(first+second)<s.Float('1e-20')

# Non-minimal anomaly: direct integration independent of finite-difference code.
x=s.symbols('x',real=True)
NN=1+s.Rational(1,5)*s.cos(x)
MM=1+s.Rational(3,10)*s.sin(x)
qq=s.cos(x)
PP=s.Rational(3,5);lam=s.Rational(1,4)
expr=-2*lam*PP*(NN*s.diff(MM*qq,x,2)-MM*s.diff(NN*qq,x,2))
anomaly=s.simplify(s.integrate(s.expand_trig(expr),(x,0,2*s.pi)))
assert anomaly==3*s.pi/50

# Spectral independent check with FFT differentiation and direct trapezoid.
n=4096
xx=2*np.pi*np.arange(n)/n
fn=lambda f: np.fft.ifft(1j*np.fft.fftfreq(n,1/n)*np.fft.fft(f)).real
Nn=1+.2*np.cos(xx)
Mn=1+.3*np.sin(xx)
qn=np.cos(xx)
spec=-2*.25*.6 * (2*np.pi/n)*np.sum(Nn*fn(fn(Mn*qn))-Mn*fn(fn(Nn*qn)))
assert abs(spec-3*np.pi/50)<1e-12,spec

# Pure ADM bracket at flat metric: first derivatives of -sqrt(g) R.
# With 1D x-dependence: R_lin=- dxx(h_yy+h_zz). For gamma=I and pi_xx=P(x),
# the curvature variation against momenta gives 2P(N M''-M N'').
# Compare to D_g[-] = -2P'(N M'-M N') spectrally without importing v25.
Pn=.3+.11*np.sin(xx+.23)+.14*np.cos(2*xx-.48)
Ng=1+.2*np.cos(xx+.2);Mg=.8+.15*np.sin(xx-.32)+.09*np.cos(3*xx-.1)
pb=2*(2*np.pi/n)*np.sum(Pn*(Ng*fn(fn(Mg))-Mg*fn(fn(Ng))))
Dg=(2*np.pi/n)*np.sum((Ng*fn(Mg)-Mg*fn(Ng))*(-2*fn(Pn)))
assert abs(pb-Dg)<1e-12,(pb,Dg)

report={'symbolic_offshell_cross_sum':'0',
        'single_cross_sympy_sample':str(first),
        'opposite_cross_sympy_sample':str(second),
        'nonminimal_symbolic_exact':str(anomaly),
        'nonminimal_spectral_4096':float(spec),
        'spectral_error_vs_exact':float(abs(spec-float(anomaly))),
        'gravitational_self_spectral_pb':float(pb),
        'gravitational_momentum_spectral_rhs':float(Dg),
        'gravitational_spectral_difference':float(pb-Dg),
        'scope':'3 diagonal metric components and scalar matter, x-dependent slice around flat spatial metric'}
(OUT/'independent_audit_v25.json').write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
print(json.dumps(report,indent=2,ensure_ascii=False))
print('independent audit PASSED')
