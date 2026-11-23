#!/usr/bin/env python3
"""Independent, exact-rational 5-cell canonical Poisson bracket audit.

This code does not import verify_v24.py, and uses an alternate positive
polynomial constitutive law A=1+2(q-z)^2 (not the tanh law).
"""
from pathlib import Path
import json
import sympy as s

OUT=Path(__file__).resolve().parent
n=5
q=s.symbols('q0:5')
z=s.symbols('z0:5')
p=s.symbols('p0:5')
r=s.symbols('r0:5')
F=lambda i:(i+5)%5
frac=s.Rational
vals={}
qval=[frac(1,7),frac(3,11),-frac(2,9),frac(4,13),-frac(1,8)]
zval=[frac(2,11),-frac(1,9),frac(1,7),frac(1,10),-frac(2,13)]
pval=[frac(4,9),frac(1,5),-frac(3,8),frac(2,7),frac(1,6)]
rval=[-frac(3,7),frac(2,9),frac(1,4),frac(2,13),-frac(1,5)]
a=[frac(11,10),frac(13,10),frac(7,6),frac(9,8),frac(6,5)]
N=[frac(7,6),frac(11,9),frac(5,4),frac(8,7),frac(13,11)]
M=[frac(9,10),frac(6,7),frac(13,8),frac(5,6),frac(11,12)]
for sy,va in zip(q,qval): vals[sy]=va
for sy,va in zip(z,zval): vals[sy]=va
for sy,va in zip(p,pval): vals[sy]=va
for sy,va in zip(r,rval): vals[sy]=va

def H(lapse,kappa,matched):
    density=[]
    for j in range(n):
        dq=(q[F(j+1)]-q[F(j-1)])/2
        dz=(z[F(j+1)]-z[F(j-1)])/2
        y=q[j]-z[j]
        A=1+2*y*y
        B=A if matched else 1
        density.append((p[j]**2/A+r[j]**2+B*dq*dq+dz*dz)/(2*a[j]) + a[j]*kappa*y*y/2)
    return s.Add(*[lapse[j]*density[j] for j in range(n)])

def full_exact_bracket(matched,kappa):
    HN=H(N,kappa,matched)
    HM=H(M,kappa,matched)
    bracket=s.S.Zero
    for qs,ps in [(q,p),(z,r)]:
        for f_i,p_i in zip(qs,ps):
            # evaluate each derivative BEFORE summing to avoid giant expressions
            aa=s.diff(HN,f_i).subs(vals)
            bb=s.diff(HM,p_i).subs(vals)
            cc=s.diff(HN,p_i).subs(vals)
            dd=s.diff(HM,f_i).subs(vals)
            bracket+=aa*bb-cc*dd
    return s.cancel(bracket)

def gradient_only(matched):
    GQ=[]; GZ=[]
    # exact centered derivative of spatial flux at each node
    for i in range(n):
        def flux_q(j,lapse):
            jj=F(j)
            y=qval[jj]-zval[jj]
            AA=1+2*y*y
            BB=AA if matched else 1
            return lapse[jj]*BB*(qval[F(jj+1)]-qval[F(jj-1)])/2/a[jj]
        def flux_z(j,lapse):
            jj=F(j)
            return lapse[jj]*(zval[F(jj+1)]-zval[F(jj-1)])/2/a[jj]
        # dH_N/dq_i is local - D(N B dq/a), no factors h since h=1
        # local source is proportional to N_i; antisym cancellation
        dNq=-(flux_q(i+1,N)-flux_q(i-1,N))/2
        dMq=-(flux_q(i+1,M)-flux_q(i-1,M))/2
        dNz=-(flux_z(i+1,N)-flux_z(i-1,N))/2
        dMz=-(flux_z(i+1,M)-flux_z(i-1,M))/2
        A=1+2*(qval[i]-zval[i])**2
        dNpq=N[i]*pval[i]/(a[i]*A)
        dMpq=M[i]*pval[i]/(a[i]*A)
        dNpz=N[i]*rval[i]/a[i]
        dMpz=M[i]*rval[i]/a[i]
        GQ.append(dNq*dMpq-dNpq*dMq)
        GZ.append(dNz*dMpz-dNpz*dMz)
    return s.cancel(sum(GQ)+sum(GZ))

def main():
    results=[]
    for matched in [True,False]:
        values=[]
        for kap in [s.S.Zero,s.Rational(7,5)]:
            pb=full_exact_bracket(matched,kap)
            values.append(pb)
        gradient=gradient_only(matched)
        assert values[0]==values[1]==gradient,(matched,values,gradient)
        results.append({'model':'matched' if matched else 'mismatched',
                        'poisson_exact':str(values[0]),
                        'gradient_only_exact':str(gradient),
                        'potential_zero_vs_nonzero_exactly_identical':True,
                        'float_value':float(values[0])})
    report={'independent_audit':True,'grid':'5-site periodic centered-difference lattice',
            'arithmetic':'exact rational SymPy, no float approximations',
            'constitutive':'A=1+2(q-z)^2; independent of tanh model',
            'canonical_bracket':'direct symbolic derivatives of two independently constructed smeared Hamiltonians',
            'results':results,
            'warning':'even matched model does not have exact finite-lattice Dirac algebra because central differences lack Leibniz product rule; comparison is with exact lattice gradient expression, not with continuum closure'}
    (OUT/'exact_rational_audit_v24.json').write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps(report,indent=2,ensure_ascii=False))

if __name__=='__main__':main()
