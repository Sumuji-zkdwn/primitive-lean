"""Exact rational regression for the selected F16/E Fenchel section.

This is an independent algebraic smoke test, not a substitute for Lean.
"""
from fractions import Fraction as F

def section(t, s, v):
    return (1-t)**2*s*s + (1+t*t)*v*v/2

def score(t, p, q, s, v):
    return p*s + q*v-section(t,s,v)

def atlas_e(t,s,v):
    k=2*(1-t)**2; a=1+t*t
    return k*s*s/2+a*v*v/2

def check():
    data=[F(-3),F(-2),F(-1),F(0),F(1),F(2),F(3)]
    for t in data:
        for s in data:
            for v in [F(-2),F(0),F(2)]:
                assert section(t,s,v)==atlas_e(t,s,v)
                assert section(t,s,v)>=0
        assert (2*(1-t)**2*(1+t*t)==0)==(t==1)
    for p in data:
        for q in data:
            assert score(0,p,q,p/2,q)==p*p/4+q*q/2
            assert score(-1,p,q,p/8,q/2)==p*p/16+q*q/4
            assert score(1,F(0),q,F(3),q/2)==q*q/4
            for s in data:
                for v in data:
                    assert score(0,p,q,s,v)<=p*p/4+q*q/2
                    assert score(-1,p,q,s,v)<=p*p/16+q*q/4
                    assert score(1,F(0),q,s,v)<=q*q/4
    for B in data:
        for p in [F(-2),F(-1),F(1),F(2)]:
            q=F(3); s=(B+1-q*q/4)/p
            assert score(1,p,q,s,q/2)==B+1
    return {"passed":True,"section":"exact rational E-atlas specialization",
            "dual":"finite at t=0, t=-1; t=1 bounded iff p=0",
            "scope":"2D selected F16 section only, not the full 16D conjugate"}

if __name__ == "__main__":
    import json
    print(json.dumps(check(),indent=2))
