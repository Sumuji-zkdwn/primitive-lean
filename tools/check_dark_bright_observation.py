#!/usr/bin/env python3
"""Exact rational finite regressions; not a substitute for the Lean proofs."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
import json


def output(x):
    a,b,c,d=x
    return a*c+b*d,b*c-a*d


def summary(x):
    a,b,c,d=x
    return (*output(x),a*a+b*b-c*c-d*d)


def norm2(x):
    return sum((v*v for v in x),F(0))


def mix(x,c=F(3,5),s=F(4,5)):
    a,b,u,v=x
    return c*a+s*v,c*b-s*u,c*u+s*b,c*v-s*a


def evolve(q,c=F(3,5),s=F(4,5)):
    r,i,z=q
    return (c*c+s*s)*r,(c*c-s*s)*i+c*s*z,(c*c-s*s)*z-4*c*s*i


def phase(x,p,q):
    a,b,c,d=x
    return p*a-q*b,q*a+p*b,p*c-q*d,q*c+p*d


def swap(x):
    return x[2],x[3],x[0],x[1]


def intensity(x):
    r,i=output(x)
    return r*r+i*i


def main():
    states=[tuple(map(F,x)) for x in product(range(-2,3),repeat=4)]
    pulses=[(F(1),F(0)),(F(0),F(1)),(F(3,5),F(4,5)),(F(-3,5),F(4,5)),
            (F(5,13),F(12,13)),(F(2),F(3)),(F(0),F(0))]
    phases=[(F(1),F(0)),(F(0),F(1)),(F(-1),F(0)),(F(3,5),F(4,5)),(F(5,13),F(12,13))]
    groups=[defaultdict(set) for _ in range(4)]
    checks=defaultdict(int)
    for x in states:
        r,i,z=summary(x)
        assert 4*(r*r+i*i)+z*z==norm2(x)**2
        checks['sphere_identity']+=1
        assert z==(25*output(mix(x))[1]+7*i)/12
        checks['one_probe_reconstruction']+=1
        for c,s in pulses:
            assert summary(mix(x,c,s))==evolve(summary(x),c,s)
            assert norm2(mix(x,c,s))==(c*c+s*s)*norm2(x)
            assert swap(mix(x,c,s))==mix(swap(x),c,s)
            checks['mixing_closure_and_norm']+=1
        for p,q in phases:
            assert summary(phase(x,p,q))==summary(x)
            checks['common_phase']+=1
        cur,swapped,qs=x,swap(x),summary(x)
        trace=[]
        for _ in range(13):
            assert summary(cur)==qs
            assert intensity(cur)==intensity(swapped)
            checks['trace_and_intensity_swap']+=1
            trace.append(output(cur))
            cur,swapped,qs=mix(cur),mix(swapped),evolve(qs)
        for group,key in zip(groups,[output(x),summary(x),tuple(trace[:2]),tuple(trace)]):
            group[key].add(x)
    partitions=[frozenset(map(frozenset,g.values())) for g in groups]
    assert partitions[1]==partitions[2]==partitions[3]
    left=tuple(map(F,(1,0,2,0))); right=swap(left)
    assert output(left)==output(right)==(F(2),F(0))
    assert norm2(left)==norm2(right)==5
    assert output(mix(left))==(F(2),F(-36,25))
    assert output(mix(right))==(F(2),F(36,25))
    for c,s in pulses:
        xb=tuple(map(F,(1,0,0,0))); xd=swap(xb)
        assert (output(mix(xb,c,s))==output(mix(xd,c,s)))==(c*s==0)
        checks['closure_obstruction_witness']+=1
    print(json.dumps({'status':'all checks passed','sample_states':len(states),
        'sample_grid':'[-2,2]^4 over integers','arithmetic':'fractions.Fraction',
        'checks':dict(checks),'partition_counts':dict(zip(
            ['current_coherence','coherence_plus_imbalance','two_readouts','depth_twelve_trace'],
            [len(g) for g in groups])),
        'scope':'Finite regressions only; no proof of general claims by enumeration.'},indent=2))


if __name__=='__main__':
    main()
