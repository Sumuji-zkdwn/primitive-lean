#!/usr/bin/env python3
"""PR #103 fourth-probe audit. Exact arithmetic uses only Python stdlib.
Numerical noise examples are illustrative, not experimental PAD calibration.
"""
from fractions import Fraction as F
from itertools import combinations
from math import log

P=tuple(map(F,("30373/121700","6137/60850","66883/121700","1/10")))
Q=tuple(map(F,("760623/3042500","249697/760625","56861/608500","249696/760625")))
M=F(3,2)
T=(F(1,4),F(1,3),F(1,2),F(4,5))
R=(1298,12980,84370,147450,138186,128090,119935,86700,41616)

def response(s,p):
    return sum((v*s**j for j,v in enumerate(p)),F(0))
def poly(t,cs):
    return sum((v*t**j for j,v in enumerate(cs)),F(0))
def gap(t):
    return response(t**3,P)-response(t**4,Q)
def factor_gap(t):
    return -(t-1)*(2*t-1)*(3*t-1)*(4*t-1)*poly(t,R)/3042500
def profile(x,y):
    return (F(1)-M+x+2*y,M-2*x-3*y,x,y)
def solve(a,b):
    n=len(b)
    ab=[[F(v) for v in row]+[F(b[i])] for i,row in enumerate(a)]
    for j in range(n):
        k=next(i for i in range(j,n) if ab[i][j]!=0)
        ab[j],ab[k]=ab[k],ab[j]
        z=ab[j][j]
        ab[j]=[v/z for v in ab[j]]
        for i in range(n):
            if i!=j:
                z=ab[i][j]
                ab[i]=[v-z*w for v,w in zip(ab[i],ab[j])]
    return [ab[i][-1] for i in range(n)]
def four_grid(nodes,a,b):
    rows,rhs=[],[]
    for t in nodes:
        s,v=t**a,t**b
        A,B=(s-1)**2,(v-1)**2
        rows.append((A,A*(s+2),-B,-B*(v+2)))
        rhs.append(M*(v-s))
    x,y,z,w=solve(rows,rhs)
    return profile(x,y),profile(z,w)
def reading(u,p,alpha):
    s=u**alpha
    return sum(float(v)*s**j for j,v in enumerate(p))
def alpha_slope(u,p,alpha):
    s=u**alpha
    return log(u)*s*sum(j*float(p[j])*s**(j-1) for j in range(1,4))

assert sum(P)==sum(Q)==1
assert sum(j*x for j,x in enumerate(P))==sum(j*x for j,x in enumerate(Q))==M
assert all(v>0 for v in P+Q) and P!=Q
for t in T[:3]: assert gap(t)==0
assert gap(F(4,5))==F(13370535881703,371398925781250)
for t in [F(0),F(1,10),F(1,4),F(1,3),F(1,2),F(3,5),F(4,5),F(1)]:
    assert gap(t)==factor_gap(t) and poly(t,R)>0
assert response(F(1),P)==response(F(1),Q)==1
p4,q4=four_grid(T,3,4)
assert p4[1]==F(-10198519616027,34784891871190)
assert q4[1]==F(-442933771561904,434811148389875)
assert p4[1]<0 and q4[1]<0
for t in T: assert response(t**3,p4)==response(t**4,q4)
print("PASS exact gap",gap(F(4,5)),float(gap(F(4,5))))
print("PASS fixed-alpha four-probe exclusion via negative p1/q1",p4[1],q4[1])

nodes=tuple(map(F,("1/6","1/5","1/4","1/3","2/5","1/2","3/5","4/5")))
for a,b in ((6,7),(5,6),(4,5),(3,4),(2,3),(1,2),(2,5)):
    grid=list(combinations(nodes,4))
    assert len(grid)==70
    bad=0
    for xs in grid:
        p,q=four_grid(xs,a,b)
        if min(p+q)>0: bad+=1
    assert bad==0
    print("PASS finite grid alpha ratio",F(b,a),"0 positive of",len(grid))
print("Caution: 0/490 is a finite result, NOT universal injectivity.")

for u in (0.25,0.4,0.512,0.6,0.7,0.74,0.8,0.9,1.0):
    delta=reading(u,P,1)-reading(u,Q,4/3)
    dp=alpha_slope(u,P,1) if u!=1 else 0.
    dq=alpha_slope(u,Q,4/3) if u!=1 else 0.
    print(f"u={u:.3f} gap={delta:+.9f} illustrative_gap_over_sigma0.01={abs(delta)/.01:.3f} slopes={dp:+.5f},{dq:+.5f}")
best=max(((i/10000,abs(reading(i/10000,P,1)-reading(i/10000,Q,4/3))) for i in range(1,10000)),key=lambda z:z[1])
assert .738<best[0]<.742 and .0556<best[1]<.0557
print("PASS numerical grid maximum",best)
