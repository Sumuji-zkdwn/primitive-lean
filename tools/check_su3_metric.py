"""Exact algebraic test: squashed SU(3) metric retains su3+su2+u1 symmetries.

Proves a dimension-4 Lie algebra stabilizer of a left-invariant positive
SU(3) metric at the identity, and computes its scalar curvature by Milnor's
unimodular Lie-group formula. These are algebraic, not 12D vacuum solutions.
"""
import sympy as S

I=S.I
rt3=S.sqrt(3)
zero=S.zeros(3)

def M(rows):return S.Matrix(rows)
lam=[
 M([[0,1,0],[1,0,0],[0,0,0]]),
 M([[0,-I,0],[I,0,0],[0,0,0]]),
 S.diag(1,-1,0),
 M([[0,0,1],[0,0,0],[1,0,0]]),
 M([[0,0,-I],[0,0,0],[I,0,0]]),
 M([[0,0,0],[0,0,1],[0,1,0]]),
 M([[0,0,0],[0,0,-I],[0,I,0]]),
 S.diag(1,1,-2)/rt3,
]
T=[-I*L/2 for L in lam]

def check():
    for a in range(8):
        for b in range(8):
            assert S.simplify(-2*S.trace(T[a]*T[b]))==int(a==b)
    f={}
    for a in range(8):
        for b in range(8):
            C=T[a]*T[b]-T[b]*T[a]
            for c in range(8):
                value=S.simplify(-2*S.trace(C*T[c]))
                f[a,b,c]=value
                assert S.im(value)==0
            assert (C-sum((f[a,b,c]*T[c] for c in range(8)),zero)).applyfunc(S.simplify)==zero
    ad=[]
    for a in range(8):
        ad.append(S.Matrix(8,8,lambda c,b:f[a,b,c]))
    weights=[1,1,1,2,2,2,2,1]
    Q=S.diag(*weights)
    defects=[(m.T*Q+Q*m).applyfunc(S.simplify) for m in ad]
    for a in (0,1,2,7):assert defects[a]==S.zeros(8)
    for a in (3,4,5,6):assert defects[a]!=S.zeros(8)
    system=S.Matrix(64,8,lambda row,col:defects[col][row//8,row%8])
    assert system.rank()==4
    null=system.nullspace()
    assert len(null)==4
    for v in null:
        assert v[3]==v[4]==v[5]==v[6]==0
    # Check invariance algebra closes and u(1) commutes with su(2).
    for a in (0,1,2,7):
        for b in (0,1,2,7):
            for c in (3,4,5,6):assert f[a,b,c]==0
    for a in (0,1,2):
        assert all(f[7,a,c]==0 for c in range(8))
    # For compact unimodular groups, scalar R = -1/4∑||[E_a,E_b]||²
    # -1/2∑ Killing(E_a,E_a), with E_a=T_a/sqrt(q_a).
    scalar_coupling=S.simplify(sum(f[a,b,c]**2*weights[c]/(weights[a]*weights[b])
        for a in range(8) for b in range(8) for c in range(8)))
    killing_diag=[S.simplify(sum(f[a,b,c]*f[a,c,b] for b in range(8) for c in range(8)))
                  for a in range(8)]
    assert killing_diag==[-3]*8,killing_diag
    scalar=S.simplify(-scalar_coupling/4 - sum(killing_diag[a]/weights[a] for a in range(8))/2)
    assert scalar>0
    print('PASS exact su3 commutators and left-invariant metric symmetry')
    print('stabilizer dim:',len(null),'basis: λ1,λ2,λ3,λ8 = su2+u1')
    print('full gauge Lie algebra with always-present left su3: 8+4=12')
    print('scalar bracket sum',scalar_coupling,'scalar curvature',scalar)
    print('positive scalar implies no *untwisted* harmonic Dirac spinors on compact SU3')

if __name__=='__main__':check()
