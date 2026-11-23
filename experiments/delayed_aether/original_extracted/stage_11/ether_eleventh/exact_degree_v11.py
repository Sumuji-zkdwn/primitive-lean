#!/usr/bin/env python3
"""Rational-arithmetic signed preimage certificate for a finite boxed S3 map.

The 4-vector vertex field uses the rational inverse-stereographic map, with
boundary vertices fixed to (1,0,0,0). Triangles/tetrahedra are linearly
interpolated and normalized. Critical orientation and preimage tests use
SymPy's exact Rational arithmetic, not floats.
"""
from fractions import Fraction as F
import json
from pathlib import Path
from sympy import Matrix, Rational
from verify_v11 import make_mesh
P=Path(__file__).resolve().parent


def projective_target():
    return Matrix([-1, F(1,7),-F(1,11),F(1,13)])


def vertices_rational(n):
    center=(F(1,20),-F(1,25),F(1,30))
    a=F(1,2)
    verts=[]
    for i in range(n+1):
      for j in range(n+1):
        for k in range(n+1):
          X=[-1+F(2*p,n) for p in (i,j,k)]
          x=[X[u]-center[u] for u in range(3)]
          r2=sum(v*v for v in x)
          d=r2+a*a
          q=[(r2-a*a)/d]+[2*a*v/d for v in x]
          if max(abs(t) for t in X)==1:
             q=[F(1),F(0),F(0),F(0)]
          assert sum(qi*qi for qi in q)==1
          verts.append(q)
    return verts


def exact_certificate(n):
    coords,tets=make_mesh(n)
    q=vertices_rational(n)
    tgt=[F(-1),F(1,7),F(-1,11),F(1,13)]
    candidates=[];preimages=[];negative_mixed=[];rank_deficient=[]
    for tri in tets:
        vi=[int(z) for z in tri]
        qs=[q[k] for k in vi]
        # Simple hemisphere exclusion for zero in convex hull.
        if min(v[0] for v in qs)<0 and max(v[0] for v in qs)>0:
            negative_mixed.append(vi)
            mat=Matrix.hstack(*[Matrix(v) for v in qs])
            d=mat.det()
            if d==0:rank_deficient.append(vi)
        if not any(v[0]<0 for v in qs):continue
        FF=[[v[j]-tgt[j]/tgt[0]*v[0] for j in (1,2,3)] for v in qs]
        if not all(min(row[d] for row in FF)<=0<=max(row[d] for row in FF) for d in range(3)):
            continue
        candidates.append(vi)
        A=Matrix(3,3,lambda i,j: FF[j+1][i]-FF[0][i])
        if A.det()==0:continue
        b=Matrix([-FF[0][i] for i in range(3)])
        lam_rest=A.inv()*b
        lam=[1-sum(lam_rest)]+list(lam_rest)
        if not all(c>0 for c in lam):continue
        Q=[sum(lam[i]*qs[i][j] for i in range(4)) for j in range(4)]
        if not Q[0]/tgt[0]>0:continue
        D=Matrix.hstack(Matrix(Q),*[Matrix([qs[i][j]-qs[0][j] for j in range(4)]) for i in (1,2,3)]).det()
        sgn=1 if D>0 else (-1 if D<0 else 0)
        assert sgn!=0
        preimages.append({'tetra_vertex_indices':vi,'sign':sgn,
                          'barycentric':[str(z) for z in lam],
                          'target_scale':str(Q[0]/tgt[0])})
    # If no mixed-sign tetrahedron has det(q0,q1,q2,q3)=0, then
    # no interpolated 4-vector vanishes anywhere (provided all q[0]!=0).
    assert all(v[0]!=0 for v in q)
    res={'n':n,'tetrahedra':len(tets),'boundary_is_constant':True,
         'mixed_scalar_tetrahedra':len(negative_mixed),
         'rank_deficient_mixed_tetrahedra':rank_deficient,
         'regular_value_candidates':len(candidates),
         'signed_preimages':preimages, 'degree':sum(d['sign'] for d in preimages)}
    return res


def main():
    records=[exact_certificate(n) for n in (6,8)]
    (P/'exact_degree_certificate.json').write_text(json.dumps(records,indent=2),encoding='utf8')
    for r in records: print('exact rational:',r['n'],'tetra',r['tetrahedra'],
        'candidates',r['regular_value_candidates'],'preimages',len(r['signed_preimages']),
        'degree',r['degree'],'rank_deficient_mixed',len(r['rank_deficient_mixed_tetrahedra']))
    assert all(r['degree']==-1 and not r['rank_deficient_mixed_tetrahedra'] for r in records)

if __name__=='__main__':main()
