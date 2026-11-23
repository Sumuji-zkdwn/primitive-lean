#!/usr/bin/env python3
"""Stage 32 independent audit: build actual 4-simplex dihedral angles from Gram normals.

Avoids using stage32.verify_v32 formulas for action, geometric incidence, and gradients.
Recomputes 4 internal + 16 boundary triangular hinges in 4D individually.
"""
from __future__ import annotations
from collections import Counter
from itertools import combinations
from pathlib import Path
from math import pi
import json
import sympy as sp
import mpmath as mp

mp.mp.dps=75
ROOT=Path(__file__).resolve().parent
E,F=4,5
POST=[(0,1,2,4,5),(0,1,3,4,5),(0,2,3,4,5),(1,2,3,4,5)]


def edge_squared(a,b,s):
    return mp.mpf(0) if a==b else (s if {a,b}=={4,5} else mp.mpf(1))


def dihedral_gram(simplex,triangle,s):
    # Gram of four simplex edge vectors from chosen first vertex.
    vertices=list(simplex)
    rays=vertices[1:]
    g=mp.matrix([[ (edge_squared(vertices[0],vi,s)
                     +edge_squared(vertices[0],vj,s)
                     -edge_squared(vi,vj,s))/2 for vj in rays] for vi in rays])
    inv=g**-1
    normals=mp.matrix(5)
    # matrix gram of normals opposite each of 5 vertices
    for i in range(5):
        for j in range(5):
            if i==0 and j==0: x=sum(inv[a,b] for a in range(4) for b in range(4))
            elif i==0: x=-sum(inv[a,j-1] for a in range(4))
            elif j==0: x=-sum(inv[i-1,b] for b in range(4))
            else: x=inv[i-1,j-1]
            normals[i,j]=x
    opposite=[q for q in vertices if q not in triangle]
    assert len(opposite)==2
    ii,jj=map(vertices.index,opposite)
    c=-normals[ii,jj]/mp.sqrt(normals[ii,ii]*normals[jj,jj])
    assert abs(c)<=1+mp.mpf('1e-60'),(triangle,s,c)
    return mp.acos(c),c


def triangle_area(triangle,s):
    a,b,c=triangle
    aa=edge_squared(a,b,s)
    bb=edge_squared(a,c,s)
    cc=edge_squared(b,c,s)
    return mp.sqrt(4*aa*bb-(aa+bb-cc)**2)/4


def complete_action(x):
    s=x*x
    tet=Counter(face for simplex in POST for face in combinations(simplex,4))
    boundary_tet=[face for face,n in tet.items() if n==1]
    btri={t for tet in boundary_tet for t in combinations(tet,3)}
    triangles={t for simplex in POST for t in combinations(simplex,3)}
    inner=triangles-btri
    assert len(inner)==4 and len(btri)==16 and len(tet)==14
    result=mp.mpf('0')
    for tri in triangles:
        angles=[dihedral_gram(simplex,tri,s)[0] for simplex in POST if set(tri).issubset(simplex)]
        angle_target=2*mp.pi if tri in inner else mp.pi
        result+=triangle_area(tri,s)*(angle_target-sum(angles))
    return result


def grouped_action(x):
    s=x*x
    ain=x*mp.sqrt(4-s)/4
    aouter=mp.sqrt(3)/4
    cin=(s-2)/(2*(s-3))
    cbase=1-3*s/4
    cside=mp.sqrt(s/(8*(3-s)))
    theta_in=mp.acos(cin)
    theta_base=mp.acos(cbase)
    theta_side=mp.acos(cside)
    return (4*ain*(2*mp.pi-3*theta_in)
            +4*aouter*(mp.pi-theta_base)
            +12*aouter*(mp.pi-2*theta_side))


def exact_sympy():
    s=sp.symbols('s')
    G=sp.Matrix([[s,s/2,s/2,s/2],
                 [s/2,1,sp.Rational(1,2),sp.Rational(1,2)],
                 [s/2,sp.Rational(1,2),1,sp.Rational(1,2)],
                 [s/2,sp.Rational(1,2),sp.Rational(1,2),1]])
    det=sp.factor(G.det())
    inv=G.inv()
    assert sp.simplify(det-s*(8-3*s)/16)==0
    assert sp.simplify(sp.diff((s-2)/(2*(s-3)),s)+1/(2*(s-3)**2))==0
    assert sp.simplify((-inv[2,3]/inv[2,2])-(s-2)/(2*(s-3)))==0
    assert sp.simplify(sum(inv)-inv[0,0])==0
    cbase=sp.factor(sum(inv[:,0])/inv[0,0])
    assert sp.simplify(cbase-(1-3*s/4))==0
    side_sq=sp.factor(inv[0,3]**2/(inv[0,0]*inv[3,3]))
    assert sp.simplify(side_sq-s/(8*(3-s)))==0
    det_flat=det.subs(s,sp.Rational(5,2))
    assert det_flat==sp.Rational(5,64)
    return {'symbolic_4simplex_gramdet':str(det),
            'flat_det':str(det_flat),
            'cos_inner': '(s-2)/(2*(s-3))',
            'cos_base': '1-3*s/4',
            'cos_side_sq': 's/(8*(3-s))',
            'status':'PASS'}


def high_precision():
    probes=['1.05','1.23','1.41421356237309504880168872420969807856967187537695',
            '1.51', '1.5811388300841896659994467722163592668597775696626','1.62']
    max_delta=mp.mpf('0')
    for y in probes:
        x=mp.mpf(y)
        a=complete_action(x)
        b=grouped_action(x)
        max_delta=max(max_delta,abs(a-b))
        assert abs(a-b)<mp.mpf('1e-60'),(x,a,b)
        finite=mp.diff(complete_action,x)
        s=x*x
        d=2*mp.pi-3*mp.acos((s-2)/(2*(s-3)))
        da=(2-s)/(2*mp.sqrt(4-s))
        direct=4*da*d
        assert abs(finite-direct)<mp.mpf('1e-58'),(x,finite,direct)

    flat=mp.sqrt(mp.mpf(5)/2)
    saddle=mp.sqrt(2)
    hflat=mp.diff(complete_action,flat,2)
    hsad=mp.diff(complete_action,saddle,2)
    assert abs(hflat-8*mp.sqrt(5))<mp.mpf('1e-52'), hflat
    assert abs(hsad+2*mp.pi)<mp.mpf('1e-52'),hsad
    deltad=mp.diff(lambda x:2*mp.pi-3*mp.acos((x*x-2)/(2*(x*x-3))),flat)
    assert abs(deltad+4*mp.sqrt(30))<mp.mpf('1e-52')
    return {'action_equivalence_max':mp.nstr(max_delta,12),
            'flat_hessian':mp.nstr(hflat,48),'flat_expected':'8sqrt(5)',
            'saddle_hessian':mp.nstr(hsad,48),'saddle_expected':'-2pi',
            'flat_deficit_slope':mp.nstr(deltad,48),
            'differentiated_full_simplicial_action':True,
            'probes':len(probes),'digits':75,'status':'PASS'}


def main():
    result={'symbolic':exact_sympy(),'independent_high_precision':high_precision(),
            'scope':'4D Euclidean Regge action with fixed boundary; no Lorentzian propagation'}
    (ROOT/'independent_audit_v32.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps(result,ensure_ascii=False,indent=2))

if __name__=='__main__':main()
