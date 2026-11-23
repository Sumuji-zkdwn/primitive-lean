#!/usr/bin/env python3
"""Stage 32: independent finite 4D Euclidean Regge 2->4 geometry and memory test.

One new interior edge EF. No propagating spin-2 or Lorentzian constraints are claimed.
The 4D Regge action, its boundary term, and the curvature-memory potential
are deliberately supplied by known/auxiliary variational laws.
"""
from __future__ import annotations

from collections import Counter
from fractions import Fraction as Q
from itertools import combinations
from math import acos, cos, pi, sqrt, isclose
from pathlib import Path
import csv
import json

A, B, C, D, E, F = range(6)
BEFORE = [(A, B, C, D, E), (A, B, C, D, F)]
AFTER = [(A, B, C, E, F), (A, B, D, E, F),
         (A, C, D, E, F), (B, C, D, E, F)]
ROOT = Path(__file__).resolve().parent


def incidence(simplices):
    """All vertices are abstract; no embedding is assumed."""
    edges = {p for s in simplices for p in combinations(sorted(s), 2)}
    tetra = Counter(q for s in simplices for q in combinations(sorted(s), 4))
    bdy = {q for q, n in tetra.items() if n == 1}
    inner_tet = {q for q, n in tetra.items() if n == 2}
    assert all(n in (1, 2) for n in tetra.values())
    triangles = {q for s in simplices for q in combinations(sorted(s), 3)}
    btri = {q for f in bdy for q in combinations(f, 3)}
    return edges, bdy, inner_tet, triangles - btri, btri, triangles


def gram(s):
    """Exact 4x4 Gram matrix at E with rays to F,A,B,C."""
    return [[Q(s), Q(s, 2), Q(s, 2), Q(s, 2)],
            [Q(s, 2), Q(1), Q(1, 2), Q(1, 2)],
            [Q(s, 2), Q(1, 2), Q(1), Q(1, 2)],
            [Q(s, 2), Q(1, 2), Q(1, 2), Q(1)]]


def gram_minors(s):
    return (s, s * (4 - s) / 4, s * (3 - s) / 4,
            s * (8 - 3*s) / 16)


def cosine_inner(s):
    return (s - 2) / (2 * (s - 3))


def cosine_base(s):
    return 1 - 3*s / 4


def cosine_side_sq(s):
    return s / (8 * (3 - s))


def angle_deficit(x):
    s = x*x
    if not (0 < s < 8/3):
        raise ValueError('each four-simplex requires 0 < x^2 < 8/3')
    return 2*pi - 3*acos(cosine_inner(s))


def angle_deficit_prime(x):
    s = x*x
    if not (0 < s < 8/3):
        raise ValueError('nondegenerate simplex interval required')
    c = cosine_inner(s)
    # d(cos(theta))/ds = -1/[2(s-3)^2]
    return -3*x/((s-3)**2*sqrt(1-c*c))


def triangle_area(x):
    if not 0 < x*x < 8/3:
        raise ValueError('nondegenerate simplex interval required')
    return x*sqrt(4-x*x)/4


def triangle_area_prime(x):
    return (2-x*x)/(2*sqrt(4-x*x))


def reduced_action(x):
    """Full 4D Euclidean Regge action, including Gibbons-Hawking Regge boundary term.

    Four internal hinges: (E,F,v) for v in A..D, each with 3 incident simplices.
    Four boundary hinges of three base vertices, one angle per hinge.
    Twelve boundary hinges of E or F plus two base vertices, two angles each.
    All boundary triangles are equilateral with area sqrt(3)/4.
    """
    s=x*x
    d=angle_deficit(x)
    abase=sqrt(3)/4
    theta_base=acos(cosine_base(s))
    theta_side=acos(sqrt(cosine_side_sq(s)))
    return 4*triangle_area(x)*d + 4*abase*(pi-theta_base) + 12*abase*(pi-2*theta_side)


def regge_gradient(x):
    """Schlaefli-reduced Regge equation (with fixed boundary edge lengths)."""
    return 4*angle_deficit(x)*triangle_area_prime(x)


def exact_checks():
    pre=incidence(BEFORE)
    post=incidence(AFTER)
    assert len(pre[0])==14 and len(post[0])==15
    assert post[0]-pre[0]=={(E,F)} and not pre[0]-post[0]
    assert pre[1]==post[1] and len(pre[1])==8
    assert len(pre[2])==1 and len(post[2])==6
    assert pre[3]==set() and post[3]=={(i,E,F) for i in (A,B,C,D)}
    assert len(pre[4])==len(post[4])==16
    assert len(pre[5])==16 and len(post[5])==20
    for s in [Q(1), Q(2), Q(5,2), Q(8,3)-Q(1,50), Q(1,3)]:
        assert all(v>0 for v in gram_minors(s))
    assert cosine_inner(Q(1))==Q(1,4)
    assert cosine_inner(Q(2))==Q(0)
    assert cosine_inner(Q(5,2))==-Q(1,2)
    assert cosine_base(Q(1))==Q(1,4)
    assert cosine_base(Q(5,2))==-Q(7,8)
    assert cosine_side_sq(Q(1))==Q(1,16)
    assert cosine_side_sq(Q(5,2))==Q(5,8)
    for s in [Q(1),Q(4,3),Q(2),Q(5,2)]:
        for t in [Q(1),Q(7,4),Q(5,2),Q(8,3)-Q(1,20)]:
            assert cosine_inner(s)-cosine_inner(t)==(t-s)/(2*(s-3)*(t-3))
    # Exact stationary factors: delta(x) and A'(x), not one or the other.
    assert abs(angle_deficit(sqrt(5/2)))<1e-14
    assert abs(angle_deficit(sqrt(2))-pi/2)<1e-14
    assert abs(triangle_area_prime(sqrt(2)))<1e-15
    assert abs(angle_deficit_prime(sqrt(5/2))+4*sqrt(30))<1e-12
    assert isclose(gram_minors(Q(5,2))[-1],Q(5,64), rel_tol=0,abs_tol=0)
    return {'simplices_before':2,'simplices_after':4,'edges_before':14,
            'edges_after':15,'new_internal_edge':'EF','boundary_tetrahedra':8,
            'internal_tetra_before':1,'internal_tetra_after':6,
            'interior_triangles_before':0,'interior_triangles_after':4,
            'boundary_triangles':16,'flat_squared_edge':'5/2',
            'nonflat_stationary_squared_edge':'2',
            'flat_deficit_slope':'-4 sqrt(30)','regge_flat_Hessian':'8 sqrt(5)',
            'regge_curved_stationary_Hessian':'-2 pi'}


def finite_difference(f, x, h):
    return (f(x+h)-f(x-h))/(2*h)


def numerical_checks():
    samples=[1.0,1.15,1.25,1.35,sqrt(2),1.5,sqrt(5/2),1.6]
    max_schlafli=0.;rows=[]
    for x in samples:
        # Difference of independently evaluated full Regge action and Schlaefli formula.
        # h=1e-5, cancellation limited to ~1e-9.
        direct=finite_difference(reduced_action,x,2e-5)
        schl=regge_gradient(x)
        error=abs(direct-schl); max_schlafli=max(max_schlafli,error)
        rows.append({'x':x,'s':x*x,'deficit':angle_deficit(x),
                     'regge_action':reduced_action(x),'numerical_action_gradient':direct,
                     'schlaefli_gradient':schl,'gradient_error':error})
    assert max_schlafli<5e-7,max_schlafli
    xflat=sqrt(5/2); xcurved=sqrt(2)
    h=1e-4
    def hessian(x):return (reduced_action(x+h)-2*reduced_action(x)+reduced_action(x-h))/h**2
    assert abs(hessian(xflat)-8*sqrt(5))<5e-5,(hessian(xflat),8*sqrt(5))
    assert abs(hessian(xcurved)+2*pi)<5e-5,(hessian(xcurved),-2*pi)
    assert abs(regge_gradient(xcurved))<1e-12
    assert abs(regge_gradient(xflat))<1e-12
    with (ROOT/'regge_action_scan_v32.csv').open('w',newline='',encoding='utf8') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
    return {'max_action_gradient_disagreement':max_schlafli,
            'flat_x':xflat,'curved_saddle_x':xcurved,
            'flat_regge_Hessian_fd':hessian(xflat),
            'curved_regge_Hessian_fd':hessian(xcurved),
            'curved_deficit':angle_deficit(xcurved),
            'full_action_at_flat':reduced_action(xflat)}


def effective_memory_critical(kappa,mu):
    """Minimize algebraically over m to get eta*delta^2/2 added to Regge.

    Does not assert 4D Lorentzian time evolution. Searches one nonflat
    critical point 0 < x < sqrt(2) for positive eta and classifies it.
    """
    eta=kappa*mu/(kappa+mu) if kappa+mu>0 else 0
    def force_factor(x): return 4*triangle_area_prime(x)+eta*angle_deficit_prime(x)
    if eta==0: xs=sqrt(2)
    else:
        lo,hi=1e-9,sqrt(2)
        assert force_factor(lo)>0 and force_factor(hi)<0
        for _ in range(80):
            mid=(lo+hi)/2
            if force_factor(mid)>0: lo=mid
            else: hi=mid
        xs=(lo+hi)/2
    def e_eff(x):return reduced_action(x)+eta*angle_deficit(x)**2/2
    h=1e-4
    curv=(e_eff(xs+h)-2*e_eff(xs)+e_eff(xs-h))/h**2
    m_eq=kappa*angle_deficit(xs)/(kappa+mu) if kappa+mu else 0
    assert angle_deficit(xs)>0 and curv<0, (xs,curv)
    assert abs(finite_difference(e_eff,xs,1e-5))<1e-6
    return {'kappa':kappa,'mu':mu,'eta':eta,'nonflat_x':xs,
            'nonflat_squared_edge':xs*xs,'deficit':angle_deficit(xs),
            'memory_at_critical':m_eq,'reduced_Hessian':curv,
            'stable':False}


def main():
    exact=exact_checks()
    finite=numerical_checks()
    memory=[effective_memory_critical(k,.5) for k in (0,.02,.1,.3,1,3)]
    memory.append(effective_memory_critical(10,10))
    memory.append(effective_memory_critical(100,100))
    with (ROOT/'memory_stationary_scan_v32.csv').open('w',newline='',encoding='utf8') as f:
        w=csv.DictWriter(f,fieldnames=list(memory[0]));w.writeheader();w.writerows(memory)
    result={'status':'PASS','scope':'4D Euclidean 2-4 Pachner patch, fixed boundary; no Lorentzian propagation',
            'exact':exact,'finite_difference':finite,'curvature_memory':memory}
    (ROOT/'audit_v32.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n',encoding='utf8')
    print(json.dumps(result,indent=2,ensure_ascii=False))
    return result

if __name__=='__main__': main()
