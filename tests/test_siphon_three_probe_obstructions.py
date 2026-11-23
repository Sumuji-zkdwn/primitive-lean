"""Exact rational/dual-number regression for E-L observation obstructions.

Topological proofs are in the companion note; finite tests do not prove them.
"""
from fractions import Fraction as Q
from itertools import product, combinations
from collections import Counter
import unittest

def E(z):
    u,v=z
    r=v+u**3
    U=u+r**2
    return U,r-U**3

def L(z):
    u,v=z
    return v,v-u

def first(word,z):
    for op in word:
        z= E(z) if op=='E' else L(z)
    return z[0]

def p(x): return Q(1)/(1+9*x**4)

def three_square(z):
    return (z[0]**2,first('E',z)**2,first('LELL',z)**2)

def mirror_pair(u,r):
    return (u,r-u**3),(u,-r-u**3)

def pair_sum(u,r):
    z,w=mirror_pair(u,r)
    return first('LELL',z)+first('LELL',w)

def four_minor_values(u,v):
    r=v+u**3
    U=u+r**2
    t=v-u+v**3
    V=v+t**2
    return (
        4*u*v,
        8*u*r*U,
        4*v*U*(1+6*u**2*r),
        4*u*V*(1+2*t*(1+3*v**2)),
    )

class Dual:
    """Exact two-variable first derivatives."""
    def __init__(self,x,du=0,dv=0):
        self.x,self.du,self.dv=Q(x),Q(du),Q(dv)
    def __add__(self,b):
        if not isinstance(b,Dual): b=Dual(b)
        return Dual(self.x+b.x,self.du+b.du,self.dv+b.dv)
    __radd__=__add__
    def __neg__(self): return Dual(-self.x,-self.du,-self.dv)
    def __sub__(self,b): return self+-b if isinstance(b,Dual) else self+Dual(-b)
    def __rsub__(self,b): return Dual(b)+-self
    def __mul__(self,b):
        if not isinstance(b,Dual): b=Dual(b)
        return Dual(self.x*b.x,self.du*b.x+self.x*b.du,self.dv*b.x+self.x*b.dv)
    __rmul__=__mul__
    def __pow__(self,n):
        assert isinstance(n,int) and n>=0
        if n==0:return Dual(1)
        return Dual(self.x**n,n*self.x**(n-1)*self.du,n*self.x**(n-1)*self.dv)

def exact_jacobian_four(u,v):
    z=(Dual(u,1,0),Dual(v,0,1))
    ze=E(z); zl=L(z); zel=E(zl)
    outputs=(z[0]**2,ze[0]**2,z[1]**2,zel[0]**2)
    rows=[(a.du,a.dv) for a in outputs]
    def det(i,j): return rows[i][0]*rows[j][1]-rows[i][1]*rows[j][0]
    return det(0,2),det(0,1),det(1,2),det(0,3)

class ThreeProbeObstructions(unittest.TestCase):
    def test_linear_directions_of_words(self):
        # Every E has identity differential at origin; L has order six.
        for k in range(5):
            for w in product('EL',repeat=k):
                q=first(w,(Dual(0,1),Dual(0,0,1)))
                residue=sum(c=='L' for c in w)%6
                expected=((1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1))[residue]
                self.assertEqual((q.du,q.dv),expected)

    def test_many_finite_grids_misleadingly_separate(self):
        for size,den in ((3,1),(6,2),(10,2),(14,2)):
            vals=[Q(k,den) for k in range(-size,size+1)]
            states=list(product(vals,repeat=2))
            self.assertEqual(len({three_square(z) for z in states}),len(states))

    def test_bounded_word_triples_general_obstruction_counts(self):
        words=[()] + [w for k in range(1,5) for w in product('EL',repeat=k)]
        pure={tuple('E'*k) for k in range(5)}
        states=list(product(range(-2,3),repeat=2))
        data={w: tuple(first(w,z)**2 for z in states) for w in words}
        counts=Counter()
        grid_unique=Counter()
        for tri in combinations(words,3):
            residues={sum(a=='L' for a in w)%3 for w in tri}
            if len(residues)>1:
                category='mixed'
            elif sum(w in pure for w in tri)>=2:
                category='twoE'
            else:
                category='remaining'
            counts[category]+=1
            if len(set(zip(*(data[w] for w in tri))))==25:
                grid_unique[category]+=1
        self.assertEqual(dict(counts),{'mixed':4090,'twoE':60,'remaining':345})
        self.assertEqual(dict(grid_unique),{'mixed':3394,'twoE':20,'remaining':304})

    def test_exact_ivr_bracket_for_real_collision(self):
        r=Q(1,100)
        self.assertGreater(pair_sum(Q(-1,1000),r),0)
        self.assertLess(pair_sum(Q(0),r),0)
        for u in (Q(-1,1000),Q(0),Q(-1,10000)):
            z,w=mirror_pair(u,r)
            self.assertEqual(z[0]**2,w[0]**2)
            self.assertEqual(first('E',z)**2,first('E',w)**2)

    def test_four_minor_formulas_by_exact_dual_numbers(self):
        vals=[Q(i,3) for i in range(-6,7)]
        for u,v in product(vals,repeat=2):
            self.assertEqual(four_minor_values(u,v),exact_jacobian_four(u,v))

    def test_four_read_rank_two_except_origin_on_grid(self):
        vals=[Q(i,3) for i in range(-12,13)]
        for u,v in product(vals,repeat=2):
            self.assertEqual(any(m!=0 for m in four_minor_values(u,v)),(u,v)!=(0,0))

    def test_probability_equivalence(self):
        vals=[Q(i,5) for i in range(-15,16)]
        for x,y in product(vals,repeat=2):
            self.assertEqual(p(x)==p(y),x*x==y*y)

if __name__=='__main__':
    unittest.main()
