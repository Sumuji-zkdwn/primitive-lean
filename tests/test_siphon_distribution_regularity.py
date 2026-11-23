"""Exact rational probes for tangent-distribution observability regularity.

These checks support, but cannot replace, the real-domain proof in the note.
No external dependencies; existing E and L model definitions are unchanged.
"""
from fractions import Fraction
from itertools import product, combinations
import unittest

def E(z):
    u,v=z
    r=v+u**3
    U=u+r**2
    return U, r-U**3

def L(z):
    u,v=z
    return v,v-u

def p(u):
    return 1/(1+9*u**4)

def dp(u):
    return -36*u**3/(1+9*u**4)**2

def observations(z):
    return p(z[0]),p(E(z)[0]),p(E(E(z))[0]),p(L(z)[0]),p(E(L(z))[0])

def determinant_first_three(u,r,n,m):
    return 2*r*(m-n)*dp(u+n*r**2)*dp(u+m*r**2)

def determinant_at_zero_fibre(u):
    return dp(u)*dp(-u**3)

def run_word(z, word):
    for op in word:
        z=E(z) if op=='E' else L(z)
    return z

class SiphonDistributionRegularity(unittest.TestCase):
    def test_full_rank_except_origin_on_rational_grid(self):
        vals=[Fraction(k,2) for k in range(-6,7)]
        checked=0
        for u,r in product(vals,repeat=2):
            if r:
                minors=[determinant_first_three(u,r,n,m) for n,m in combinations(range(3),2)]
                self.assertTrue(any(minor for minor in minors),(u,r))
            elif u:
                self.assertNotEqual(determinant_at_zero_fibre(u),0)
            else:
                self.assertEqual(dp(u),0)
            checked+=1
        self.assertEqual(checked,169)

    def test_probability_quartic_identity(self):
        for u in [Fraction(k,8) for k in range(-40,41)]:
            self.assertEqual(1-p(u),9*u**4/(1+9*u**4))
            self.assertTrue(0<=1-p(u)<=9*u**4)

    def test_every_short_word_fixes_origin(self):
        words=[()] + [tuple(w) for k in range(1,6) for w in product(('E','L'),repeat=k)]
        for w in words:
            self.assertEqual(run_word((Fraction(0),Fraction(0)),w),(0,0))
            self.assertEqual(p(run_word((Fraction(0),Fraction(0)),w)[0]),1)
        self.assertEqual(len(words),63)

    def test_specific_pair_first_four_equal(self):
        for t in [Fraction(1,100),Fraction(1,2),Fraction(1),Fraction(2),Fraction(10)]:
            z,w=(t,-t**3),(-t,t**3)
            oz,ow=observations(z),observations(w)
            self.assertEqual(oz[:4],ow[:4])
            self.assertNotEqual(oz[4],ow[4])
            self.assertGreater(oz[4]-ow[4],0)

    def test_fourth_order_bound_for_short_words_near_zero(self):
        words=[tuple(w) for k in range(5) for w in product(('E','L'),repeat=k)]
        for word in words:
            ratios=[]
            for t in [Fraction(1,256),Fraction(1,512)]:
                x=run_word((t,t),word)[0]
                ratios.append((1-p(x))/t**4)
            self.assertLess(ratios[1],100*(1+ratios[0]))

if __name__=='__main__':
    unittest.main()
