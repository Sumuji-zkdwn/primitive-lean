"""Local curvature-probability reconstruction tests.

Paper proof is in docs/research/2026-11-23-curvature-observation-repair.md.
Finite tests are independent arithmetic checks, not a Lean proof.
"""
from fractions import Fraction
from itertools import product
import unittest

def q(u):
    # q(u) = 1/2 + signed_curvature(u)/12
    return .5-u/(2*(1+9*u**4)**1.5)

def qprime(u):
    return (45*u**4-1)/(2*(1+9*u**4)**2.5)

def qjet(u):
    # Rational second-jet surrogate, not the same as curvature.
    return Fraction(1,2)+u/(2*(1+u*u))

class CurvatureSensor(unittest.TestCase):
    def test_global_probability_range(self):
        for k in range(-100,101):
            self.assertTrue(0<q(k/4)<1)

    def test_explicit_local_derivative_bounds(self):
        for k in range(-100,101):
            u=Fraction(k,400)
            lower=(1-45*u**4)/(2*(1+9*u**4)**3)
            self.assertGreater(lower,Fraction(1,3))
            self.assertGreaterEqual(-qprime(float(u)),1/3-1e-13)
            self.assertLessEqual(-qprime(float(u)),1/2+1e-13)

    def test_two_curvature_probabilities_are_patch_bilipschitz(self):
        vals=[k/40 for k in range(-10,11)]
        for x,y in product(vals,repeat=2):
            if x==y: continue
            ratio=abs(q(x)-q(y))/abs(x-y)
            self.assertGreaterEqual(ratio,1/3-1e-12)
            self.assertLessEqual(ratio,1/2+1e-12)

    def test_rational_second_jet_surrogate_has_nondegenerate_origin(self):
        self.assertEqual(qjet(Fraction(0)),Fraction(1,2))
        t=Fraction(1,1000)
        self.assertEqual((qjet(t)-qjet(Fraction(0)))/t,Fraction(1,2)/(1+t*t))

if __name__=='__main__':
    unittest.main()
