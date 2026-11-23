"""Independent exact rational checks for four probability reads of E and L.

The global theorem is proved in the companion research note. Finite checks
cannot establish global real injectivity or minimality.
"""
import unittest
from fractions import Fraction as F
from itertools import product

def E(z):
    u,v=z
    r=v+u**3
    U=u+r**2
    return (U,r-U**3)

def L(z):
    u,v=z
    return v,v-u

def squares(z):
    u,v=z
    return (u*u,E(z)[0]**2,v*v,E(L(z))[0]**2)

def prob(z):
    return F(1,1)/(1+9*z[0]**4)

def four_prob(z):
    return (prob(z),prob(E(z)),prob(L(z)),prob(E(L(z))))

def B(u,v):
    return (u+(v+u**3)**2)**2

def D(u,v):
    return (v+(v-u+v**3)**2)**2

def three_diff(u,r):
    v=r-u**3
    w=-r-u**3
    return D(u,v)-D(u,w)

class FourReadRegression(unittest.TestCase):
    def test_exact_full_grid_injection(self):
        for bound,den in ((3,1),(6,2),(10,2),(14,2)):
            vals=[F(i,den) for i in range(-bound,bound+1)]
            states=list(product(vals,repeat=2))
            self.assertEqual(len({squares(z) for z in states}),len(states))
            self.assertEqual(len({four_prob(z) for z in states}),len(states))

    def test_squared_reads_equivalent_to_probabilities(self):
        for n in range(-30,31):
            a=F(n,10)
            self.assertEqual(prob((a,0)),F(1,1)/(1+9*(a*a)**2))

    def test_difference_factors(self):
        vals=[F(i,3) for i in range(-7,8)]
        for u,v in product(vals,repeat=2):
            r=v+u**3
            t=v-u+v**3
            self.assertEqual(B(u,v)-B(-u,-v),4*u*r*r)
            self.assertEqual(D(u,v)-D(-u,-v),4*v*t*t)
            self.assertEqual(B(u,v)-B(-u,v),4*u*(u**6+v*v)*(1+2*u*u*v))
            self.assertEqual(D(u,v)-D(-u,v),
                             -8*u*v*(1+v*v)*(u*u+v+(v+v**3)**2))
            self.assertEqual(B(u,v)-B(u,-v),8*u**3*v*(u**6+u+v*v))
            self.assertEqual(D(u,v)-D(u,-v),
                             -4*v*(2*u*(1+v*v)-1)*(u*u+(v+v**3)**2))

    def test_positive_sos_polynomial(self):
        for i in range(1,400):
            a=F(i,100)
            lhs=4*a**3-2*a+1
            rhs=(2*a-1)**2+2*a*((a-1)**2+a*a)
            self.assertEqual(lhs,rhs)
            self.assertGreater(rhs,0)

    def test_three_probe_counterexamples(self):
        for u in (F(1),F(1,3),F(2)):
            z,w=(u,-u**3),(-u,u**3)
            a,b=squares(z),squares(w)
            self.assertEqual((a[0],a[1],a[2]),(b[0],b[1],b[2]))
            z,w=(u,F(0)),(-u,F(0))
            a,b=squares(z),squares(w)
            self.assertEqual((a[0],a[2],a[3]),(b[0],b[2],b[3]))
        u=F(1,4)
        self.assertGreater(three_diff(u,F(3,4)),0)
        self.assertLess(three_diff(u,F(1)),0)
        # The first 2 observables agree for r and -r identically.
        for r in (F(3,4),F(1)):
            z,w=(u,r-u**3),(u,-r-u**3)
            self.assertEqual(squares(z)[:2],squares(w)[:2])

if __name__=="__main__":
    unittest.main()
