"""Independent exact finite checks for rationally glued circle-clock layers.

Angles are represented by a + b*sqrt(2) mod Z, with a,b rational.
Because sqrt(2) is irrational, equality and rationality checks are exact.
This is a countable test subset, not a proof of all angles in R/Z.
"""
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
import unittest

@dataclass(frozen=True)
class Angle:
    a: Fraction = Fraction(0)
    b: Fraction = Fraction(0)

    def __post_init__(self):
        object.__setattr__(self, "a", Fraction(self.a) % 1)
        object.__setattr__(self, "b", Fraction(self.b))

    def __add__(self, other):
        return Angle(self.a + other.a, self.b + other.b)

    @property
    def rational(self):
        return self.b == 0


Point = tuple[Angle, bool]


def glued(x: Point, y: Point) -> bool:
    return x[0] == y[0] and (x[1] == y[1] or x[0].rational)


def rotate(delta: Angle, x: Point) -> Point:
    return (x[0] + delta, x[1])


def flip(x: Point) -> Point:
    return (x[0], not x[1])


class RationalClockChecks(unittest.TestCase):
    def test_setoid_laws_exhaustive_finite_family(self):
        angles = [Angle(a,b) for a,b in product(
            (Fraction(0),Fraction(1,3),Fraction(1,2)),
            (Fraction(0), Fraction(1)))]
        states = list(product(angles, (False,True)))
        for x in states:
            self.assertTrue(glued(x,x))
            for y in states:
                self.assertEqual(glued(x,y),glued(y,x))
                for z in states:
                    if glued(x,y) and glued(y,z):
                        self.assertTrue(glued(x,z))

    def test_rotation_descends_exactly_for_rational_shifts(self):
        angles = [Angle(a,b) for a,b in product(
            (Fraction(0),Fraction(1,3),Fraction(1,2)),
            (Fraction(0), Fraction(1)))]
        states = list(product(angles,(False,True)))
        shifts = [Angle(0,0),Angle(Fraction(1,3)),Angle(1),Angle(0,1),
                  Angle(Fraction(1,3),1)]
        for delta in shifts:
            respects = all(
                not glued(x,y) or glued(rotate(delta,x),rotate(delta,y))
                for x,y in product(states,repeat=2))
            self.assertEqual(respects,delta.rational)

    def test_full_revolution_and_hidden_layer(self):
        full=Angle(1)
        self.assertEqual(full,Angle(0))
        for a in (Angle(Fraction(1,3)),Angle(0,1)):
            self.assertEqual(a+full,a)
        origin_a,origin_b=(Angle(0),False),(Angle(0),True)
        self.assertTrue(glued(origin_a,origin_b))
        irrational=Angle(0,1)
        self.assertFalse(glued(rotate(irrational,origin_a),
                               rotate(irrational,origin_b)))

    def test_explicit_internal_switch_separated_from_rotation(self):
        for angle in (Angle(0),Angle(Fraction(1,3)),Angle(0,1)):
            point=(angle,False)
            full_rotated=rotate(Angle(1),point)
            self.assertEqual(full_rotated,point)
            switched=flip(full_rotated)
            self.assertEqual(glued(switched,point),angle.rational)
            self.assertEqual(flip(switched),point)
            self.assertEqual(angle,switched[0])


if __name__=="__main__":
    unittest.main(verbosity=2)
