"""Exact Fraction checks for ternary cell observations; NOT a PI proof."""
from fractions import Fraction as F

J = F(47, 52)

def overlap(x, lo, hi):
    return max(F(0), min(x, hi) - lo)

def deficit_tail(n):
    q = F(1, 3**n)
    return q/2 - 3*q*q/4 + 9*q*q*q/26

def good_phi(s):
    return (F(89,104)*min(s, F(2,3)) + max(F(0), s-F(2,3))) / J

def bad_phi(s, depth):
    if s == 0:
        return F(0)
    total = deficit_tail(depth+1)
    for n in range(1,depth+1):
        eps = F(1,3**n)
        ell = eps/3
        center = 3*eps/2
        sl, sr = center-eps*ell/2, center+eps*ell/2
        il, ir = eps+ell, eps+2*ell
        total += (1-eps)*(overlap(s,il,sl)+overlap(s,sr,ir))
    return (s-total)/J

def power2_phi(s):
    x = 2*s - 1
    return (1 + (x*x if x >= 0 else -x*x))/2

def delta(phi, k, j):
    h = F(1,3**k)
    return phi((j+1)*h) - phi(j*h)

def main():
    assert deficit_tail(1) == F(5,52)
    good = delta(good_phi,1,0)
    bad = delta(lambda s:bad_phi(s,1),1,0)
    assert good == F(89,282)
    assert bad == F(1207,3807)
    assert bad-good == F(11,7614)
    print("level-one located cell:",good,bad,bad-good)
    assert F(89,104)/J == F(89,94)
    for n in range(1,9):
        eps = F(1,3**n)
        mean_slope = (2*eps-eps*eps)/J
        assert mean_slope > 0
        print("bad neck cell:",n+1,mean_slope)
    for k in range(1,8):
        h = F(1,3**k)
        j = (3**k-1)//2
        central_length = delta(power2_phi,k,j)
        assert central_length == h*h
        assert central_length/h == h
        print("PI power gauge central slope:",k,h)
    print("PASS: position-sensitive distinctions, no general PI inference")

if __name__ == "__main__":
    main()
