"""Exact Fraction checks for a doubling-but-not-PI ternary-gate model.

Finite/algebraic verification only: doubling and continuum PI claims have
separate paper proofs in 2026-11-23-laakso-doubling-pi-separation.md.
"""
from fractions import Fraction as Q

C, L = Q(4, 5), Q(5, 4)

def z(n):
    return Q(1, 6**n)

def s(n):
    return Q(1, 3**n)

def ell(n):
    return z(n) - z(n + 1)

def H(n):
    return Q(8, 5) * (2**n - 1)

def F(x):
    x = Q(x)
    assert 0 <= x <= 1
    if x == 0:
        return Q(0)
    if x >= z(1):
        return s(1) + C*(x-z(1))
    n = 1
    while not z(n+1) <= x <= z(n):
        n += 1
    t, h = x-z(n+1), ell(n)
    triangular_integral = t*t/h if 2*t <= h else h/2-(h-t)*(h-t)/h
    return s(n+1) + C*t + H(n)*triangular_integral

def good(x):
    x = Q(x)
    return x/2 if x <= s(1) else z(1)+L*(x-s(1))

def jump(n, side, t):
    assert n >= 2 and 0 <= t <= ell(n)/2
    width = ell(n) if side == '-' else ell(n-1)
    height = H(n) if side == '-' else H(n-1)
    value = s(n)-F(z(n)-t) if side == '-' else F(z(n)+t)-s(n)
    assert value == C*t+height*t*t/width
    return value

def exact_ramp_mean(n):
    """Mean rho on the symmetric z_n ± z_n/4^n strip, exactly rational."""
    assert n >= 1
    return Q(4, 5) + (26*Q(2)**n-28)/(25*Q(4)**n)


def test():
    assert F(1) == 1 and F(z(1)) == s(1)
    for n in range(1, 27):
        delta = z(n) / 4**n
        computed = (F(z(n)+delta)-F(z(n)-delta))/(2*delta)
        assert computed == exact_ramp_mean(n)
        assert Q(4, 5) < computed <= Q(26, 25)
    print("PASS: exact symmetric-ramp mean <= 26/25 for depths 1..26")
    assert good(1) == 1 and good(s(1)) == z(1)
    for n in range(1, 18):
        assert F(z(n)) == s(n)
        assert F(z(n))-F(z(n+1)) == Q(2,3)*s(n)
        assert F(z(n)) == s(n)  # actual ternary gate: j=1
        for k in range(1,7):
            h=Q(1,3**k)
            assert F(1)-F(1-L*h) == h
            assert good(1)-good(1-h) == L*h
        if n>=3:
            delta=z(n)/4**n
            energy=(F(z(n)+delta)-F(z(n)-delta))/(2*delta)
            assert C < energy < 3
    print('PASS: all shell masses and aligned ternary gates; exact end-interval witness')
    for lam in (1,2,4,10):
        kap=Q(1,16*lam)
        K=0
        while Q(1,3**K)>kap*kap/400:
            K+=1
        for n in range(max(12,5+K),27):
            r=kap*z(n)
            assert z(n)/4**n < r/6
            assert jump(n,'-',r)+jump(n,'+',r) <=4*kap*kap*s(n)
            assert jump(n,'-',lam*r)+jump(n,'+',lam*r) < s(n)/20
            for side in ('-','+'):
                strip=jump(n,side,r/3)-jump(n,side,r/6)
                assert strip >= kap*kap*s(n)/100
                assert strip >=4*s(n+K)
            assert r/s(n)==kap*Q(1,2**n)
        print('lambda',lam,'fixed extra depth K',K)
    # 1-D doubling ratios at sampled centres; diagnostic only.
    largest=Q(0)
    for n in range(2,11):
        for x in (z(n),z(n)-ell(n)/12,z(n)+ell(n)/12,z(n+1)+ell(n)/2):
            for denom in (2,5,10,20,50,100,250):
                r=z(n)/denom
                small=F(min(Q(1),x+r))-F(max(Q(0),x-r))
                big=F(min(Q(1),x+2*r))-F(max(Q(0),x-2*r))
                largest=max(largest,big/small)
    print('sampled 1D doubling ratio (NOT a proof):',float(largest))
    print('PASS: all exact rational checks; paper proof still required for continuum')

if __name__ == '__main__':
    test()
