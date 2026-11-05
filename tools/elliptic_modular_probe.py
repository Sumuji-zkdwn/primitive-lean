"""Exact, finite observation probe for the classical level-11 modular elliptic curve.

Curve: y^2 + y = x^3 - x^2 - 10*x - 20 (11a1).
Form:  eta(tau)^2 * eta(11*tau)^2
      = q * product_{n>=1} (1-q^n)^2 (1-q^(11n))^2.

The two sides are computed independently with integer arithmetic. This finite
check is NOT a proof of modularity, or a claim about other elliptic curves.
"""
from math import gcd, isqrt


def is_prime(n: int) -> bool:
    return n >= 2 and all(n % d != 0 for d in range(2, isqrt(n) + 1))


def eta_coefficients(degree: int) -> list[int]:
    """Coefficients a[0]..a[degree] from a truncated integral q-product."""
    if degree < 1:
        raise ValueError("degree must be positive")
    coeff = [0] * (degree + 1)
    coeff[1] = 1
    for n in range(1, degree + 1):
        for exponent in (n, 11 * n):
            if exponent > degree:
                continue
            for _ in range(2):  # multiply twice by (1 - q^exponent)
                for k in range(degree, exponent - 1, -1):
                    coeff[k] -= coeff[k - exponent]
    return coeff


def points_on_curve(p: int, constant: int = 20) -> int:
    """Number of projective F_p-points on y^2+y=x^3-x^2-10x-constant."""
    if not is_prime(p):
        raise ValueError("p must be prime")
    square_counts = [0] * p
    for y in range(p):
        square_counts[(y * y + y) % p] += 1
    # The point at infinity is counted once.
    return 1 + sum(
        square_counts[(x**3 - x**2 - 10 * x - constant) % p]
        for x in range(p)
    )


def observation_rows(max_prime: int = 97, degree: int = 200) -> list[dict[str, int]]:
    """Compare a_p=p+1-#E(F_p) with the modular q coefficient, p != 11."""
    if degree < max_prime:
        raise ValueError("degree must cover the largest tested prime")
    coeff = eta_coefficients(degree)
    return [
        {"p": p, "points": (n := points_on_curve(p)),
         "curve_a_p": p + 1 - n, "form_a_p": coeff[p]}
        for p in range(2, max_prime + 1) if is_prime(p) and p != 11
    ]


def hecke_failures(degree: int = 200) -> list[str]:
    """Check good-prime square relation and coprime-index multiplicativity."""
    a = eta_coefficients(degree)
    failures = []
    for p in range(2, isqrt(degree) + 1):
        if is_prime(p) and p != 11 and a[p * p] != a[p] ** 2 - p:
            failures.append(f"square: p={p}")
    for m in range(1, degree + 1):
        for n in range(1, degree // m + 1):
            if gcd(m, n) == 1 and a[m * n] != a[m] * a[n]:
                failures.append(f"coprime: m={m}, n={n}")
    return failures


if __name__ == "__main__":
    for row in observation_rows():
        print(f"p={row['p']:>2} points={row['points']:>3} "
              f"curve={row['curve_a_p']:>3} form={row['form_a_p']:>3}")
    rows = observation_rows()
    failures = hecke_failures()
    assert all(row["curve_a_p"] == row["form_a_p"] for row in rows)
    assert not failures, failures
    print(f"PASS: {len(rows)} good primes <= 97, Hecke checks to degree 200")
