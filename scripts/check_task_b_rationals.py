#!/usr/bin/env python3
"""Independent exact-rational diagnostics; not a substitute for the Lean proofs.

Scale out C=4/(2+pi)^2, so the pointwise and tail checks need no floating-point pi.
Check rational parameters num/den with 2 <= den <= 20 and 0 < num < den,
including repeated representations, plus named and near-endpoint examples.
The omitted normalized tail uses the analytic bound 4/(3*(N-1)^2) from the
cubic integral test; the script checks the resulting finite enclosures, not
the integral-test theorem itself or all real parameters. Run with ordinary
Python (without -O, which disables the assertions).
"""
from fractions import Fraction as F


def check(a, nmax=32):
    s = a * (1-a)
    h = (a+1)/(a*(a+2)) + (2-a)/((1-a)*(3-a))
    r = a/(1-a*a) + (1-a)/(a*(2-a))
    assert h == 3*(s+1)/(s*(s+6))
    assert r == (1-s)/(s*(s+2))
    assert r-h == (-4*s-14)/(s*s+8*s+12)
    assert r-h+F(7,6) == s*(7*s+32)/(6*(s*s+8*s+12))
    assert r-F(4,3) == (1-4*s)*(s+3)/(3*s*(s+2))
    assert r-h >= -F(7,6) and r >= F(4,3)
    assert 75*r-12*h >= 70
    assert F(4,25)*h+F(32,75) < r
    b = (1+max(a,1-a))/2
    negative_head_reciprocals = a/(b*b-a*a)+(1-a)/(b*b-(1-a)**2)
    assert r < negative_head_reciprocals
    tail = F(0)
    checked = 0
    for ell in range(-nmax,nmax+1):
        if ell in (-2,-1,0,1):
            continue
        x = abs(ell+a)
        y = abs(ell)-1
        sigma = (x*x-1)/x
        finite_sigma = (x*x-b*b)/x
        coefficient_den = ell+1 if ell % 2 == 0 else ell
        weight = F(1,coefficient_den**2)
        assert 2 <= x and 0 < y <= x
        assert F(3,4)*x <= sigma < finite_sigma
        assert weight <= F(1,y*y)
        assert weight/sigma <= 4*weight/(3*x) <= 4*weight/(3*y) <= F(4,3*y**3)
        tail += weight/sigma
        checked += 1
    assert tail + F(4,3*(nmax-1)**2) < F(8,3)
    return h, r, checked


if __name__ == '__main__':
    cases = 0
    terms = 0
    for den in range(2,21):
        for num in range(1,den):
            _, _, checked = check(F(num,den))
            cases += 1
            terms += checked
    for a, expected in [(F(1,2),(F(12,5),F(4,3))),
                        (F(1,4),(F(304,99),F(208,105))),
                        (F(3,4),(F(304,99),F(208,105)))]:
        h,r,_ = check(a)
        assert (h,r) == expected
    check(F(1,100),100)
    check(F(99,100),100)
    assert F(1,8) < F(3,8)
    print(f'PASS: {cases} rational parameter cases, {terms} pointwise comparisons, '
          'named examples and near-endpoint tail enclosures; no floating-point arithmetic.')
