#!/usr/bin/env python3
"""Standard-library exact guards for the odd Colombo Beta/split-knot ledger.

This is an index/constant/sign guard, not a proof of the arbitrary-rank
split-knot theorem.  It checks:

* the two Beta constants used in the Colombo and Volterra factorizations;
* the absence of an extra m! in the ordered de Bruijn formula (finite exact
  exterior-algebra model);
* the absence of an extra m! in separate antisymmetrization (finite exact
  model);
* the support implication used to preserve s_i < u_i;
* the Torelli-layer Pfaffian/Vandermonde sign and constant; and
* all parameter equivalences in the odd-branch status ledger.

No third-party package, floating point, Lean, or external service is used.
"""

from fractions import Fraction
from itertools import combinations, permutations, product
from math import comb, factorial


def det(a):
    a = [[Fraction(x) for x in row] for row in a]
    n = len(a)
    out = Fraction(1)
    for j in range(n):
        pivot = next((i for i in range(j, n) if a[i][j]), None)
        if pivot is None:
            return Fraction(0)
        if pivot != j:
            a[j], a[pivot] = a[pivot], a[j]
            out = -out
        p = a[j][j]
        out *= p
        for i in range(j + 1, n):
            q = a[i][j] / p
            for k in range(j + 1, n):
                a[i][k] -= q * a[j][k]
    return out


def pfaffian(a):
    n = len(a)
    if n == 0:
        return Fraction(1)
    total = Fraction(0)
    for j in range(1, n):
        minor = [
            [a[p][q] for q in range(n) if q not in (0, j)]
            for p in range(n) if p not in (0, j)
        ]
        total += (-1) ** (j + 1) * a[0][j] * pfaffian(minor)
    return total


def exterior_matrix(vectors):
    return [[vectors[j][i] for j in range(len(vectors))]
            for i in range(len(vectors[0]))]


def check_beta_constants():
    checks = 0
    for r in range(0, 13):
        beta = sum(
            Fraction((-1) ** k * comb(r, k), r + k + 1)
            for k in range(r + 1)
        )
        expected = Fraction(factorial(r) ** 2, factorial(2 * r + 1))
        assert beta == expected
        assert beta * Fraction(factorial(2 * r + 1), factorial(r) ** 2) == 1
        checks += 1

    for p in range(0, 8):
        for d in range(1, 8):
            r = p + d
            integral = sum(
                Fraction((-1) ** k * comb(d - 1, k), p + k + 1)
                for k in range(d)
            )
            expected = Fraction(factorial(p) * factorial(d - 1), factorial(r))
            constant = Fraction(factorial(r), factorial(p) * factorial(d - 1))
            assert integral == expected and constant * integral == 1
            checks += 1
    return checks


def check_debruijn_ordered_coefficient():
    checks = 0
    for m, atoms in ((1, 4), (2, 5), (3, 5)):
        dim = 2 * m
        left = []
        right = []
        weights = []
        for t in range(atoms):
            left.append([Fraction((t + 1) ** i) for i in range(dim)])
            right.append([Fraction((-t - 2) ** i) for i in range(dim)])
            weights.append(Fraction(t + 2, t + 1))

        c = [[Fraction(0) for _ in range(dim)] for _ in range(dim)]
        for t in range(atoms):
            for i in range(dim):
                for j in range(dim):
                    c[i][j] += weights[t] * (
                        left[t][i] * right[t][j] - right[t][i] * left[t][j]
                    )

        ordered = Fraction(0)
        for subset in combinations(range(atoms), m):
            columns = []
            weight = Fraction(1)
            for t in subset:
                columns.extend((left[t], right[t]))
                weight *= weights[t]
            ordered += weight * det(exterior_matrix(columns))
        assert pfaffian(c) == ordered
        checks += 1
    return checks


def trunc(x, q):
    return Fraction(x ** q) if x > 0 else Fraction(0)


def check_antisymmetrization_no_factorial():
    # Finite-sum analogue of the two independent ordered integrations in
    # the one-shot Volterra formula.  The identity is purely alternating and
    # therefore audits the coefficient independently of analytic integration.
    checks = 0
    for m in (1, 2, 3):
        dim = 2 * m
        s_grid = tuple(range(0, m + 2))
        u_grid = tuple(range(3, m + 5))
        a = tuple(2 * j + 3 for j in range(m))
        b = tuple(2 * j + 2 for j in range(m))
        q = 1

        def lv(s):
            return [Fraction((s + 1) ** i) for i in range(dim)]

        def rv(u):
            return [Fraction((-u - 1) ** i) for i in range(dim)]

        def base(ss, uu):
            return det(exterior_matrix([lv(s) for s in ss] + [rv(u) for u in uu]))

        full = Fraction(0)
        for ss in product(s_grid, repeat=m):
            for uu in product(u_grid, repeat=m):
                weight = Fraction(1)
                for j in range(m):
                    weight *= trunc(a[j] - ss[j], q)
                    weight *= trunc(uu[j] - b[j], q)
                full += base(ss, uu) * weight

        ordered = Fraction(0)
        for ss in combinations(s_grid, m):
            wl = [[trunc(a[j] - ss[i], q) for j in range(m)] for i in range(m)]
            for uu in combinations(u_grid, m):
                wr = [[trunc(uu[i] - b[j], q) for j in range(m)] for i in range(m)]
                ordered += base(ss, uu) * det(wl) * det(wr)
        assert full == ordered
        checks += 1
    return checks


def check_support_pairing():
    checks = 0
    values = range(7)
    for m in (1, 2, 3):
        lists = list(combinations(values, m))
        for q in range(4):
            for s in lists:
                for a in lists:
                    w = [[trunc(a[j] - s[i], q) for j in range(m)] for i in range(m)]
                    if det(w):
                        assert all(s[i] < a[i] for i in range(m))
                    checks += 1
    return checks


def vandermonde(xs):
    out = 1
    for i in range(len(xs)):
        for j in range(i + 1, len(xs)):
            out *= xs[j] - xs[i]
    return out


def check_torelli_constant():
    checks = 0
    for m in range(1, 6):
        xs = list(range(2 * m))
        d = 2 * m - 1
        a = [[Fraction((xs[j] - xs[i]) ** d) for j in range(2 * m)]
             for i in range(2 * m)]
        epsilon = (-1) ** (m * (m - 1) // 2)
        constant = epsilon
        for i in range(m):
            constant *= comb(2 * m - 1, i)
        assert pfaffian(a) == constant * vandermonde(xs)
        checks += 1
    return checks


def check_parameter_ledger():
    checks = 0
    for m in range(1, 20):
        n = 2 * m
        for ell in range(0, 2 * m + 3):
            r = m - 1 + ell
            d = 2 * r + 1
            assert d == n - 1 + 2 * ell
            assert (r >= 2 * m - 2) == (ell >= m - 1) == (d >= 2 * n - 3)
            if 1 <= ell <= m - 2:
                assert m <= r <= 2 * m - 3
            checks += 1
    return checks


def main():
    counts = {
        "Beta constants": check_beta_constants(),
        "ordered de Bruijn coefficient": check_debruijn_ordered_coefficient(),
        "antisymmetrization coefficient": check_antisymmetrization_no_factorial(),
        "support/pairing implications": check_support_pairing(),
        "Torelli constants": check_torelli_constant(),
        "parameter equivalences": check_parameter_ledger(),
    }
    for label, count in counts.items():
        print(f"{label}: {count} exact checks PASS")
    print("odd-branch Beta/split-knot ledger guard: PASS")


if __name__ == "__main__":
    main()
