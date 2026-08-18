#!/usr/bin/env python3
"""End-to-end exact guard for ODD_BRANCH_STAIRCASE_CLOSURE.md.

This is a finite sign/index guard, not a substitute for the arbitrary-rank
solid-minor and staircase proofs.  It independently checks:

* the critical and Volterra-lifted paired determinants on every Dyck word
  through m=5;
* the m=2 degree-zero convention;
* the sharp below-threshold counterexamples;
* direct Pfaffian signs and the exact Torelli constant through m=6;
* strict central-simplex determinants;
* a shifted binomial Cauchy--Binet expansion in which every separated-power
  summand really has positive sign.

Only the Python standard library and exact ``Fraction`` arithmetic are used.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations
from math import comb, prod

from lower_exponent_split_gate_exact import H, determinant, pfaffian
from lower_exponent_seam_solid_exact import dyck_words, metric_for_word


def vandermonde(values: list[Fraction]) -> Fraction:
    return Fraction(
        prod(
            values[j] - values[i]
            for i in range(len(values))
            for j in range(i + 1, len(values))
        )
    )


def pfaffian_power(xs: list[Fraction], exponent: int) -> Fraction:
    matrix = [
        [
            Fraction(0) if i == j else (xs[j] - xs[i]) ** exponent
            for j in range(len(xs))
        ]
        for i in range(len(xs))
    ]
    return pfaffian(matrix)


def deterministic_x_profiles(
    ss: list[Fraction], us: list[Fraction]
) -> list[list[Fraction]]:
    m = len(ss)
    low = min(ss + us) - 3 * m - 1
    high = max(ss + us) + 3 * m + 1
    span = high - low
    uniform = [
        low + Fraction((2 * i + 1) * span, 4 * m)
        for i in range(2 * m)
    ]

    # A nonuniform profile with alternating short and long gaps.
    nonuniform: list[Fraction] = []
    current = low
    for i in range(2 * m):
        current += Fraction(1 + (i * i + 3 * i + m) % 7, 3)
        nonuniform.append(current)
    scale = (high - low) / (nonuniform[-1] - nonuniform[0] + 2)
    nonuniform = [low + (value - nonuniform[0] + 1) * scale for value in nonuniform]
    assert all(uniform[i] < uniform[i + 1] for i in range(2 * m - 1))
    assert all(nonuniform[i] < nonuniform[i + 1] for i in range(2 * m - 1))
    return [uniform, nonuniform]


def audit_paired_determinants() -> tuple[int, int, int]:
    critical = lifted = 0
    for m in range(2, 6):
        for index, word in enumerate(dyck_words(m)):
            ss, us = metric_for_word(word, seed=17 + 5 * m + index)
            for xs in deterministic_x_profiles(ss, us):
                value = H(xs, ss, us, m - 2)
                assert value >= 0, (m, word, "critical", value)
                critical += 1
                for degree in range(m - 1, m + 2):
                    value = H(xs, ss, us, degree)
                    assert value >= 0, (m, word, degree, value)
                    lifted += 1
    high_rank = 0
    for m in range(6, 10):
        words = dyck_words(m)
        for index in (0, len(words) // 2, len(words) - 1):
            ss, us = metric_for_word(words[index], seed=71 + m + index)
            xs = deterministic_x_profiles(ss, us)[1]
            assert H(xs, ss, us, m - 2) >= 0
            assert H(xs, ss, us, m - 1) >= 0
            high_rank += 2
    return critical, lifted, high_rank


def audit_degree_zero_and_sharpness() -> tuple[int, int]:
    # Both m=2 Dyck words, with x chosen in every support region.
    checks = 0
    examples = [
        (
            [Fraction(v) for v in (0, 3, 6, 9)],
            [Fraction(v) for v in (2, 4)],
            [Fraction(v) for v in (5, 7)],
        ),
        (
            [Fraction(v) for v in (0, 3, 6, 9)],
            [Fraction(v) for v in (2, 6)],
            [Fraction(v) for v in (4, 8)],
        ),
    ]
    for xs, ss, us in examples:
        assert H(xs, ss, us, 0) >= 0
        assert H(xs, ss, us, 1) >= 0
        checks += 2

    # Exhaust every weak relative order representable on seven ranks,
    # including samples that coincide with S/U knots.  The direct
    # prefix/suffix proof says the determinant is one in exactly three
    # index configurations and zero otherwise.
    exhaustive = 0
    positive_indices = {(1, 2, 2, 4), (1, 2, 3, 4), (1, 3, 3, 4)}
    grid = range(7)
    for x_values in combinations(grid, 4):
        for s_values in combinations(grid, 2):
            for u_values in combinations(grid, 2):
                if any(s_values[j] >= u_values[j] for j in range(2)):
                    continue
                xs = [Fraction(value) for value in x_values]
                ss = [Fraction(value) for value in s_values]
                us = [Fraction(value) for value in u_values]
                ell = tuple(sum(x < s for x in xs) for s in ss)
                rr = tuple(1 + sum(x <= u for x in xs) for u in us)
                expected = Fraction(int((*ell, *rr) in positive_indices))
                assert H(xs, ss, us, 0) == expected, (xs, ss, us, ell, rr)
                exhaustive += 1

    xs = [Fraction(v) for v in (0, 3, 5, 7, 11, 14)]
    ss = [Fraction(v) for v in (2, 6, 8)]
    us = [Fraction(v) for v in (4, 10, 12)]
    assert H(xs, ss, us, 0) == -1
    assert H(xs, ss, us, 1) == 36
    checks += 2

    xs = [Fraction(v) for v in (0, 13, 20, 38, 60, 86, 88, 100)]
    ss = [Fraction(v) for v in (4, 50, 70, 83)]
    us = [Fraction(v) for v in (27, 66, 78, 90)]
    assert H(xs, ss, us, 1) == -9_609_600
    checks += 1
    return checks, exhaustive


def audit_torelli_and_pfaffian_sign() -> tuple[int, int]:
    tore = signs = 0
    for m in range(1, 7):
        xs = [Fraction(i * i + 3 * i + (i % 2)) for i in range(2 * m)]
        assert all(xs[i] < xs[i + 1] for i in range(2 * m - 1))
        epsilon = -1 if (m * (m - 1) // 2) % 2 else 1

        exponent = 2 * m - 1
        actual = pfaffian_power(xs, exponent)
        expected = Fraction(epsilon)
        expected *= prod(comb(2 * m - 1, k) for k in range(m))
        expected *= vandermonde(xs)
        assert actual == expected, (m, actual, expected)
        tore += 1

        for r in range(m - 1, m + 3):
            actual = pfaffian_power(xs, 2 * r + 1)
            assert epsilon * actual > 0, (m, r, actual)
            signs += 1
    return tore, signs


def separated_power_matrix(
    left: list[Fraction], right: list[Fraction], degree: int
) -> list[list[Fraction]]:
    return [[(y - x) ** degree for y in right] for x in left]


def audit_shifted_binomial_terms(
    left: list[Fraction], right: list[Fraction], degree: int
) -> int:
    """Every Cauchy--Binet term is positive after shifting into the gap."""
    m = len(left)
    assert len(right) == m and left[-1] < right[0] and degree >= m - 1
    center = (left[-1] + right[0]) / 2
    xvars = [center - value for value in left]  # positive, decreasing
    tvars = [value - center for value in right]  # positive, increasing
    assert all(value > 0 for value in xvars + tvars)

    total = Fraction(0)
    checks = 0
    for exponents in combinations(range(degree + 1), m):
        left_minor = determinant(
            [[xvars[i] ** k for k in exponents] for i in range(m)]
        )
        right_minor = determinant(
            [
                [
                    Fraction(comb(degree, k)) * tvars[j] ** (degree - k)
                    for j in range(m)
                ]
                for k in exponents
            ]
        )
        term = left_minor * right_minor
        assert term > 0, (left, right, degree, exponents, term)
        total += term
        checks += 1

    direct = determinant(separated_power_matrix(left, right, degree))
    assert total == direct and direct > 0
    return checks


def audit_central_simplex() -> tuple[int, int]:
    determinants = binomial_terms = 0
    for m in range(2, 7):
        left = [Fraction(i) for i in range(m)]
        knots = [Fraction(2 * m + 2 * j) for j in range(m)]
        right = [Fraction(5 * m + i * i + i) for i in range(m)]
        assert left[-1] < knots[0] < knots[-1] < right[0]
        xs = left + right
        for degree in range(m - 1, m + 2):
            value = H(xs, knots, knots, degree)
            assert value > 0, (m, degree, value)
            determinants += 1
            binomial_terms += audit_shifted_binomial_terms(left, knots, degree)

            # Reflect the right block to the same separated-power audit.
            reflected_left = [-value for value in reversed(right)]
            reflected_right = [-value for value in reversed(knots)]
            binomial_terms += audit_shifted_binomial_terms(
                reflected_left, reflected_right, degree
            )
    return determinants, binomial_terms


def main() -> None:
    critical, lifted, high_rank = audit_paired_determinants()
    boundary, boundary_exhaustive = audit_degree_zero_and_sharpness()
    tore, signs = audit_torelli_and_pfaffian_sign()
    central, terms = audit_central_simplex()
    print(
        "paired determinants: "
        f"critical={critical}, lifted={lifted}, high-rank={high_rank} PASS"
    )
    print(
        "degree-zero/sharpness: "
        f"anchors={boundary}, knot-boundary orders={boundary_exhaustive} PASS"
    )
    print(f"Torelli anchors={tore}, direct odd-Pfaffian signs={signs} PASS")
    print(
        f"central determinants={central}, shifted positive binomial terms={terms} PASS"
    )
    print("odd-branch staircase closure end-to-end exact guard: PASS")


if __name__ == "__main__":
    main()
