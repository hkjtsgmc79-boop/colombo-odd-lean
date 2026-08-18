#!/usr/bin/env python3
"""Exact audit for the critical-degree raw Marsden coefficient matrix.

At degree d=m-2 the raw common-refinement matrix has columns

    L_j(i) = 1_{i<=alpha_j} prod_{h=1}^d (s_j-T_{i+h}),
    R_j(i) = 1_{i>=m-1+beta_j} prod_{h=1}^d (T_{i+h}-u_j).

This verifier checks the product formula for every small mixed solid minor,
the Desnanot--Jacobi induction data for the large mixed solid minors, and the
correct *active* Neville-pivot formula.  All arithmetic is exact.  The finite
checks guard the arbitrary-m proof in LOWER_EXPONENT_SEAM_SOLID_THEOREM.md;
they are not used as a substitute for it.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product
from math import prod

from lower_exponent_split_gate_exact import (
    determinant,
    dyck_words,
    raw_refinement_coefficients,
)


def minor(
    matrix: list[list[Fraction]], rows: list[int], columns: list[int]
) -> Fraction:
    return determinant([[matrix[i][j] for j in columns] for i in rows])


def metric_for_word(word: str, seed: int) -> tuple[list[Fraction], list[Fraction]]:
    values: list[Fraction] = []
    current = 0
    for index in range(len(word)):
        current += 1 + (index * index + 3 * seed * index + 5 * seed) % 13
        values.append(Fraction(current))
    ss = [values[i] for i, letter in enumerate(word) if letter == "S"]
    us = [values[i] for i, letter in enumerate(word) if letter == "U"]
    return ss, us


def merged_ranks(
    ss: list[Fraction], us: list[Fraction]
) -> tuple[list[int], list[int]]:
    merged = sorted(ss + us)
    rank = {value: index for index, value in enumerate(merged)}
    return [rank[s] for s in ss], [rank[u] for u in us]


def vandermonde(values: list[Fraction]) -> Fraction:
    return Fraction(prod(values[j] - values[i]
                         for i in range(len(values))
                         for j in range(i + 1, len(values))))


def small_seam_product(
    knots: list[Fraction],
    degree: int,
    row_start: int,
    left_values: list[Fraction],
    right_values: list[Fraction],
) -> Fraction:
    """The positive closed product for q<=degree+1."""
    q = len(left_values) + len(right_values)
    assert 1 <= q <= degree + 1

    common = lambda x: prod(
        x - knots[row_start + h] for h in range(q, degree + 1)
    )
    basis_constant = prod(
        knots[row_start + degree + 1 + i] - knots[row_start + j]
        for i in range(q)
        for j in range(i + 1, q)
    )
    cross = prod(s - u for s, u in product(left_values, right_values))
    value = Fraction(basis_constant)
    value *= prod(Fraction(common(s)) for s in left_values)
    value *= prod(abs(Fraction(common(u))) for u in right_values)
    value *= vandermonde(left_values)
    value *= vandermonde(right_values)
    value *= Fraction(cross)
    return value


def structured_columns(
    m: int, a: int, c: int, b: int
) -> tuple[list[int], int, int]:
    """L_a,...,L_m followed by R_c,...,R_{c+b-1}; indices are 1-based."""
    ell = m - a + 1
    h = c + b - 1
    assert 1 <= a <= m and 1 <= c <= h <= m
    return list(range(a - 1, m)) + list(range(m + c - 1, m + h)), ell, h


def structured_support_bounds(
    m: int,
    alpha: list[int],
    beta: list[int],
    a: int,
    c: int,
    b: int,
) -> tuple[int, int]:
    """Exact perfect-matching interval for a structured mixed row block."""
    _, ell, h = structured_columns(m, a, c, b)
    q = ell + b
    return m + beta[h - 1] - q, alpha[a - 1]


def audit_structured_mixed_minors(
    ss: list[Fraction], us: list[Fraction]
) -> tuple[int, int, int]:
    """Audit every suffix-L/consecutive-R solid row block."""
    m = len(ss)
    d = m - 2
    knots, matrix = raw_refinement_coefficients(ss, us, d)
    alpha, beta = merged_ranks(ss, us)
    row_count = len(matrix)
    small = large = dj = 0

    for a in range(1, m + 1):
        for c in range(1, m + 1):
            for b in range(1, m - c + 2):
                columns, ell, h = structured_columns(m, a, c, b)
                q = ell + b
                lower, upper = structured_support_bounds(
                    m, alpha, beta, a, c, b
                )
                for r in range(row_count - q + 1):
                    rows = list(range(r, r + q))
                    value = minor(matrix, rows, columns)
                    supported = lower <= r <= upper
                    assert (value > 0) == supported, (
                        m, a, c, b, r, lower, upper, value
                    )
                    if not supported:
                        assert value == 0
                        continue

                    if q <= m - 1:
                        expected = small_seam_product(
                            knots,
                            d,
                            r,
                            ss[a - 1 :],
                            us[c - 1 : h],
                        )
                        assert value == expected, (
                            m, a, c, b, r, value, expected
                        )
                        small += 1
                    else:
                        # In the large regime the matching interval has width
                        # at most one.  This is the combinatorial reason one
                        # cross term in Desnanot--Jacobi always vanishes.
                        assert upper - lower <= 1
                        large += 1

                        tl = minor(matrix, rows[:-1], columns[:-1])
                        br = minor(matrix, rows[1:], columns[1:])
                        tr = minor(matrix, rows[:-1], columns[1:])
                        bl = minor(matrix, rows[1:], columns[:-1])
                        middle = minor(matrix, rows[1:-1], columns[1:-1])
                        assert middle > 0 and tl > 0 and br > 0
                        assert tr == 0 or bl == 0
                        assert value * middle == tl * br - tr * bl
                        assert value * middle == tl * br
                        dj += 1
    return small, large, dj


def audit_all_actual_solid_minors(
    ss: list[Fraction], us: list[Fraction]
) -> int:
    """Every actual consecutive-row/consecutive-column minor is TN."""
    m = len(ss)
    alpha, beta = merged_ranks(ss, us)
    _, matrix = raw_refinement_coefficients(ss, us, m - 2)
    nr = len(matrix)
    nc = len(matrix[0])
    tested = 0
    for q in range(1, nc + 1):
        for r in range(nr - q + 1):
            for c in range(nc - q + 1):
                value = minor(
                    matrix,
                    list(range(r, r + q)),
                    list(range(c, c + q)),
                )
                if c + q <= m:                       # left only
                    supported = r <= alpha[c]
                elif c >= m:                         # right only
                    h = c - m + q                    # 1-based last R index
                    supported = r >= m + beta[h - 1] - q
                else:                                # crosses the one seam
                    a = c + 1
                    b = c + q - m
                    lower = m + beta[b - 1] - q
                    upper = alpha[a - 1]
                    supported = lower <= r <= upper
                assert (value > 0) == supported, (m, q, r, c, value)
                if not supported:
                    assert value == 0
                tested += 1
    return tested


def largest_solid_pivot_ratio(
    original: list[list[Fraction]], row: int, column: int
) -> tuple[int, Fraction] | None:
    """Correct compressed-Neville pivot: largest positive ending solid."""
    candidates: list[tuple[int, Fraction]] = []
    for q in range(1, min(row, column) + 2):
        rows = list(range(row - q + 1, row + 1))
        columns = list(range(column - q + 1, column + 1))
        numerator = minor(original, rows, columns)
        denominator = (
            minor(original, rows[:-1], columns[:-1])
            if q > 1
            else Fraction(1)
        )
        if numerator > 0 and denominator > 0:
            candidates.append((q, numerator / denominator))
    return candidates[-1] if candidates else None


def audit_compressed_neville(
    ss: list[Fraction], us: list[Fraction]
) -> tuple[int, int]:
    """Check the active pivot formula and the exact active-row profile."""
    m = len(ss)
    d = m - 2
    alpha, beta = merged_ranks(ss, us)
    gamma = [m - 1 + value for value in beta]
    _, original = raw_refinement_coefficients(ss, us, d)
    work = [row[:] for row in original]
    labels = list(range(len(work)))
    operations = deletions = 0

    for column in range(2 * m):
        if column == 0:
            expected = list(range(len(original)))
        elif column < m:
            expected = (
                list(range(alpha[-1] + 1))
                + list(range(max(alpha[-1] + 1, gamma[0]), len(original)))
            )
        else:
            j = column - m                 # zero-based current R index
            expected = (
                list(range(m))
                + gamma[:j]
                + list(range(gamma[j], len(original)))
            )
        assert labels == expected, (m, column, labels, expected)

        # Before the column is changed, every nonzero active entry is the
        # largest-ending-solid ratio.  The previously used fixed bordered
        # pivot-row ratio is not this quantity and fails already at m=3.
        for position in range(column, len(work)):
            if work[position][column] == 0:
                continue
            result = largest_solid_pivot_ratio(
                original, labels[position], column
            )
            assert result is not None
            _, ratio = result
            assert work[position][column] == ratio, (
                m, column, labels[position], work[position][column], ratio
            )

        for position in range(len(work) - 1, column, -1):
            if work[position][column] == 0:
                continue
            # At the critical degree the nonzero active segment has no gap;
            # all structural zero rows are deleted only after a column.
            assert work[position - 1][column] > 0
            multiplier = work[position][column] / work[position - 1][column]
            assert multiplier > 0
            for target in range(column, 2 * m):
                work[position][target] -= (
                    multiplier * work[position - 1][target]
                )
            assert work[position][column] == 0
            operations += 1

        for position in range(len(work) - 1, -1, -1):
            if all(value == 0 for value in work[position]):
                del work[position]
                del labels[position]
                deletions += 1

    assert labels == list(range(m)) + gamma
    assert deletions == m - 1
    for i, row in enumerate(work):
        assert row[i] > 0
        assert all(row[j] == 0 for j in range(i))
    return operations, deletions


def main() -> None:
    totals = [0, 0, 0, 0, 0, 0]
    for m in range(2, 7):
        words = dyck_words(m)
        for index, word in enumerate(words):
            ss, us = metric_for_word(word, seed=m + index + 1)
            small, large, dj = audit_structured_mixed_minors(ss, us)
            solids = audit_all_actual_solid_minors(ss, us)
            operations, deletions = audit_compressed_neville(ss, us)
            for i, value in enumerate(
                (small, large, dj, solids, operations, deletions)
            ):
                totals[i] += value
        print(f"m={m}: all {len(words)} Dyck chambers exact PASS")

    # A larger-rank guard without the expensive all-chamber enumeration.
    for m in range(7, 10):
        words = dyck_words(m)
        for index in (0, len(words) // 2, len(words) - 1):
            ss, us = metric_for_word(words[index], seed=31 + m + index)
            audit_structured_mixed_minors(ss, us)
            audit_compressed_neville(ss, us)
        print(f"m={m}: three extremal/central chambers exact PASS")

    print(
        "audited totals through all chambers m<=6: "
        f"small mixed products={totals[0]}, "
        f"large mixed positives={totals[1]}, DJ identities={totals[2]}, "
        f"actual solid minors={totals[3]}, "
        f"positive Neville chips={totals[4]}, deletions={totals[5]}"
    )
    print("critical-degree seam-solid theorem exact audit: PASS")


if __name__ == "__main__":
    main()
