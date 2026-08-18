#!/usr/bin/env python3
"""Exact narrow red team from the critical seam matrix to odd Pfaffians.

The script is intentionally independent of the arbitrary-rank seam proof.
It protects its interfaces and normalizations at m=2,3:

* Marsden/B-spline multiplication, with no missing scalar;
* the p=0 indicator convention at m=2;
* Volterra antisymmetrization, with no m!;
* de Bruijn exterior expansion, with exactly one ordered-chamber copy;
* the grouped/interleaved sign (-1)^(m choose 2);
* the Colombo Beta constant; and
* strict central-simplex and Torelli/Pfaffian anchors.

Only Python's standard library and exact Fraction arithmetic are used.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations, permutations, product
from math import comb, factorial, prod


def determinant(matrix: list[list[int | Fraction]]) -> Fraction:
    work = [[Fraction(value) for value in row] for row in matrix]
    order = len(work)
    if order == 0:
        return Fraction(1)
    assert all(len(row) == order for row in work)
    answer = Fraction(1)
    sign = 1
    for column in range(order):
        pivot = next(
            (row for row in range(column, order) if work[row][column] != 0),
            None,
        )
        if pivot is None:
            return Fraction(0)
        if pivot != column:
            work[column], work[pivot] = work[pivot], work[column]
            sign = -sign
        value = work[column][column]
        answer *= value
        for target in range(column, order):
            work[column][target] /= value
        for row in range(column + 1, order):
            multiplier = work[row][column]
            if multiplier:
                for target in range(column, order):
                    work[row][target] -= multiplier * work[column][target]
    return sign * answer


def minor(
    matrix: list[list[int | Fraction]],
    rows: tuple[int, ...],
    columns: tuple[int, ...],
) -> Fraction:
    return determinant([[matrix[row][column] for column in columns] for row in rows])


def pfaffian(matrix: list[list[int | Fraction]]) -> Fraction:
    order = len(matrix)
    if order == 0:
        return Fraction(1)
    answer = Fraction(0)
    for column in range(1, order):
        reduced = [
            [
                matrix[row][target]
                for target in range(order)
                if target not in (0, column)
            ]
            for row in range(order)
            if row not in (0, column)
        ]
        answer += (-1) ** (column + 1) * matrix[0][column] * pfaffian(reduced)
    return answer


def vandermonde(values: list[int | Fraction]) -> Fraction:
    return Fraction(
        prod(
            values[j] - values[i]
            for i in range(len(values))
            for j in range(i + 1, len(values))
        )
    )


def trunc(value: int | Fraction, degree: int) -> Fraction:
    """Strict truncated power; degree zero is the open indicator."""

    value = Fraction(value)
    if value <= 0:
        return Fraction(0)
    return value**degree


def split_matrix(
    x: list[int | Fraction],
    s: list[int | Fraction],
    u: list[int | Fraction],
    degree: int,
) -> list[list[Fraction]]:
    return [
        [trunc(value - node, degree) for value in s]
        + [trunc(node - value, degree) for value in u]
        for node in x
    ]


def b_spline_basis(
    knots: list[int | Fraction], degree: int, node: int | Fraction
) -> list[Fraction]:
    knots = [Fraction(value) for value in knots]
    node = Fraction(node)
    basis = [
        Fraction(int(knots[index] <= node < knots[index + 1]))
        for index in range(len(knots) - 1)
    ]
    for current_degree in range(1, degree + 1):
        next_basis: list[Fraction] = []
        for index in range(len(knots) - current_degree - 1):
            left = Fraction(0)
            left_denominator = knots[index + current_degree] - knots[index]
            if left_denominator:
                left = (node - knots[index]) * basis[index] / left_denominator
            right = Fraction(0)
            right_denominator = (
                knots[index + current_degree + 1] - knots[index + 1]
            )
            if right_denominator:
                right = (
                    (knots[index + current_degree + 1] - node)
                    * basis[index + 1]
                    / right_denominator
                )
            next_basis.append(left + right)
        basis = next_basis
    return basis


def raw_marsden_coefficients(
    s: list[int], u: list[int], degree: int, anchor_left: int, anchor_right: int
) -> tuple[list[int], list[list[Fraction]], list[int], list[int]]:
    merged = sorted(s + u)
    ranks = {value: index for index, value in enumerate(merged)}
    p = [ranks[value] for value in s]
    q = [ranks[value] for value in u]
    knots = [anchor_left] * (degree + 1) + merged + [anchor_right] * (degree + 1)
    row_count = len(knots) - degree - 1
    matrix: list[list[Fraction]] = []
    for row in range(row_count):
        left = [
            Fraction(prod(value - knots[row + h] for h in range(1, degree + 1)))
            if row <= ranks[value]
            else Fraction(0)
            for value in s
        ]
        right = [
            Fraction(prod(knots[row + h] - value for h in range(1, degree + 1)))
            if row >= degree + 1 + ranks[value]
            else Fraction(0)
            for value in u
        ]
        matrix.append(left + right)
    return knots, matrix, p, q


def matrix_product(
    left: list[list[Fraction]], right: list[list[Fraction]]
) -> list[list[Fraction]]:
    return [
        [
            sum(left[row][inner] * right[inner][column] for inner in range(len(right)))
            for column in range(len(right[0]))
        ]
        for row in range(len(left))
    ]


def all_minors_nonnegative(matrix: list[list[Fraction]]) -> int:
    row_count = len(matrix)
    column_count = len(matrix[0])
    tested = 0
    for order in range(1, min(row_count, column_count) + 1):
        for rows in combinations(range(row_count), order):
            for columns in combinations(range(column_count), order):
                assert minor(matrix, rows, columns) >= 0, (rows, columns)
                tested += 1
    return tested


def check_marsden_anchors() -> tuple[list[tuple[int, Fraction]], int]:
    anchors = [
        (2, [0, 3, 7, 10], [2, 6], [4, 8], -5, 15),
        (3, [0, 3, 6, 10, 13, 16], [2, 5, 9], [4, 8, 12], -5, 20),
    ]
    values: list[tuple[int, Fraction]] = []
    audited = 0
    for m, x, s, u, anchor_left, anchor_right in anchors:
        degree = m - 2
        knots, coefficients, _, q = raw_marsden_coefficients(
            s, u, degree, anchor_left, anchor_right
        )
        collocation = [b_spline_basis(knots, degree, node) for node in x]
        direct = split_matrix(x, s, u, degree)
        assert matrix_product(collocation, coefficients) == direct
        audited += all_minors_nonnegative(coefficients)
        audited += all_minors_nonnegative(collocation)
        critical = determinant(direct)
        assert critical > 0
        if m == 2:
            # Degree zero is the strict indicator convention, not 0^0=1.
            assert degree == 0 and critical == 1
            assert direct == [
                [1, 1, 0, 0],
                [0, 1, 0, 0],
                [0, 0, 1, 0],
                [0, 0, 1, 1],
            ]
        pivot_rows = list(range(m)) + [degree + 1 + rank for rank in q]
        assert minor(
            coefficients, tuple(pivot_rows), tuple(range(2 * m))
        ) > 0
        values.append((m, critical))
    return values, audited


def check_scalar_beta_and_volterra() -> int:
    checks = 0
    for r in range(0, 10):
        beta = sum(
            Fraction((-1) ** k * comb(r, k), r + k + 1)
            for k in range(r + 1)
        )
        expected = Fraction(factorial(r) ** 2, factorial(2 * r + 1))
        assert beta == expected
        c_r = Fraction(factorial(2 * r + 1), factorial(r) ** 2)
        assert c_r * beta == 1
        checks += 1

    for degree in range(1, 10):
        x = Fraction(-2)
        s = Fraction(5)
        integral = (s - x) ** degree / degree
        assert degree * integral == trunc(s - x, degree)
        checks += 1
    return checks


def columns_to_matrix(columns: list[list[Fraction]]) -> list[list[Fraction]]:
    return [[columns[column][row] for column in range(len(columns))] for row in range(len(columns[0]))]


def check_ordered_antisymmetrization() -> int:
    """Finite-sum analogue of the two independent Volterra integrations."""

    checks = 0
    for m in (2, 3):
        dimension = 2 * m
        a_grid = tuple(range(0, m + 2))
        b_grid = tuple(range(3, m + 5))
        s_target = tuple(2 * index + 3 for index in range(m))
        u_target = tuple(2 * index + 2 for index in range(m))

        def left_vector(value: int) -> list[Fraction]:
            return [Fraction((value + 2) ** row) for row in range(dimension)]

        def right_vector(value: int) -> list[Fraction]:
            return [Fraction((-value - 3) ** row) for row in range(dimension)]

        def base(a_values: tuple[int, ...], b_values: tuple[int, ...]) -> Fraction:
            columns = [left_vector(value) for value in a_values] + [
                right_vector(value) for value in b_values
            ]
            return determinant(columns_to_matrix(columns))

        labelled = Fraction(0)
        for a_values in product(a_grid, repeat=m):
            for b_values in product(b_grid, repeat=m):
                weight = Fraction(1)
                for index in range(m):
                    weight *= int(a_values[index] < s_target[index])
                    weight *= int(u_target[index] < b_values[index])
                labelled += base(a_values, b_values) * weight

        ordered = Fraction(0)
        for a_values in combinations(a_grid, m):
            left_weight = [
                [Fraction(int(a_values[row] < s_target[column])) for column in range(m)]
                for row in range(m)
            ]
            for b_values in combinations(b_grid, m):
                right_weight = [
                    [Fraction(int(u_target[column] < b_values[row])) for column in range(m)]
                    for row in range(m)
                ]
                ordered += (
                    base(a_values, b_values)
                    * determinant(left_weight)
                    * determinant(right_weight)
                )
        assert labelled == ordered
        checks += 1
    return checks


def check_step_support() -> int:
    checks = 0
    for m in (2, 3):
        ordered_lists = list(combinations(range(8), m))
        for a in ordered_lists:
            for s in ordered_lists:
                left = [
                    [Fraction(int(a[row] < s[column])) for column in range(m)]
                    for row in range(m)
                ]
                value = determinant(left)
                assert value in (0, 1)
                if value:
                    assert a[0] < s[0]
                    assert all(s[index - 1] <= a[index] < s[index] for index in range(1, m))
                checks += 1
    return checks


def check_debruijn_and_factorial() -> int:
    checks = 0
    for m, atom_count in ((2, 5), (3, 6)):
        dimension = 2 * m
        left = [
            [Fraction((atom + 1) ** row) for row in range(dimension)]
            for atom in range(atom_count)
        ]
        right = [
            [Fraction((-atom - 2) ** row) for row in range(dimension)]
            for atom in range(atom_count)
        ]
        skew = [[Fraction(0) for _ in range(dimension)] for _ in range(dimension)]
        for atom in range(atom_count):
            for row in range(dimension):
                for column in range(dimension):
                    skew[row][column] += (
                        left[atom][row] * right[atom][column]
                        - right[atom][row] * left[atom][column]
                    )

        ordered = Fraction(0)
        for atoms in combinations(range(atom_count), m):
            columns: list[list[Fraction]] = []
            for atom in atoms:
                columns.extend((left[atom], right[atom]))
            ordered += determinant(columns_to_matrix(columns))

        full = Fraction(0)
        for atoms in product(range(atom_count), repeat=m):
            columns = []
            for atom in atoms:
                columns.extend((left[atom], right[atom]))
            full += determinant(columns_to_matrix(columns))

        assert pfaffian(skew) == ordered
        assert full == factorial(m) * ordered
        checks += 1
    return checks


def separated_power_determinant(
    x: list[int | Fraction], t: list[int | Fraction], degree: int
) -> Fraction:
    return determinant(
        [[(Fraction(tj) - Fraction(xi)) ** degree for tj in t] for xi in x]
    )


def shifted_positive_cauchy_binet_terms(
    x: list[int | Fraction],
    t: list[int | Fraction],
    degree: int,
    cut: int | Fraction,
) -> list[Fraction]:
    """Positive expansion of (t_j-x_i)^degree around x_m<cut<t_1."""

    order = len(x)
    assert len(t) == order and x[-1] < cut < t[0]
    early = [Fraction(cut) - Fraction(value) for value in x]  # decreasing
    late = [Fraction(value) - Fraction(cut) for value in t]   # increasing
    terms: list[Fraction] = []
    for exponents in combinations(range(degree + 1), order):
        left = [
            [
                Fraction(comb(degree, exponent)) * value**exponent
                for exponent in exponents
            ]
            for value in early
        ]
        right = [
            [value ** (degree - exponent) for value in late]
            for exponent in exponents
        ]
        terms.append(determinant(left) * determinant(right))
    return terms


def check_strictness_and_binomial_warning() -> tuple[int, list[tuple[int, int, Fraction]]]:
    checks = 0
    central_values: list[tuple[int, int, Fraction]] = []
    central_data = [
        (2, [0, 2, 8, 10], [3, 5]),
        (3, [0, 2, 4, 10, 12, 14], [5, 6, 7]),
    ]
    for m, x, t in central_data:
        early = x[:m]
        late = x[m:]
        base_degree = m - 1
        base_left = separated_power_determinant(early, t, base_degree)
        expected = (
            prod(comb(base_degree, k) for k in range(m))
            * vandermonde(early)
            * vandermonde(t)
        )
        assert base_left == expected > 0
        for degree in range(base_degree, base_degree + 3):
            grouped = determinant(split_matrix(x, t, t, degree))
            left_value = separated_power_determinant(early, t, degree)
            right_value = separated_power_determinant(t, late, degree)
            left_terms = shifted_positive_cauchy_binet_terms(
                early, t, degree, Fraction(early[-1] + t[0], 2)
            )
            # Transpose the right block: rows=t and columns=late.
            right_terms = shifted_positive_cauchy_binet_terms(
                t, late, degree, Fraction(t[-1] + late[0], 2)
            )
            assert all(term > 0 for term in left_terms)
            assert all(term > 0 for term in right_terms)
            assert sum(left_terms) == left_value
            assert sum(right_terms) == right_value
            assert grouped == left_value * right_value > 0
            central_values.append((m, degree, grouped))
            checks += 1

    # Red-team the discarded claim that the ordinary binomial Cauchy--Binet
    # expansion is termwise positive.
    x = [0, 1]
    t = [2, 3]
    degree = 2
    terms: list[Fraction] = []
    for exponents in combinations(range(degree + 1), 2):
        left = [
            [Fraction(comb(degree, k) * (-node) ** k) for k in exponents]
            for node in x
        ]
        right = [
            [Fraction(node ** (degree - k)) for node in t]
            for k in exponents
        ]
        terms.append(determinant(left) * determinant(right))
    assert terms == [12, -5, 0]
    assert sum(terms) == separated_power_determinant(x, t, degree) == 7
    checks += 1
    return checks, central_values


def check_grouping_and_pfaffian_anchors() -> tuple[int, list[tuple[int, int, Fraction]]]:
    checks = 0
    values: list[tuple[int, int, Fraction]] = []
    for m in (2, 3):
        x = list(range(2 * m))
        epsilon = (-1) ** (m * (m - 1) // 2)
        for r in range(m - 1, m + 2):
            skew = [
                [Fraction((x[column] - x[row]) ** (2 * r + 1)) for column in range(2 * m)]
                for row in range(2 * m)
            ]
            value = pfaffian(skew)
            assert epsilon * value > 0
            values.append((m, r, value))
            if r == m - 1:
                constant = prod(comb(2 * m - 1, k) for k in range(m))
                assert value == epsilon * constant * vandermonde(x)
            checks += 1

        t = [Fraction(2 * m - 1, 2) + Fraction(index, m + 1) for index in range(m)]
        grouped_columns = []
        interleaved_columns = []
        for value in t:
            left = [trunc(value - node, m - 1) for node in x]
            right = [trunc(node - value, m - 1) for node in x]
            grouped_columns.append(left)
            interleaved_columns.extend((left, right))
        for value in t:
            grouped_columns.append([trunc(node - value, m - 1) for node in x])
        grouped = determinant(columns_to_matrix(grouped_columns))
        interleaved = determinant(columns_to_matrix(interleaved_columns))
        assert interleaved == epsilon * grouped
        checks += 1
    return checks, values


def main() -> None:
    marsden_values, minor_count = check_marsden_anchors()
    beta_checks = check_scalar_beta_and_volterra()
    antisym_checks = check_ordered_antisymmetrization()
    support_checks = check_step_support()
    debruijn_checks = check_debruijn_and_factorial()
    strict_checks, central_values = check_strictness_and_binomial_warning()
    pfaffian_checks, pfaffian_values = check_grouping_and_pfaffian_anchors()

    print(f"Marsden anchors: {marsden_values}; audited TN minors={minor_count}: PASS")
    print(f"scalar Beta/Volterra constants: {beta_checks} checks: PASS")
    print(f"ordered Volterra antisymmetrization: {antisym_checks} checks, no m!: PASS")
    print(f"step-kernel support implications: {support_checks} checks: PASS")
    print(f"de Bruijn exterior coefficient: {debruijn_checks} checks, full=m!*ordered: PASS")
    print(f"central strict anchors: {central_values}: PASS")
    print("binomial Cauchy--Binet warning: terms=(12,-5,0), total=7")
    print(f"Pfaffian anchors: {pfaffian_values}: PASS")
    print("odd seam-to-Pfaffian narrow red team: PASS")


if __name__ == "__main__":
    main()
