#!/usr/bin/env python3
"""Exact gates for the conjectural lower-exponent split-knot theorem.

The target is

    det[(s_j-x_i)_+^p | (x_i-u_j)_+^p] >= 0,

for ordered x, s, u with s_j < u_j at the proposed sharp threshold
p=m-2.  Everything here uses exact rational/integer arithmetic.  Finite
searches are evidence unless explicitly identified as exhaustive symbolic
certificates.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations, permutations
from math import comb
import random


def determinant(matrix: list[list[Fraction]]) -> Fraction:
    work = [row[:] for row in matrix]
    n = len(work)
    assert all(len(row) == n for row in work)
    answer = Fraction(1)
    for col in range(n):
        pivot = next((r for r in range(col, n) if work[r][col]), None)
        if pivot is None:
            return Fraction(0)
        if pivot != col:
            work[pivot], work[col] = work[col], work[pivot]
            answer = -answer
        value = work[col][col]
        answer *= value
        for j in range(col, n):
            work[col][j] /= value
        for i in range(col + 1, n):
            multiplier = work[i][col]
            if multiplier:
                for j in range(col, n):
                    work[i][j] -= multiplier * work[col][j]
    return answer


def tp(value: Fraction, p: int) -> Fraction:
    return value**p if value > 0 else Fraction(0)


def split_matrix(
    xs: list[Fraction], ss: list[Fraction], us: list[Fraction], p: int
) -> list[list[Fraction]]:
    return [
        [tp(s - x, p) for s in ss] + [tp(x - u, p) for u in us]
        for x in xs
    ]


def H(
    xs: list[Fraction], ss: list[Fraction], us: list[Fraction], p: int
) -> Fraction:
    return determinant(split_matrix(xs, ss, us, p))


def pfaffian(matrix: list[list[Fraction]]) -> Fraction:
    n = len(matrix)
    assert n % 2 == 0 and all(len(row) == n for row in matrix)
    if n == 0:
        return Fraction(1)
    answer = Fraction(0)
    for j in range(1, n):
        keep = [i for i in range(1, n) if i != j]
        minor = [[matrix[a][b] for b in keep] for a in keep]
        answer += (-1) ** (j + 1) * matrix[0][j] * pfaffian(minor)
    return answer


def product_g(
    xs: list[Fraction], ss: list[Fraction], us: list[Fraction], p: int
) -> list[list[Fraction]]:
    left = [[tp(s - x, p) for s in ss] for x in xs]
    right = [[tp(x - u, p) for u in us] for x in xs]
    return [
        [sum(left[i][k] * right[j][k] for k in range(len(ss)))
         for j in range(len(xs))]
        for i in range(len(xs))
    ]


def check_all_minors_tn(matrix: list[list[Fraction]]) -> int:
    n = len(matrix)
    count = 0
    for order in range(1, n + 1):
        for rows in combinations(range(n), order):
            for cols in combinations(range(n), order):
                value = determinant(
                    [[matrix[i][j] for j in cols] for i in rows]
                )
                assert value >= 0, (order, rows, cols, value)
                count += 1
    return count


def divided_difference_coefficients(nodes: list[Fraction]) -> list[Fraction]:
    return [
        Fraction(1, 1)
        / prod_fraction(nodes[j] - nodes[h] for h in range(len(nodes)) if h != j)
        for j in range(len(nodes))
    ]


def prod_fraction(values) -> Fraction:
    answer = Fraction(1)
    for value in values:
        answer *= value
    return answer


def divided_difference_basis(
    xs: list[Fraction], ss: list[Fraction], us: list[Fraction], p: int
) -> list[list[Fraction]]:
    """Prefix-left and suffix-right divided differences.

    The column transform has positive determinant, so the full determinant
    has exactly the sign of H.  Every resulting entry is nonnegative.
    """
    m = len(ss)
    left_columns: list[list[Fraction]] = []
    right_columns: list[list[Fraction]] = []
    for k in range(1, m + 1):
        lc = divided_difference_coefficients(ss[:k])
        left_columns.append(
            [sum(c * tp(s - x, p) for c, s in zip(lc, ss[:k])) for x in xs]
        )
    for j in range(m):
        nodes = us[j:]
        rc = divided_difference_coefficients(nodes)
        right_columns.append(
            [
                (-1) ** (m - j - 1)
                * sum(c * tp(x - u, p) for c, u in zip(rc, nodes))
                for x in xs
            ]
        )
    columns = left_columns + right_columns
    matrix = [[columns[j][i] for j in range(2 * m)] for i in range(2 * m)]
    assert all(value >= 0 for row in matrix for value in row)
    return matrix


def divided_difference_tn_probe() -> tuple[bool, tuple | None]:
    """Test the tempting 'one ordinary TN basis' shortcut."""
    examples = [
        ([0, 3, 5, 7, 11, 14], [2, 6, 8], [4, 10, 12]),
        (
            [0, 14, 43, 51, 73, 86, 111, 119],
            [6, 19, 77, 87],
            [30, 63, 98, 108],
        ),
    ]
    for raw_xs, raw_ss, raw_us in examples:
        xs = list(map(Fraction, raw_xs))
        ss = list(map(Fraction, raw_ss))
        us = list(map(Fraction, raw_us))
        m = len(ss)
        matrix = divided_difference_basis(xs, ss, us, m - 2)
        check_all_minors_tn(matrix)
    return True, None


def lower_refinement_coefficients(
    ss: list[Fraction], us: list[Fraction], p: int
) -> tuple[list[Fraction], list[list[Fraction]]]:
    """Common fine B-spline coefficients after the prefix/suffix DD change."""
    m = len(ss)
    assert p == m - 2
    a = min(ss + us) - 1
    b = max(ss + us) + 1
    fine = [a] * (p + 1) + sorted(ss + us) + [b] * (p + 1)
    nrows = len(fine) - p - 1
    raw_left: list[list[Fraction]] = []
    raw_right: list[list[Fraction]] = []
    for s in ss:
        raw_left.append(
            [
                prod_fraction(s - fine[i + h] for h in range(1, p + 1))
                # The normalized fine B-spline has support
                # [T_i,T_{i+p+1}].  It can occur in (s-x)_+^p only when
                # that support ends at or before s.  For p>0 the previous
                # off-by-one condition happened to add only zero terms, but
                # the distinction is essential at p=0.
                if fine[i + p + 1] <= s
                else Fraction(0)
                for i in range(nrows)
            ]
        )
    for u in us:
        raw_right.append(
            [
                prod_fraction(fine[i + h] - u for h in range(1, p + 1))
                # Dually, the whole fine support must start at or after u.
                if fine[i] >= u
                else Fraction(0)
                for i in range(nrows)
            ]
        )
    columns: list[list[Fraction]] = []
    for k in range(1, m + 1):
        coeff = divided_difference_coefficients(ss[:k])
        columns.append(
            [sum(c * raw_left[j][i] for j, c in enumerate(coeff)) for i in range(nrows)]
        )
    for j in range(m):
        nodes = us[j:]
        coeff = divided_difference_coefficients(nodes)
        columns.append(
            [
                (-1) ** (m - j - 1)
                * sum(c * raw_right[j + h][i] for h, c in enumerate(coeff))
                for i in range(nrows)
            ]
        )
    matrix = [[columns[j][i] for j in range(2 * m)] for i in range(nrows)]
    assert all(value >= 0 for row in matrix for value in row)
    return fine, matrix


def raw_refinement_coefficients(
    ss: list[Fraction], us: list[Fraction], p: int
) -> tuple[list[Fraction], list[list[Fraction]]]:
    """The untransformed common-refinement (Marsden) coefficient matrix.

    We use normalized degree-p B-splines on the open fine knot vector.  The
    support tests use the *whole* fine B-spline support; this also makes the
    p=0 convention unambiguous.
    """
    m = len(ss)
    assert p == m - 2
    a = min(ss + us) - 1
    b = max(ss + us) + 1
    fine = [a] * (p + 1) + sorted(ss + us) + [b] * (p + 1)
    nrows = len(fine) - p - 1
    matrix = [
        [
            prod_fraction(s - fine[i + h] for h in range(1, p + 1))
            if fine[i + p + 1] <= s
            else Fraction(0)
            for s in ss
        ]
        + [
            prod_fraction(fine[i + h] - u for h in range(1, p + 1))
            if u <= fine[i]
            else Fraction(0)
            for u in us
        ]
        for i in range(nrows)
    ]
    assert all(value >= 0 for row in matrix for value in row)
    return fine, matrix


def coefficient_matrix_tn_probe() -> tuple[int, int, int]:
    """Exact evidence for the raw and DD common-refinement TN conjectures.

    The two fixed examples are exhaustive over all nonempty rectangular
    minors.  The remaining tests are deterministic exact-rational samples;
    they are evidence, not a proof for arbitrary m.
    """
    examples = [
        ([1, 4, 8], [2, 6, 10]),
        ([1, 5, 8, 13], [3, 7, 11, 15]),
    ]
    exhaustive = 0
    for raw_ss, raw_us in examples:
        ss = list(map(Fraction, raw_ss))
        us = list(map(Fraction, raw_us))
        p = len(ss) - 2
        _, raw = raw_refinement_coefficients(ss, us, p)
        _, dd = lower_refinement_coefficients(ss, us, p)
        raw_count = check_all_rectangular_minors_tn(raw)
        dd_count = check_all_rectangular_minors_tn(dd)
        assert raw_count == dd_count
        exhaustive += raw_count + dd_count

    rng = random.Random(2026081602)
    random_minors = 0
    for m in range(2, 9):
        word = rng.choice(dyck_words(m))
        value = 0
        ss: list[Fraction] = []
        us: list[Fraction] = []
        for letter in word:
            value += rng.randint(1, 17)
            (ss if letter == "S" else us).append(Fraction(value))
        _, raw = raw_refinement_coefficients(ss, us, m - 2)
        _, dd = lower_refinement_coefficients(ss, us, m - 2)
        for matrix in (raw, dd):
            nr = len(matrix)
            nc = len(matrix[0])
            for _ in range(2000):
                order = rng.randint(1, nc)
                rows = sorted(rng.sample(range(nr), order))
                cols = sorted(rng.sample(range(nc), order))
                minor = determinant(
                    [[matrix[i][j] for j in cols] for i in rows]
                )
                assert minor >= 0, (m, word, order, rows, cols, minor)
                random_minors += 1
    return exhaustive, random_minors, len(examples)


def variable_knot_chain_counterexample() -> Fraction:
    """Componentwise ordering of arbitrary knot tuples does not imply TN.

    This is deliberately away from all knot boundaries.  Degree zero
    B-splines are normalized interval indicators, so no endpoint convention
    is involved.
    """
    tuples = [[2, 32], [4, 42], [6, 54], [20, 64]]
    xs = list(map(Fraction, [7, 17, 21, 51]))
    assert all(
        tuples[j][k] < tuples[j + 1][k]
        for j in range(3)
        for k in range(2)
    )
    matrix: list[list[Fraction]] = []
    for x in xs:
        row: list[Fraction] = []
        for nodes_raw in tuples:
            nodes = list(map(Fraction, nodes_raw))
            coefficients = divided_difference_coefficients(nodes)
            row.append(
                sum(c * tp(t - x, 0) for c, t in zip(coefficients, nodes))
            )
        matrix.append(row)
    rows = (0, 2, 3)
    cols = (0, 2, 3)
    value = determinant([[matrix[i][j] for j in cols] for i in rows])
    assert value == Fraction(-1, 63360)
    return value


def minimal_lower_counterexample() -> tuple[Fraction, Fraction]:
    """The first meaningful below-threshold case: m=3, p=0."""
    xs = list(map(Fraction, [0, 3, 5, 7, 11, 14]))
    ss = list(map(Fraction, [2, 6, 8]))
    us = list(map(Fraction, [4, 10, 12]))
    below = H(xs, ss, us, 0)
    threshold = H(xs, ss, us, 1)
    assert below == -1 and threshold == 36
    return below, threshold


def check_all_rectangular_minors_tn(matrix: list[list[Fraction]]) -> int:
    nr = len(matrix)
    nc = len(matrix[0])
    count = 0
    for order in range(1, min(nr, nc) + 1):
        for rows in combinations(range(nr), order):
            for cols in combinations(range(nc), order):
                value = determinant([[matrix[i][j] for j in cols] for i in rows])
                assert value >= 0, (order, rows, cols, value)
                count += 1
    return count


def abstract_tn_pfaffian_counterexample() -> tuple[int, Fraction, Fraction, int]:
    """The proposed abstract TN/upper/rank implication is false.

    This example even has the requested support-separated factorization
    G=L R^T by paired truncated-power columns.
    """
    m = 4
    p = 1
    xs = list(map(Fraction, [0, 13, 20, 38, 60, 86, 88, 100]))
    ss = list(map(Fraction, [4, 50, 70, 83]))
    us = list(map(Fraction, [27, 66, 78, 90]))
    h_value = H(xs, ss, us, p)
    assert h_value == -9609600
    g = product_g(xs, ss, us, p)
    assert all(g[i][j] == 0 for i in range(2 * m) for j in range(i + 1))
    tn_minors = check_all_minors_tn(g)
    skew = [[g[i][j] - g[j][i] for j in range(2 * m)] for i in range(2 * m)]
    pf = pfaffian(skew)
    assert pf == (-1) ** (m * (m - 1) // 2) * h_value
    # Here binom(4,2) is even, so the conjectured fixed sign is violated.
    assert pf < 0
    return m, h_value, pf, tn_minors


SparsePolynomial = dict[tuple[int, ...], int]


def polynomial_product(a: SparsePolynomial, b: SparsePolynomial) -> SparsePolynomial:
    out: SparsePolynomial = {}
    for alpha, av in a.items():
        for beta, bv in b.items():
            exponent = tuple(x + y for x, y in zip(alpha, beta))
            out[exponent] = out.get(exponent, 0) + av * bv
    return {key: value for key, value in out.items() if value}


def linear_interval(lo: int, hi: int, gap_count: int) -> SparsePolynomial:
    if lo >= hi:
        return {}
    out: SparsePolynomial = {}
    for index in range(lo, hi):
        exponent = [0] * gap_count
        exponent[index] = 1
        out[tuple(exponent)] = 1
    return out


def permutation_sign(values: tuple[int, ...]) -> int:
    return (-1) ** sum(
        values[i] > values[j]
        for i in range(len(values))
        for j in range(i + 1, len(values))
    )


def m3_symbolic_threshold_certificate() -> tuple[int, int, int, int]:
    """Coefficientwise chamber proof of H_1>=0 at m=3.

    There are 341 chambers satisfying the necessary one-sided rank support.
    Every corresponding adjacent-gap polynomial is either zero or has only
    positive coefficients.  The remaining 4279 chambers vanish by rank.
    """
    m = 3
    total_points = 4 * m
    gap_count = total_points - 1
    zero_exp = (0,) * gap_count
    signed_perms = [
        (perm, permutation_sign(perm)) for perm in permutations(range(2 * m))
    ]
    strict = positive = zero = monomials = 0
    for word in dyck_words(m):
        knot_labels: list[tuple[str, int]] = []
        si = ui = 0
        for letter in word:
            if letter == "S":
                knot_labels.append(("S", si))
                si += 1
            else:
                knot_labels.append(("U", ui))
                ui += 1
        for x_positions_tuple in combinations(range(total_points), 2 * m):
            x_positions = set(x_positions_tuple)
            order: list[tuple[str, int]] = []
            xi = ki = 0
            for rank in range(total_points):
                if rank in x_positions:
                    order.append(("X", xi))
                    xi += 1
                else:
                    order.append(knot_labels[ki])
                    ki += 1
            pos = {label: rank for rank, label in enumerate(order)}
            xs = [pos[("X", i)] for i in range(2 * m)]
            ss = [pos[("S", i)] for i in range(m)]
            us = [pos[("U", i)] for i in range(m)]
            if not all(xs[j] < ss[j] and us[j] < xs[m + j] for j in range(m)):
                continue
            strict += 1
            matrix = [
                [linear_interval(x, s, gap_count) for s in ss]
                + [linear_interval(u, x, gap_count) for u in us]
                for x in xs
            ]
            polynomial: SparsePolynomial = {}
            for perm, sign in signed_perms:
                term: SparsePolynomial = {zero_exp: 1}
                for row, col in enumerate(perm):
                    term = polynomial_product(term, matrix[row][col])
                    if not term:
                        break
                for exponent, coefficient in term.items():
                    polynomial[exponent] = polynomial.get(exponent, 0) + sign * coefficient
                    if polynomial[exponent] == 0:
                        del polynomial[exponent]
            assert all(coefficient > 0 for coefficient in polynomial.values())
            if polynomial:
                positive += 1
                monomials += len(polynomial)
            else:
                zero += 1
    assert strict == 341
    return strict, positive, zero, monomials


def dyck_words(m: int) -> list[str]:
    out: list[str] = []

    def rec(word: str, s_count: int, u_count: int) -> None:
        if len(word) == 2 * m:
            out.append(word)
            return
        if s_count < m:
            rec(word + "S", s_count + 1, u_count)
        if u_count < s_count:
            rec(word + "U", s_count, u_count + 1)

    rec("", 0, 0)
    return out


def step_states(word: str) -> list[list[Fraction]]:
    """Rows of the p=0 matrix on successive knot-complement intervals."""
    m = len(word) // 2
    state = [Fraction(1)] * m + [Fraction(0)] * m
    states = [state[:]]
    s_count = 0
    u_count = 0
    for letter in word:
        if letter == "S":
            state[s_count] = 0
            s_count += 1
        else:
            state[m + u_count] = 1
            u_count += 1
        states.append(state[:])
    return states


def step_minor(word: str, omitted_interval: int) -> Fraction:
    states = step_states(word)
    return determinant(
        [row for i, row in enumerate(states) if i != omitted_interval]
    )


def step_minor_formula(word: str, omitted_interval: int) -> int:
    """Closed cofactor formula for the p=0 interval-state matrix."""
    m = len(word) // 2
    h = omitted_interval
    if h == 0 or h == 2 * m or word[h - 1] == word[h]:
        return 0
    circuit = 1 if word[h - 1 : h + 1] == "SU" else -1
    inversions = sum(
        1
        for i, a in enumerate(word)
        for b in word[i + 1 :]
        if a == "U" and b == "S"
    )
    return (-1) ** (m + h + inversions) * circuit


def check_step_classification(max_m: int = 8) -> dict[int, tuple[int, int, int]]:
    summary: dict[int, tuple[int, int, int]] = {}
    for m in range(1, max_m + 1):
        positive = negative = nonzero = 0
        peak_count = 0
        for word in dyck_words(m):
            peak_count += sum(
                word[h - 1 : h + 1] == "SU" for h in range(1, 2 * m)
            )
            for h in range(2 * m + 1):
                value = step_minor(word, h)
                assert value == step_minor_formula(word, h)
                assert value in (-1, 0, 1)
                positive += value > 0
                negative += value < 0
                nonzero += value != 0
        # Narayana sum: total peaks over all Dyck words.
        assert peak_count == comb(2 * m - 1, m - 1)
        summary[m] = positive, negative, nonzero
    return summary


def random_paired_instance(m: int, rng: random.Random) -> tuple[list[Fraction], list[Fraction], list[Fraction]]:
    """Random strict rational chamber with a random positive-gap metric."""
    word = rng.choice(dyck_words(m))
    labels: list[tuple[str, int]] = []
    si = ui = 0
    for letter in word:
        if letter == "S":
            labels.append(("S", si))
            si += 1
        else:
            labels.append(("U", ui))
            ui += 1
    knot_labels = labels
    x_positions = set(rng.sample(range(4 * m), 2 * m))
    labels = []
    x_index = knot_index = 0
    for position in range(4 * m):
        if position in x_positions:
            labels.append(("X", x_index))
            x_index += 1
        else:
            labels.append(knot_labels[knot_index])
            knot_index += 1
    gaps = [rng.randint(1, 13) for _ in range(4 * m - 1)]
    coordinates = [Fraction(0)]
    for gap in gaps:
        coordinates.append(coordinates[-1] + gap)
    xs = [Fraction(0)] * (2 * m)
    ss = [Fraction(0)] * m
    us = [Fraction(0)] * m
    for coordinate, (kind, index) in zip(coordinates, labels):
        if kind == "X":
            xs[index] = coordinate
        elif kind == "S":
            ss[index] = coordinate
        else:
            us[index] = coordinate
    assert xs == sorted(xs) and ss == sorted(ss) and us == sorted(us)
    assert all(s < u for s, u in zip(ss, us))
    return xs, ss, us


def randomized_threshold_sweep(
    max_m: int = 8, cases_per_m: int = 400, seed: int = 20260816
) -> tuple[dict[int, int], dict[int, tuple[int, list[int], list[int], list[int]]]]:
    rng = random.Random(seed)
    zeros: dict[int, int] = {}
    first_lower_negative: dict[int, tuple[int, list[int], list[int], list[int]]] = {}
    for m in range(2, max_m + 1):
        threshold = m - 2
        zero_count = 0
        for _ in range(cases_per_m):
            xs, ss, us = random_paired_instance(m, rng)
            value = H(xs, ss, us, threshold)
            assert value >= 0, (m, threshold, xs, ss, us, value)
            zero_count += value == 0
            if threshold > 0 and m not in first_lower_negative:
                lower = H(xs, ss, us, threshold - 1)
                if lower < 0:
                    first_lower_negative[m] = (
                        lower.numerator,
                        [int(x) for x in xs],
                        [int(s) for s in ss],
                        [int(u) for u in us],
                    )
        zeros[m] = zero_count
    return zeros, first_lower_negative


def main() -> None:
    print("p=0 step classification (positive, negative, nonzero):")
    for m, counts in check_step_classification().items():
        print(f"  m={m}: {counts}; peak sum={comb(2*m-1,m-1)}")
    zeros, counterexamples = randomized_threshold_sweep()
    print("threshold p=m-2 randomized exact sweep: PASS")
    print("zero counts:", zeros)
    print("first exact p=m-3 negatives:")
    for m, data in counterexamples.items():
        print(f"  m={m}: H={data[0]}, X={data[1]}, S={data[2]}, U={data[3]}")
    below, threshold = minimal_lower_counterexample()
    print(
        "minimal meaningful sharpness witness: "
        f"m=3, H_0={below}, H_1={threshold}"
    )
    m, h_value, pf, minor_count = abstract_tn_pfaffian_counterexample()
    print(
        "abstract TN strict-upper rank<=m Pfaffian implication: FAIL; "
        f"m={m}, H={h_value}, Pf={pf}, all {minor_count} minors of G are TN"
    )
    dd_tn, obstruction = divided_difference_tn_probe()
    print(
        "prefix-DD transformed collocation fixed-example TN probe:",
        "PASS" if dd_tn else "FAIL",
    )
    if obstruction is not None:
        print("  first obstruction:", obstruction[:5])
    exhaustive, sampled, example_count = coefficient_matrix_tn_probe()
    print(
        "raw/DD common-refinement TN evidence: PASS; "
        f"{example_count} fixed examples, {exhaustive} exhaustive minors "
        f"(raw+DD), {sampled} sampled exact minors"
    )
    variable_failure = variable_knot_chain_counterexample()
    print(
        "arbitrary componentwise knot-tuple B-spline TN shortcut: FAIL; "
        f"strict-chain 3-minor={variable_failure}"
    )
    strict, positive, zero, monomials = m3_symbolic_threshold_certificate()
    print(
        "m=3,p=1 coefficientwise all-chamber theorem: PASS; "
        f"strict-support chambers={strict}, positive={positive}, zero={zero}, "
        f"positive monomials={monomials}"
    )


if __name__ == "__main__":
    main()
