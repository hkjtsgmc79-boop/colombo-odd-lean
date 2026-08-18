# Colombo `k = 2` Lean status

Status: **ODD-EXPONENT BRANCH COMPLETE / FULL BUILD PASS**.

The production umbrella `ColomboGeneralK2.lean` contains an unconditional
Lean proof of the odd-exponent theorem stated in the accompanying paper.

## Public endpoints

For arbitrary `m`, `r`, and strictly increasing real nodes, the production
library proves:

- `Odd.pairedSplitNonnegative_critical`: the critical degree `m - 2` for
  every `m ≥ 2`;
- `Odd.pairedSplitNonnegative_of_threshold`: every degree `p ≥ m - 2`;
- `Odd.splitDet_nonnegative`: the elementwise paired split-determinant
  theorem, including cross-family coincidences and sampled knots;
- `Odd.odd_colombo_pfaffian_sign`: for `m ≥ 1` and `r ≥ m - 1`,
  `0 < (-1)^(m.choose 2) * recursivePf(...)`; and
- `Odd.odd_colombo_determinant_positive`: strict positivity of the odd
  power-difference determinant under the same assumptions.

## Boundary ledger

- `m = 1`: direct recursive-Pfaffian evaluation.
- `m = 2`: direct degree-zero strict-step enumeration; equality with a knot
  and the allowed off-diagonal cross-family tie are included.
- `m ≥ 3`, all knots distinct: exact sorting into `TwoFanData`, followed by
  the B-spline/Marsden/two-fan total-nonnegativity chain.
- `m ≥ 3`, cross-family ties: common positive right shift and continuity at
  the positive critical exponent.
- `p > m - 2`: exact Volterra propagation with coefficient `p^(2*m)` and no
  factorial.

## Trust boundary

The full odd theorem uses no `sorry`, `admit`, project-local `axiom`, or
project-local `opaque` declaration. Representative final `#print axioms`
commands report only `propext`, `Classical.choice`, and `Quot.sound`.

The exact Python guards verify finite sign and normalization anchors, but are
not used as arbitrary-rank proofs.

The even-exponent branch and a complete formalization of every historical
result discussed in the paper are outside this status claim. The older
AD-MS/complementary-minor/concrete-P4 modules remain available and unchanged
as a separate line of infrastructure.

See `README.md` for build instructions and `FULL_ODD_LEAN_REPORT.md` for the
complete verification record.
