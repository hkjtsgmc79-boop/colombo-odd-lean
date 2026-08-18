# Colombo odd-exponent theorem in Lean 4

This repository contains a complete Lean 4 formalization of the odd-exponent
branch of Colombo's determinant problem for even matrix size.

For every `m ≥ 1`, every strictly increasing
`x : Fin (2 * m) → ℝ`, and every `r ≥ m - 1`, the library proves

```lean
0 < (-1 : ℝ) ^ (m.choose 2) *
  recursivePf m (powerDifference x (2 * r + 1))
```

and consequently

```lean
0 < (powerDifference x (2 * r + 1)).det
```

The public endpoints are:

- `ColomboGeneralK2.Odd.odd_colombo_pfaffian_sign`;
- `ColomboGeneralK2.Odd.odd_colombo_determinant_positive`;
- `ColomboGeneralK2.Odd.pairedSplitNonnegative_critical`;
- `ColomboGeneralK2.Odd.pairedSplitNonnegative_of_threshold`; and
- `ColomboGeneralK2.Odd.splitDet_nonnegative`.

The final assembly is in
[`ColomboGeneralK2/OddMainTheorem.lean`](ColomboGeneralK2/OddMainTheorem.lean),
and [`ColomboGeneralK2.lean`](ColomboGeneralK2.lean) is the production
umbrella.

## Verification status

- Full odd-exponent theorem: **PASS**.
- Production Lean modules: **49**.
- Production Lean source: **19,963 physical lines**
  (**20,009** including the umbrella).
- Frozen toolchain: Lean **v4.30.0**.
- Frozen dependency: mathlib **v4.30.0**, commit
  `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
- Audited source freeze in the private development repository: `d6cb9c0`.
- Final verification-report snapshot in that repository: `985771b`.

This distribution has a fresh Git history so that unrelated development files,
local paths, caches, and author-machine metadata are not published with the
formalization.

The audited build completed all **2817/2817** jobs. The production tree has no
`sorry`, `admit`, `sorryAx`, `by?`, project-local `axiom`, project-local
`opaque`, or `unsafe` declaration. Representative final theorems use only
Lean's standard logical dependencies `propext`, `Classical.choice`, and
`Quot.sound`.

See [`FULL_ODD_LEAN_REPORT.md`](FULL_ODD_LEAN_REPORT.md) for the complete
proof-gate, boundary-case, model, and verification ledger.

## Reproduce from a clean checkout

Install [Elan](https://github.com/leanprover/elan) once, then run:

```sh
git clone https://github.com/hkjtsgmc79-boop/colombo-odd-lean.git
cd colombo-odd-lean
lake update
lake exe cache get
lake build ColomboGeneralK2
```

`lean-toolchain` selects Lean v4.30.0 automatically. `lakefile.toml` pins
mathlib by exact Git commit, and the committed `lake-manifest.json` pins its
transitive dependencies. Neither `.elan` nor `.lake` belongs to the source
repository.

The finite B-spline modules may emit non-fatal linter or deprecation warnings;
the build must finish successfully.

## Repeat the trust audit

Compile the explicit kernel-axiom audit:

```sh
lake env lean Audit.lean | tee /tmp/colombo-axioms.log
python3 scripts/check_axiom_output.py /tmp/colombo-axioms.log
```

It prints the axioms of the five representative load-bearing endpoints. Each
must report exactly:

```text
[propext, Classical.choice, Quot.sound]
```

Scan the production source for forbidden placeholders and project axioms:

```sh
python3 scripts/audit_source.py
```

Run the exact finite regression guards:

```sh
python3 guards/odd_branch_beta_split_guard.py
python3 guards/odd_branch_seam_to_pfaffian_redteam.py
python3 guards/odd_branch_staircase_closure_exact.py
```

The Python programs are regression oracles for constants, signs, support
conventions, and low-dimensional anchors. They are not substitutes for the
arbitrary-`m` Lean proofs.

GitHub Actions repeats the source scan, all guards, the full Lean build, and
the axiom audit on every push and pull request.

## Repository map

- `ColomboGeneralK2/`: production Lean modules;
- `ColomboGeneralK2.lean`: production umbrella;
- `Audit.lean`: reproducible `#print axioms` audit;
- `guards/`: exact finite regression programs and their local helpers;
- `FULL_ODD_LEAN_REPORT.md`: final completion and verification report; and
- `STATUS.md`: compact theorem and trust-boundary summary.

## Mathematical scope

The repository proves the complete odd-exponent branch for matrix size
`2 * m`. It does not claim the even-exponent branch or a formalization of
every historical result cited in the accompanying manuscript.

## Citation

Citation metadata is provided in [`CITATION.cff`](CITATION.cff). For a paper,
please cite both the accompanying article and the immutable repository release
or commit used for verification.

## License

Copyright 2026 Qianli Ma.

The Lean source, Python regression programs, and repository support files are
licensed under the [Apache License 2.0](LICENSE). The accompanying article is
not distributed in this repository and is not covered by this software
license.
