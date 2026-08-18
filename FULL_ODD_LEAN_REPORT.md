# Full odd-branch Lean completion report

## Verdict

**PASS.** Development snapshot `d6cb9c0` is the audited source freeze for the
unconditional odd-exponent theorem in the accompanying paper. This standalone
distribution has a fresh Git history; the proof sources are byte-for-byte the
sources from that audited snapshot.

For arbitrary `m`, `r`, and `x`, Lean proves:

```lean
theorem odd_colombo_pfaffian_sign {m r : Nat}
    {x : Fin (2 * m) → Real}
    (hm : 0 < m) (hmr : m - 1 ≤ r) (hx : StrictMono x) :
    0 < groupingSign m *
      recursivePf m (powerDifference x (2 * r + 1))

theorem odd_colombo_determinant_positive {m r : Nat}
    {x : Fin (2 * m) → Real}
    (hm : 0 < m) (hmr : m - 1 ≤ r) (hx : StrictMono x) :
    0 < (powerDifference x (2 * r + 1)).det
```

Here `groupingSign m = (-1 : Real) ^ (m.choose 2)` and
`powerDifference x D i j = (x j - x i)^D`, exactly matching the paper.

## Development source lineage

The identifiers below record the private development audit trail. They are
provenance labels, not commits in this standalone repository's fresh history.

| Commit | Result |
|---|---|
| `d07f3e2` | audited MVP-2 checkpoint |
| `b02a798` | DSH finite B-spline/Marsden layer |
| `5455b58` | DSH metadata and report correction |
| `4e76752` | direct `m = 2`, degree-zero boundary |
| `3a874da` | exact arbitrary-size Volterra propagation |
| `e892622` | arbitrary `m ≥ 3` critical split and cross-tie closure |
| `d6cb9c0` | unconditional main theorem, umbrella, and status update |

All unrelated pre-existing untracked user files were left untouched. Neither
`.elan` nor `.lake` is tracked.

## Completed proof gates

| Gate | Public evidence | Status |
|---|---|---|
| finite B-spline/Marsden critical layer | `criticalSplit_marsden_factorization`, `criticalSplitDet_tieFree_nonneg` | PASS |
| `m = 2`, `p = 0` boundary | `criticalSplitDet_two_zero_nonneg`, `pairedSplitNonnegative_two_zero` | PASS |
| arbitrary distinct critical knots, `m ≥ 3` | `criticalSplitDet_distinct_nonneg` | PASS |
| arbitrary cross-family ties | `criticalSplitDet_nonneg_of_three_le` | PASS |
| exact Volterra recurrence | `splitDet_volterra`, coefficient `p^(2*m)`, no `m!` | PASS |
| all degrees `p ≥ m - 2` | `pairedSplitNonnegative_of_threshold`, `splitDet_nonnegative` | PASS |
| Beta--de Bruijn and central strictness | `odd_pfaffian_sign_of_paired_split` with its input now discharged | PASS |
| Pfaffian square and determinant | `odd_colombo_pfaffian_sign`, `odd_colombo_determinant_positive` | PASS |

The final interfaces contain no total-nonnegativity, paired-split,
cross-family-distinctness, sample-avoidance, or target-equality hypothesis.

## Boundary coverage

- `m = 1` is evaluated directly from the recursive Pfaffian and
  `x 0 < x 1`.
- `m = 2` uses a strict-step `4 × 4` determinant. The kernel-level finite
  core checks all `5^4 = 625` cut patterns; 105 are admissible and none has a
  negative determinant. Samples equal to knots and the allowed off-diagonal
  cross-family tie are included.
- `m ≥ 3` first sorts cross-distinct knots into an exact `TwoFanData`
  realization. A common positive shift of the right family removes the
  finitely many possible cross ties, and positive-exponent continuity closes
  the limit.
- Volterra propagation includes the first `p = 0 → 1` step and every later
  degree.

## Verification environment

- Lean `v4.30.0`
- mathlib tag `v4.30.0`, commit
  `c5ea00351c28e24afc9f0f84379aa41082b1188f`
- local project toolchain used without changing the pinned versions

The following all passed:

1. targeted source compilation of every new production module;
2. `lake build ColomboGeneralK2`;
3. the production placeholder/project-axiom scan;
4. representative `#print axioms` checks;
5. three exact regression guards; and
6. independent semantic red-team reviews of the DSH layer, degree-zero
   boundary, critical tie closure, Volterra recurrence, and final main chain.

The final full build completed **2817/2817 jobs**. It replayed non-fatal
deprecation and linter warnings in the DSH finite B-spline modules; there were
no build errors.

## Kernel axiom audit

Each of the following reports exactly
`[propext, Classical.choice, Quot.sound]`:

```text
pairedSplitNonnegative_critical
pairedSplitNonnegative_of_threshold
splitDet_nonnegative
odd_colombo_pfaffian_sign
odd_colombo_determinant_positive
```

The audited production tree contains no `sorry`, `admit`, `sorryAx`, `by?`,
project-local `axiom`, project-local `opaque`, or `unsafe` declaration.

## Exact regression guards

The final run reported:

- Beta/split-knot ledger: PASS;
- seam-to-Pfaffian red team: PASS; and
- staircase closure end-to-end guard: PASS.

Among their checks were 69 Beta constants, 6860 support/pairing implications,
6254 audited TN minors, 3920 step-kernel support implications, direct odd
Pfaffian signs, and the explicit statement that ordered Volterra
antisymmetrization has no `m!`.

These scripts are regression oracles only. Arbitrary-`m` claims are proved in
Lean.

## Size

- production Lean modules: 49;
- production Lean source: 19,963 physical lines;
- top-level declaration lines counted by the audit regex: 1,121;
- DSH spline/Marsden layer: 4,001 lines / 164 declarations;
- final closure added after DSH: 1,548 lines / 87 declaration lines:
  - `OddCriticalSplit.lean`: 309 / 15;
  - `OddDegreeZeroBoundary.lean`: 216 / 9;
  - `OddVolterra.lean`: 937 / 57;
  - `OddMainTheorem.lean`: 86 / 6.

## Agent/model ledger

- DSH external coding session: DeepSeek-V4-Pro Max, approximately 47
  compile-repair rounds, delivered `b02a798`.
- degree-zero implementation and Volterra implementation: dedicated Lean
  agents inheriting the main-session model; each received a separate
  `gpt-5.5 high` semantic red team.
- critical split closure: a failed/stale initial attempt was not accepted;
  the completed takeover used `gpt-5.6-sol xhigh`, followed by an independent
  `gpt-5.5 high` semantic red team.
- final assembly: primary owner, followed by an independent `gpt-5.5 high`
  end-to-end semantic red team.

Exact per-agent token metering is not exposed by the local Lean/Git audit, so
this report does not invent token totals. The model/task/acceptance ledger is
recorded instead.

## Paper-to-Lean coverage note

The paper describes the Volterra step determinant as equal to one
"precisely" on a full interlacing chain. Lean proves the `0`-or-`1` result and
the nonzero-support implications `a_i < s_i` and `u_i < b_i`, which are the
directions needed to prove pairedness and the recurrence. The unused reverse
direction of that descriptive biconditional is not separately exposed as a
theorem. Independent review found no consequence for the main result.

The paper writes `Pf`; Lean uses the project's `recursivePf`. The library
also proves agreement with the ordered-list Pfaffian recursion and the
skew-matrix determinant-square identity.

## Reproduce

From the repository root:

```sh
lake update
lake exe cache get
lake build ColomboGeneralK2
```

Regression guards:

```sh
python3 guards/odd_branch_beta_split_guard.py
python3 guards/odd_branch_seam_to_pfaffian_redteam.py
python3 guards/odd_branch_staircase_closure_exact.py
```

The repository includes exact version pins, a reproducible axiom audit, and
continuous-integration checks. Build caches and local toolchains are excluded.

## Scope boundary

This PASS is for the complete odd-exponent branch for even matrix size
`2 * m`. It does not claim the even-exponent branch or a formalization of
every historical theorem cited in the article.
