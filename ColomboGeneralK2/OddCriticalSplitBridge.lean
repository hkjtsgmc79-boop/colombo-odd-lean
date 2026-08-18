import ColomboGeneralK2.OddSeparatedPowers
import ColomboGeneralK2.OddStaircaseSupport

/-!
# Cauchy--Binet bridge for the critical split

This is the load-bearing algebraic interface between the two factors arising
at the critical split and the raw coefficient matrix.  It is deliberately
rectangular: the intermediate dimension is arbitrary, and selected minors
are indexed by the increasing finite-ordinal embeddings used throughout the
odd-branch development.

No positivity assertion about the product is assumed.  It is obtained by the
finite Cauchy--Binet formula from total nonnegativity of the two factors.
-/

open scoped BigOperators

namespace ColomboGeneralK2.Odd

/-- Taking selected rows and columns commutes with the matrix product, with
the full intermediate finite ordinal retained. -/
theorem submatrix_mul_eq_mul_submatrix
    {r n c k : Nat} (B : Matrix (Fin r) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin c) ℝ)
    (rows : Fin k ↪o Fin r) (cols : Fin k ↪o Fin c) :
    (B * C).submatrix rows cols =
      (B.submatrix rows id) * (C.submatrix id cols) := by
  ext i j
  simp [Matrix.mul_apply]

/-- Cauchy--Binet written directly for an arbitrary selected minor of a
rectangular product. -/
theorem matrixMinor_mul_cauchyBinet
    {r n c k : Nat} (B : Matrix (Fin r) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin c) ℝ)
    (rows : Fin k ↪o Fin r) (cols : Fin k ↪o Fin c) :
    matrixMinor (B * C) rows cols =
      ∑ middle : Fin k ↪o Fin n,
        matrixMinor B rows middle * matrixMinor C middle cols := by
  rw [matrixMinor, submatrix_mul_eq_mul_submatrix,
    OddSeparatedPowers.rectangular_det_mul]
  rfl

/-- The arbitrary-size critical Cauchy--Binet bridge: if both factors have
nonnegative increasing minors, then every increasing minor of their product
is nonnegative. -/
theorem matrixMinor_mul_nonneg
    {r n c k : Nat} (B : Matrix (Fin r) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin c) ℝ)
    (hB : IsTotallyNonnegative B) (hC : IsTotallyNonnegative C)
    (rows : Fin k ↪o Fin r) (cols : Fin k ↪o Fin c) :
    0 ≤ matrixMinor (B * C) rows cols := by
  rw [matrixMinor_mul_cauchyBinet]
  apply Finset.sum_nonneg
  intro middle _
  exact mul_nonneg (hB k rows middle) (hC k middle cols)

/-- Total nonnegativity is closed under a rectangular matrix product. -/
theorem isTotallyNonnegative_mul
    {r n c : Nat} (B : Matrix (Fin r) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin c) ℝ)
    (hB : IsTotallyNonnegative B) (hC : IsTotallyNonnegative C) :
    IsTotallyNonnegative (B * C) := by
  intro k rows cols
  exact matrixMinor_mul_nonneg B C hB hC rows cols

/-- The exact rectangular Marsden bridge: an explicitly supplied
factorization `H = B * C` and TN certificates for the two factors imply TN
of `H`.  In the odd branch the dimensions specialize to
`r = c = 2*m` and `n = 3*m-1`. -/
theorem criticalSplit_isTotallyNonnegative_rectangular
    {r n c : Nat} (H : Matrix (Fin r) (Fin c) ℝ)
    (B : Matrix (Fin r) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin c) ℝ)
    (hfactor : H = B * C)
    (hB : IsTotallyNonnegative B) (hC : IsTotallyNonnegative C) :
    IsTotallyNonnegative H := by
  rw [hfactor]
  exact isTotallyNonnegative_mul B C hB hC

/-- Paper-sized determinant specialization of the rectangular Marsden
bridge.  The intermediate dimension is exactly `3*m-1`, while both the
split matrix and its determinant have order `2*m`. -/
theorem criticalSplit_determinant_nonnegative {m : Nat}
    (H : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ)
    (B : Matrix (Fin (2 * m)) (Fin (3 * m - 1)) ℝ)
    (C : Matrix (Fin (3 * m - 1)) (Fin (2 * m)) ℝ)
    (hfactor : H = B * C)
    (hB : IsTotallyNonnegative B) (hC : IsTotallyNonnegative C) :
    0 ≤ H.det := by
  have hH := criticalSplit_isTotallyNonnegative_rectangular H B C hfactor hB hC
  have hfull := hH (2 * m) (OrderEmbedding.id _) (OrderEmbedding.id _)
  simpa [matrixMinor] using hfull

/-- Square form used by the critical split.  The equality `H = B * C` is the
explicit algebraic output of the split; total nonnegativity of `H` is a
conclusion, not a hypothesis. -/
theorem criticalSplit_matrixMinor_nonneg
    {n k : Nat} (H B C : Matrix (Fin n) (Fin n) ℝ)
    (hfactor : H = B * C)
    (hB : IsTotallyNonnegative B) (hC : IsTotallyNonnegative C)
    (rows cols : Fin k ↪o Fin n) :
    0 ≤ matrixMinor H rows cols := by
  rw [hfactor]
  exact matrixMinor_mul_nonneg B C hB hC rows cols

/-- A square critical split packages the previous minor-wise conclusion as
total nonnegativity of the resulting raw matrix. -/
theorem criticalSplit_isTotallyNonnegative
    {n : Nat} (H B C : Matrix (Fin n) (Fin n) ℝ)
    (hfactor : H = B * C)
    (hB : IsTotallyNonnegative B) (hC : IsTotallyNonnegative C) :
    IsTotallyNonnegative H := by
  intro k rows cols
  exact criticalSplit_matrixMinor_nonneg H B C hfactor hB hC rows cols

end ColomboGeneralK2.Odd
