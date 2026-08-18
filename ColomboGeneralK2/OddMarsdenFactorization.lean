import ColomboGeneralK2.OddFiniteBSpline
import ColomboGeneralK2.OddTwoFanData
import ColomboGeneralK2.OddMVP1Signatures

/-!
# Marsden factorization of the critical split matrix

This module proves the exact scalar-one factorization

`splitMatrix (m-2) x D.s D.u = bsplineCollocation D x * twoFanCoefficientMatrix D`

for every two-fan datum and every sample vector strictly inside the anchors.
The left and right column identities are the one-sided truncated-power
reproductions proved in `OddFiniteBSpline`; the coefficient matrix on the
right is the raw `twoFanCoefficientMatrix D`, entry by entry.
-/

open scoped BigOperators

namespace ColomboGeneralK2.Odd

noncomputable section

/-- The two column enumerations agree on the left block. -/
theorem twoFanColumnEquiv_symm_left {m : Nat} (j : Fin m) :
    (groupedColumnEquiv m).symm (twoFanColumnEquiv m (Sum.inl j)) = Sum.inl j := by
  simp [twoFanColumnEquiv, groupedColumnEquiv]

/-- The two column enumerations agree on the right block. -/
theorem twoFanColumnEquiv_symm_right {m : Nat} (j : Fin m) :
    (groupedColumnEquiv m).symm (twoFanColumnEquiv m (Sum.inr j)) = Sum.inr j := by
  simp [twoFanColumnEquiv, groupedColumnEquiv]

/-- Left column of the split matrix against the left coefficient column. -/
theorem splitMatrix_left_col {m : Nat} (D : TwoFanData m) (hm : 3 ≤ m)
    (x : Fin (2 * m) → ℝ) (hinside : SamplesInsideAnchors D x)
    (row : Fin (2 * m)) (j : Fin m) :
    splitMatrix (m - 2) x D.s D.u row (twoFanColumnEquiv m (Sum.inl j)) =
      (bsplineCollocation D x * twoFanCoefficientMatrix D) row
        (twoFanColumnEquiv m (Sum.inl j)) := by
  have hrow := hinside row
  have hleft := paper_marsden_left D hm j (x row) hrow
  have hLHS : splitMatrix (m - 2) x D.s D.u row (twoFanColumnEquiv m (Sum.inl j)) =
      truncPow (m - 2) (D.s j - x row) := by
    simp only [splitMatrix, twoFanColumnEquiv_symm_left, leftKernel]
  rw [hLHS]
  have hcoeff : ∀ i : Fin (3 * m - 1),
      twoFanCoefficientMatrix D i (twoFanColumnEquiv m (Sum.inl j)) =
        if (i : Nat) ≤ (D.alpha j : Nat) then
          ∏ h : Fin (m - 2), (D.s j - D.openKnot (D.slideIndex i h))
        else 0 := by
    intro i
    rw [twoFanCoefficientMatrix_left_apply]
    rfl
  simp only [Matrix.mul_apply, bsplineCollocation]
  simp_rw [hcoeff]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hleft

/-- Right column of the split matrix against the right coefficient column. -/
theorem splitMatrix_right_col {m : Nat} (D : TwoFanData m) (hm : 3 ≤ m)
    (x : Fin (2 * m) → ℝ) (hinside : SamplesInsideAnchors D x)
    (row : Fin (2 * m)) (j : Fin m) :
    splitMatrix (m - 2) x D.s D.u row (twoFanColumnEquiv m (Sum.inr j)) =
      (bsplineCollocation D x * twoFanCoefficientMatrix D) row
        (twoFanColumnEquiv m (Sum.inr j)) := by
  have hrow := hinside row
  have hright := paper_marsden_right D hm j (x row) hrow
  have hLHS : splitMatrix (m - 2) x D.s D.u row (twoFanColumnEquiv m (Sum.inr j)) =
      truncPow (m - 2) (x row - D.u j) := by
    simp only [splitMatrix, twoFanColumnEquiv_symm_right, rightKernel]
  rw [hLHS]
  have hcoeff : ∀ i : Fin (3 * m - 1),
      twoFanCoefficientMatrix D i (twoFanColumnEquiv m (Sum.inr j)) =
        if m - 1 + (D.beta j : Nat) ≤ (i : Nat) then
          ∏ h : Fin (m - 2), (D.openKnot (D.slideIndex i h) - D.u j)
        else 0 := by
    intro i
    rw [twoFanCoefficientMatrix_right_apply]
    rfl
  simp only [Matrix.mul_apply, bsplineCollocation]
  simp_rw [hcoeff]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hright

/-- The exact scalar-one Marsden factorization `H = B * C` with the raw paper
coefficient matrix. -/
theorem criticalSplit_marsden_factorization {m : Nat} (D : TwoFanData m) (hm : 3 ≤ m)
    (x : Fin (2 * m) → ℝ)
    (hinside : SamplesInsideAnchors D x) :
    splitMatrix (m - 2) x D.s D.u =
      bsplineCollocation D x * twoFanCoefficientMatrix D := by
  ext row col
  rcases hcol' : (twoFanColumnEquiv m).symm col with j | j
  · have hcol : col = twoFanColumnEquiv m (Sum.inl j) := by
      rw [← hcol']
      exact ((twoFanColumnEquiv m).apply_symm_apply col).symm
    rw [hcol]
    exact splitMatrix_left_col D hm x hinside row j
  · have hcol : col = twoFanColumnEquiv m (Sum.inr j) := by
      rw [← hcol']
      exact ((twoFanColumnEquiv m).apply_symm_apply col).symm
    rw [hcol]
    exact splitMatrix_right_col D hm x hinside row j

end

end ColomboGeneralK2.Odd
