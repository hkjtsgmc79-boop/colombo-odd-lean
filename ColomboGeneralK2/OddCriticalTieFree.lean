import ColomboGeneralK2.OddMarsdenFactorization
import ColomboGeneralK2.OddBSplineCollocation
import ColomboGeneralK2.OddCriticalSplitBridge
import ColomboGeneralK2.OddTwoFanTN
import ColomboGeneralK2.OddMVP1Signatures

/-!
# Tie-free critical split determinant

Cauchy--Binet assembly of the critical case: the Marsden factorization
`H = B * C`, the maximal-minor nonnegativity of the B-spline collocation
matrix, and the total nonnegativity of the raw two-fan coefficient matrix
together give `0 ≤ splitDet (m-2) x D.s D.u` for every strictly ordered
sample vector strictly inside the anchors.
-/

open scoped BigOperators

namespace ColomboGeneralK2.Odd

/-- The determinant of a rectangular product via the maximal-minor
Cauchy--Binet formula in the natural orders. -/
theorem det_mul_cauchyBinet {r n : Nat} (B : Matrix (Fin r) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin r) ℝ) :
    (B * C).det =
      ∑ e : Fin r ↪o Fin n,
        matrixMinor B (OrderEmbedding.id _) e * matrixMinor C e (OrderEmbedding.id _) := by
  have hcb := matrixMinor_mul_cauchyBinet B C (OrderEmbedding.id _) (OrderEmbedding.id _)
  simpa [matrixMinor] using hcb

/-- The tie-free critical split determinant is nonnegative. -/
theorem criticalSplitDet_tieFree_nonneg {m : Nat} (D : TwoFanData m) (hm : 3 ≤ m)
    (x : Fin (2 * m) → ℝ) (hx : StrictMono x)
    (hinside : SamplesInsideAnchors D x) :
    0 ≤ splitDet (m - 2) x D.s D.u := by
  unfold splitDet
  have hfactor := criticalSplit_marsden_factorization D hm x hinside
  rw [hfactor]
  rw [det_mul_cauchyBinet]
  apply Finset.sum_nonneg
  intro e _
  exact mul_nonneg (bsplineCollocation_maximalMinor_nonneg D hm x hx hinside e)
    (twoFanCoefficientMatrix_tn D (2 * m) e (OrderEmbedding.id _))

end ColomboGeneralK2.Odd
