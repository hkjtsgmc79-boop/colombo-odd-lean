import ColomboGeneralK2.OddBetaDeBruijn
import ColomboGeneralK2.OddCentralSimplex
import ColomboGeneralK2.OddCentralStrictness
import ColomboGeneralK2.OddPairedSplitLimit
import ColomboGeneralK2.OddPfaffianSquare

/-!
# Conditional odd-branch MVP-1 endgame

The paired-split statement remains the sole explicit mathematical input.
This file derives diagonal nonnegativity, strict positivity on a positive-
measure central simplex, the signed recursive-Pfaffian inequality, and its
frozen target.  No total-nonnegativity or propagation theorem is assumed
under another name.
-/

namespace ColomboGeneralK2.Odd

open MeasureTheory

noncomputable section

/-- The grouped Beta determinant is integrable on the labelled full domain. -/
theorem groupedSplitMatrix_det_integrable {m : Nat} (r : Nat)
    (x : Fin (2 * m) → Real) :
    Integrable (fun t : Fin m → Real ↦
      (groupedSplitMatrix r x t).det) (tupleVolume m) := by
  have hselected : Integrable
      (fun t : Fin m → Real ↦
        (selectedPairMatrix (betaColumns r x) (List.Vector.ofFn t)).det)
      (tupleVolume m) := by
    simpa [selectedPairDet] using
      selectedPairDet_ofFn_integrable volume (betaColumns r x)
        (betaColumns_pairIntegrable r x)
  have hscaled := hselected.const_mul (groupingSign m)
  simpa only [groupedSplitMatrix, groupedPairMatrix_det, groupingSign] using hscaled

/-- The explicit paired-split argument makes the ordered chamber integral
nonnegative after closing the split onto the diagonal. -/
theorem ordered_split_integral_nonnegative {m : Nat} (r : Nat)
    (x : Fin (2 * m) → Real) :
    OrderedSplitIntegralNonnegativeTarget r x := by
  intro hSplit
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem (measurableSet_orderedChamber m)] with t ht
  exact hSplit.groupedSplitMatrix_det_nonnegative ht

/-- The exact signed recursive Pfaffian is strictly positive, conditional
only on the paper's paired-split theorem argument. -/
theorem odd_pfaffian_sign_of_paired_split {m r : Nat}
    {x : Fin (2 * m) → Real}
    (hm : 0 < m) (hmr : m - 1 ≤ r) (hx : StrictMono x)
    (hSplit : PairedSplitNonnegative r x) :
    0 < groupingSign m *
      recursivePf m (powerDifference x (2 * r + 1)) := by
  have hintegral :
      0 < ∫ t in orderedChamber m,
        (groupedSplitMatrix r x t).det ∂tupleVolume m := by
    apply orderedChamber_integral_pos_of_central hm hx
      (fun t : Fin m → Real ↦ (groupedSplitMatrix r x t).det)
      (groupedSplitMatrix_det_integrable r x)
    · intro t ht
      exact hSplit.groupedSplitMatrix_det_nonnegative ht
    · intro t ht
      exact central_split_strict hm hmr hx ht
  rw [colombo_ordered_beta_debruijn_unconditional r x]
  exact mul_pos (pow_pos (by
    simp only [betaConstant]
    positivity) m) hintegral

/-- The frozen conditional Pfaffian-sign target is discharged. -/
theorem odd_pfaffian_sign_target {m r : Nat}
    (x : Fin (2 * m) → Real) :
    OddPfaffianSignTarget r x := by
  intro hm hmr hx hSplit
  exact odd_pfaffian_sign_of_paired_split hm hmr hx hSplit

/-- The odd power-difference determinant is strictly positive under the same
single paired-split input. -/
theorem odd_determinant_positive_of_paired_split {m r : Nat}
    {x : Fin (2 * m) → Real}
    (hm : 0 < m) (hmr : m - 1 ≤ r) (hx : StrictMono x)
    (hSplit : PairedSplitNonnegative r x) :
    0 < (powerDifference x (2 * r + 1)).det := by
  exact oddDeterminantPositive_of_pfaffianSign r x
    (odd_pfaffian_sign_target x) hm hmr hx hSplit

/-- The frozen conditional determinant-positivity target is discharged. -/
theorem odd_determinant_positive_target {m r : Nat}
    (x : Fin (2 * m) → Real) :
    OddDeterminantPositiveTarget r x :=
  oddDeterminantPositive_of_pfaffianSign r x
    (odd_pfaffian_sign_target x)

end

end ColomboGeneralK2.Odd
