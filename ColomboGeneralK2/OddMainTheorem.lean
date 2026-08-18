import ColomboGeneralK2.OddCriticalSplit
import ColomboGeneralK2.OddDegreeZeroBoundary
import ColomboGeneralK2.OddVolterra
import ColomboGeneralK2.OddMVP1Endgame

/-!
# The unconditional odd Colombo theorem

This module assembles the two critical-degree bases, the exact Volterra
propagation, and the Beta--de Bruijn/Pfaffian endgame.  Its public statements
contain no paired-split, total-nonnegativity, distinctness, or target-equality
hypotheses.
-/

namespace ColomboGeneralK2.Odd

noncomputable section

/-- The paired split determinant is nonnegative at the critical degree
`m - 2` for every `m ≥ 2`.  The exceptional degree-zero case `m = 2` is
handled directly; every larger size uses the two-fan/Marsden construction and
the cross-family tie limit. -/
theorem pairedSplitNonnegative_critical {m : Nat} (hm : 2 ≤ m)
    {x : Fin (2 * m) → Real} (hx : StrictMono x) :
    PairedSplitNonnegative (m - 2) x := by
  by_cases hm2 : m = 2
  · subst m
    simpa using pairedSplitNonnegative_two_zero x hx
  · have hm3 : 3 ≤ m := by omega
    intro s u hs hu hpair
    exact criticalSplitDet_nonneg_of_three_le hm3 hx hs hu hpair

/-- Full paired split-determinant inequality: for `m ≥ 2`, every degree
`p ≥ m - 2` is nonnegative on arbitrary strictly ordered paired knot
families, including cross-family coincidences and sampled points on knots. -/
theorem pairedSplitNonnegative_of_threshold {m p : Nat}
    (hm : 2 ≤ m) (hmp : m - 2 ≤ p)
    {x : Fin (2 * m) → Real} (hx : StrictMono x) :
    PairedSplitNonnegative p x :=
  pairedSplitNonnegative_of_base
    (pairedSplitNonnegative_critical hm hx) hmp

/-- Elementwise paper-facing form of the full paired split-determinant
inequality. -/
theorem splitDet_nonnegative {m p : Nat}
    (hm : 2 ≤ m) (hmp : m - 2 ≤ p)
    {x : Fin (2 * m) → Real} (hx : StrictMono x)
    {s u : Fin m → Real} (hs : StrictMono s) (hu : StrictMono u)
    (hpair : Paired s u) :
    0 ≤ splitDet p x s u :=
  pairedSplitNonnegative_of_threshold hm hmp hx s u hs hu hpair

/-- Unconditional fixed-sign theorem for the recursive Pfaffian of the odd
power-difference matrix.  This is the Pfaffian assertion of the paper's main
theorem. -/
theorem odd_colombo_pfaffian_sign {m r : Nat}
    {x : Fin (2 * m) → Real}
    (hm : 0 < m) (hmr : m - 1 ≤ r) (hx : StrictMono x) :
    0 < groupingSign m *
      recursivePf m (powerDifference x (2 * r + 1)) := by
  by_cases hm1 : m = 1
  · subst m
    have h01 : x 0 < x 1 := hx (by decide)
    simp [groupingSign, recursivePf, powerDifference]
    exact pow_pos (sub_pos.mpr h01) _
  · have hm2 : 2 ≤ m := by omega
    have hsplit : PairedSplitNonnegative r x :=
      pairedSplitNonnegative_of_threshold hm2 (by omega) hx
    exact odd_pfaffian_sign_of_paired_split hm hmr hx hsplit

/-- Unconditional determinant-positivity theorem for every admissible odd
exponent and every strictly increasing even-sized real node list. -/
theorem odd_colombo_determinant_positive {m r : Nat}
    {x : Fin (2 * m) → Real}
    (hm : 0 < m) (hmr : m - 1 ≤ r) (hx : StrictMono x) :
    0 < (powerDifference x (2 * r + 1)).det := by
  have hsign := odd_colombo_pfaffian_sign hm hmr hx
  have hpf : recursivePf m (powerDifference x (2 * r + 1)) ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hsign
    exact (lt_irrefl 0) hsign
  exact det_pos_of_recursivePf_ne_zero _ (powerDifference_skew r x) hpf

end

end ColomboGeneralK2.Odd
