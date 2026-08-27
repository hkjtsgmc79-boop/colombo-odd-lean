import ColomboGeneralK2.OddMainTheorem

/-!
# Solution to the Palomar challenge

This module exposes the paper's main determinant theorem with exactly the
same Mathlib-only statement as `Challenge.lean`.  The proof delegates to the
fully formalized spline, total-positivity, Volterra, and Pfaffian development
in `ColomboGeneralK2`.
-/

namespace ColomboPalomar

theorem odd_colombo_determinant_positive {m r : Nat}
    {x : Fin (2 * m) → Real}
    (hm : 0 < m) (hmr : m - 1 ≤ r) (hx : StrictMono x) :
    0 < Matrix.det
      (fun i j : Fin (2 * m) ↦ (x j - x i) ^ (2 * r + 1)) := by
  simpa [ColomboGeneralK2.Odd.powerDifference] using
    ColomboGeneralK2.Odd.odd_colombo_determinant_positive hm hmr hx

end ColomboPalomar
