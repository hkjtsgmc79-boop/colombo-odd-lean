import Mathlib

/-!
# Odd-exponent branch of Colombo's determinant problem

In his 1928 ICM communication, B. Colombo asked whether the determinant of
the matrix of powers of pairwise differences is nonzero in the expected
degree range.  The theorem below is the odd-exponent branch for even matrix
size, stated using only Mathlib notions.
-/

namespace ColomboPalomar

/-- For strictly increasing real nodes of even cardinality, every admissible
odd power-difference determinant is strictly positive. -/
theorem odd_colombo_determinant_positive {m r : Nat}
    {x : Fin (2 * m) → Real}
    (hm : 0 < m) (hmr : m - 1 ≤ r) (hx : StrictMono x) :
    0 < Matrix.det
      (fun i j : Fin (2 * m) ↦ (x j - x i) ^ (2 * r + 1)) := by
  sorry

end ColomboPalomar
