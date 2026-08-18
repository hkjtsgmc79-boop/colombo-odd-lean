import ColomboGeneralK2.OddMVP1Signatures
import ColomboGeneralK2.OddSeparatedPowers

/-!
# Strict positivity in the central split chamber

In the central chamber, the grouped split matrix has two separated-power
diagonal blocks.  Reindexing rows by the same grouped equivalence used for
the columns puts those blocks in the standard order, so no permutation sign
is introduced.
-/

namespace ColomboGeneralK2.Odd

open scoped BigOperators

noncomputable section

/-- In the central simplex, simultaneous row and column grouping exposes the
two separated-power blocks.  The off-diagonal blocks vanish because each
central knot lies strictly between the two halves of `x`. -/
private theorem groupedSplitMatrix_grouped_blocks
    {m r : Nat} {x : Fin (2 * m) → Real} {t : Fin m → Real}
    (ht : t ∈ centralSimplex x) :
    (groupedSplitMatrix r x t).submatrix (groupedColumnEquiv m)
        (groupedColumnEquiv m) =
      Matrix.fromBlocks
        (Matrix.of fun i j ↦
          (t j - x (groupedColumnEquiv m (Sum.inl i))) ^ r)
        0 0
        (Matrix.of fun i j ↦
          (x (groupedColumnEquiv m (Sum.inr i)) - t j) ^ r) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp only [Matrix.submatrix_apply, groupedSplitMatrix, groupedPairMatrix,
      Equiv.symm_apply_apply, betaColumns_zero, Matrix.fromBlocks_apply₁₁,
      Matrix.of_apply]
    rw [leftKernel, truncPow_of_pos (by linarith [(ht.2 i j).1])]
  · simp only [Matrix.submatrix_apply, groupedSplitMatrix, groupedPairMatrix,
      Equiv.symm_apply_apply, betaColumns_one, Matrix.fromBlocks_apply₁₂]
    change rightKernel r x (t _) (groupedColumnEquiv m (Sum.inl _)) = 0
    rw [rightKernel, truncPow_of_nonpos]
    linarith [(ht.2 i j).1]
  · simp only [Matrix.submatrix_apply, groupedSplitMatrix, groupedPairMatrix,
      Equiv.symm_apply_apply, betaColumns_zero, Matrix.fromBlocks_apply₂₁]
    change leftKernel r x (t _) (groupedColumnEquiv m (Sum.inr _)) = 0
    rw [leftKernel, truncPow_of_nonpos]
    linarith [(ht.2 i j).2]
  · simp only [Matrix.submatrix_apply, groupedSplitMatrix, groupedPairMatrix,
      Equiv.symm_apply_apply, betaColumns_one, Matrix.fromBlocks_apply₂₂,
      Matrix.of_apply]
    rw [rightKernel, truncPow_of_pos (by linarith [(ht.2 i j).2])]

/-- The grouped split determinant is strictly positive in the central
simplex.  Grouping the first and last `m` rows with the already-grouped
columns is a simultaneous reindexing, hence contributes no sign. -/
theorem central_split_strict {m r : Nat} {x : Fin (2 * m) → Real}
    {t : Fin m → Real} (_hm : 0 < m) (hmr : m - 1 ≤ r)
    (hx : StrictMono x) (ht : t ∈ centralSimplex x) :
    0 < (groupedSplitMatrix r x t).det := by
  let y : Fin m → Real := fun i ↦ x (groupedColumnEquiv m (Sum.inl i))
  let w : Fin m → Real := fun i ↦ x (groupedColumnEquiv m (Sum.inr i))
  have hy : StrictMono y := by
    intro i j hij
    dsimp [y]
    apply hx
    simpa [groupedColumnEquiv, finSumFinEquiv] using hij
  have hw : StrictMono w := by
    intro i j hij
    dsimp [w]
    apply hx
    simpa [groupedColumnEquiv, finSumFinEquiv] using hij
  have hleft : 0 <
      (Matrix.of fun i j ↦
        (t j - x (groupedColumnEquiv m (Sum.inl i))) ^ r :
        Matrix (Fin m) (Fin m) Real).det := by
    simpa [y] using
      OddSeparatedPowers.separatedPowers_det_pos hy ht.1
        (fun i j ↦ (ht.2 i j).1) hmr
  have hright : 0 <
      (Matrix.of fun i j ↦
        (x (groupedColumnEquiv m (Sum.inr i)) - t j) ^ r :
        Matrix (Fin m) (Fin m) Real).det := by
    simpa [w] using
      OddSeparatedPowers.rightSeparatedPowers_det_pos ht.1 hw
        (fun i j ↦ (ht.2 j i).2) hmr
  have hdet : (groupedSplitMatrix r x t).det =
      (Matrix.of fun i j ↦
        (t j - x (groupedColumnEquiv m (Sum.inl i))) ^ r :
        Matrix (Fin m) (Fin m) Real).det *
      (Matrix.of fun i j ↦
        (x (groupedColumnEquiv m (Sum.inr i)) - t j) ^ r :
        Matrix (Fin m) (Fin m) Real).det := by
    rw [← Matrix.det_submatrix_equiv_self (groupedColumnEquiv m),
      groupedSplitMatrix_grouped_blocks ht, Matrix.det_fromBlocks_zero₂₁]
  rw [hdet]
  exact mul_pos hleft hright

/-- The frozen central strictness target is discharged by
`central_split_strict`. -/
theorem central_split_strict_target {m r : Nat} {x : Fin (2 * m) → Real}
    (hm : 0 < m) (hmr : m - 1 ≤ r) (hx : StrictMono x) :
    CentralSplitStrictTarget r x := by
  intro t ht
  exact central_split_strict hm hmr hx ht

/-- Camel-case spelling of the central strictness target theorem. -/
theorem centralSplitStrictTarget {m r : Nat} {x : Fin (2 * m) → Real}
    (hm : 0 < m) (hmr : m - 1 ≤ r) (hx : StrictMono x) :
    CentralSplitStrictTarget r x :=
  central_split_strict_target hm hmr hx

end

end ColomboGeneralK2.Odd
