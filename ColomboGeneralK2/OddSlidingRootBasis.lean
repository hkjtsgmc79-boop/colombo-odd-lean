import Mathlib.LinearAlgebra.Vandermonde

/-!
# The sliding-root basis at the small seam

This file isolates the algebraic kernel of the small-seam calculation.  The
polynomial with row index `v` uses the `B` roots strictly to the left of `v`
and the `A` roots strictly to its right.  Thus the row/column convention of
`evalMatrix` is exactly `phi_v (y_j)`.
-/

open scoped BigOperators

open Finset Matrix Polynomial

namespace ColomboGeneralK2.OddSlidingRootBasis

variable {R : Type*} [CommRing R] [Nontrivial R]

noncomputable section

/-- The monic sliding-root polynomial
`prod_{h < v} (X - B_h) * prod_{v < h} (X - A_h)`. -/
def slidingRoot (q : ℕ) (A B : ℕ → R) (v : Fin q) : R[X] :=
  (∏ h ∈ range (v : ℕ), (X - C (B h))) *
    (∏ h ∈ Ico ((v : ℕ) + 1) q, (X - C (A h)))

/-- The cross-gap product occurring in the coefficient determinant. -/
def crossGapProduct (q : ℕ) (A B : ℕ → R) : R :=
  ∏ i ∈ range q, ∏ j ∈ Ico (i + 1) q, (B i - A j)

/-- Coefficients are rows (in increasing degree) and sliding polynomials are columns. -/
def coefficientMatrix (q : ℕ) (A B : ℕ → R) : Matrix (Fin q) (Fin q) R :=
  .of fun i v ↦ (slidingRoot q A B v).coeff i

/-- Sliding polynomials are rows and evaluation points are columns. -/
def evalMatrix (q : ℕ) (A B : ℕ → R) (y : Fin q → R) : Matrix (Fin q) (Fin q) R :=
  .of fun v j ↦ (slidingRoot q A B v).eval (y j)

omit [Nontrivial R] in
theorem slidingRoot_monic (q : ℕ) (A B : ℕ → R) (v : Fin q) :
    (slidingRoot q A B v).Monic := by
  classical
  exact
    (monic_prod_of_monic (range (v : ℕ)) _ fun h _ ↦ monic_X_sub_C (B h)).mul
      (monic_prod_of_monic (Ico ((v : ℕ) + 1) q) _ fun h _ ↦ monic_X_sub_C (A h))

theorem slidingRoot_natDegree (q : ℕ) (A B : ℕ → R) (v : Fin q) :
    (slidingRoot q A B v).natDegree = q - 1 := by
  classical
  rw [slidingRoot,
    (monic_prod_of_monic (range (v : ℕ)) _
      fun h _ ↦ monic_X_sub_C (B h)).natDegree_mul
        (monic_prod_of_monic (Ico ((v : ℕ) + 1) q) _
          fun h _ ↦ monic_X_sub_C (A h))]
  simp only [natDegree_finsetProd_X_sub_C_eq_card, card_range, Nat.card_Ico]
  omega

omit [Nontrivial R] in
private theorem slidingRoot_succ_sub_castSucc {n : ℕ}
    (A B : ℕ → R) (j : Fin n) :
    slidingRoot (n + 1) A B j.succ - slidingRoot (n + 1) A B j.castSucc =
      C (A (j + 1) - B j) * slidingRoot n (fun k ↦ A (k + 1)) B j := by
  classical
  simp only [slidingRoot, Fin.val_succ, Fin.val_castSucc]
  rw [Finset.prod_range_succ,
    Finset.prod_eq_prod_Ico_succ_bot (show (j : ℕ) + 1 < n + 1 by omega)]
  have hshift :
      (∏ h ∈ Ico ((j : ℕ) + 1) n, (X - C (A (h + 1)))) =
        ∏ h ∈ Ico ((j : ℕ) + 2) (n + 1), (X - C (A h)) := by
    rw [Finset.prod_Ico_add' (f := fun h ↦ X - C (A h))
      (a := (j : ℕ) + 1) (b := n) (c := 1)]
  rw [hshift]
  simp only [map_sub]
  ring

private theorem coefficientMatrix_last_row (n : ℕ) (A B : ℕ → R)
    (v : Fin (n + 1)) :
    coefficientMatrix (n + 1) A B (Fin.last n) v = 1 := by
  rw [coefficientMatrix, Matrix.of_apply]
  have h := (slidingRoot_monic (n + 1) A B v).coeff_natDegree
  simpa [slidingRoot_natDegree] using h

private theorem det_coefficientMatrix_succ (n : ℕ) (A B : ℕ → R) :
    (coefficientMatrix (n + 1) A B).det =
      (-1 : R) ^ n *
        (∏ j : Fin n, (A ((j : ℕ) + 1) - B j)) *
          (coefficientMatrix n (fun k ↦ A (k + 1)) B).det := by
  classical
  let M := coefficientMatrix (n + 1) A B
  let W : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
    .of fun i ↦ Fin.cases (M i 0) (fun j ↦ M i j.succ - M i j.castSucc)
  have hdet : M.det = W.det := by
    apply Matrix.det_eq_of_forall_col_eq_smul_add_pred (B := W) (c := fun _ ↦ 1)
    · intro i
      simp [W]
    · intro i j
      simp [W]
  have hWdet : W.det =
      (-1 : R) ^ n * (W.submatrix Fin.castSucc Fin.succ).det := by
    rw [Matrix.det_succ_row W (Fin.last n), Finset.sum_eq_single 0 _ (by simp)]
    · simp [W, M, coefficientMatrix_last_row]
    · intro j _ hj
      obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero hj
      simp [W, M, coefficientMatrix_last_row]
  have hminor : W.submatrix Fin.castSucc Fin.succ =
      .of fun i j : Fin n ↦
        (A ((j : ℕ) + 1) - B j) *
          coefficientMatrix n (fun k ↦ A (k + 1)) B i j := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.of_apply, W, Fin.cases_succ]
    simp only [M, coefficientMatrix, Matrix.of_apply]
    rw [← coeff_sub, slidingRoot_succ_sub_castSucc]
    rw [coeff_C_mul]
    simp
  change M.det = _
  rw [hdet, hWdet, hminor, Matrix.det_mul_row]
  ring

omit [Nontrivial R] in
private theorem crossGapProduct_succ (n : ℕ) (A B : ℕ → R) :
    crossGapProduct (n + 1) A B =
      (∏ j : Fin n, (B j - A ((j : ℕ) + 1))) *
        crossGapProduct n (fun k ↦ A (k + 1)) B := by
  classical
  calc
    crossGapProduct (n + 1) A B =
        ∏ i ∈ range n, ∏ j ∈ Ico (i + 1) (n + 1), (B i - A j) := by
      rw [crossGapProduct, Finset.prod_range_succ]
      simp
    _ = ∏ i ∈ range n,
          ((B i - A (i + 1)) * ∏ j ∈ Ico (i + 2) (n + 1), (B i - A j)) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [Finset.prod_eq_prod_Ico_succ_bot (by simpa using hi)]
    _ = (∏ i ∈ range n, (B i - A (i + 1))) *
          ∏ i ∈ range n, ∏ j ∈ Ico (i + 2) (n + 1), (B i - A j) := by
      rw [Finset.prod_mul_distrib]
    _ = (∏ j : Fin n, (B j - A ((j : ℕ) + 1))) *
          crossGapProduct n (fun k ↦ A (k + 1)) B := by
      rw [Finset.prod_range]
      congr 1
      rw [crossGapProduct]
      apply Finset.prod_congr rfl
      intro i hi
      rw [Finset.prod_Ico_add' (f := fun j ↦ B i - A j)
        (a := i + 1) (b := n) (c := 1)]

/-- The coefficient determinant of the monic sliding-root basis is the
cross-gap product `prod_{i<j} (B_i - A_j)`. -/
theorem det_coefficientMatrix (q : ℕ) (A B : ℕ → R) :
    (coefficientMatrix q A B).det = crossGapProduct q A B := by
  induction q generalizing A B with
  | zero => simp [coefficientMatrix, crossGapProduct]
  | succ n ih =>
      rw [det_coefficientMatrix_succ, ih, crossGapProduct_succ]
      simp_rw [show ∀ j : Fin n,
        A ((j : ℕ) + 1) - B j = -(B j - A ((j : ℕ) + 1)) by intro j; ring]
      rw [Finset.prod_neg]
      simp only [Finset.card_univ, Fintype.card_fin]
      ring_nf
      rw [show n * 2 = 2 * n by omega, pow_mul]
      simp

/- Mathlib's
`eval_matrixOfPolynomials_eq_vandermonde_mul_matrixOfPolynomials` assumes
the `j`-th polynomial has degree at most `j`.  The same proof gives the
degree-`< q` form needed here, since every sliding polynomial has degree
`q - 1`. -/
theorem transpose_evalMatrix_eq_vandermonde_mul_coefficientMatrix
    (q : ℕ) (A B : ℕ → R) (y : Fin q → R) :
    (evalMatrix q A B y)ᵀ =
      Matrix.vandermonde y * coefficientMatrix q A B := by
  classical
  ext i j
  change (slidingRoot q A B j).eval (y i) =
    ∑ k : Fin q, y i ^ (k : ℕ) * (slidingRoot q A B j).coeff k
  have hdeg : (slidingRoot q A B j).natDegree < q := by
    rw [slidingRoot_natDegree]
    have hq : 0 < q := Nat.zero_lt_of_lt j.isLt
    omega
  have hsupp : (slidingRoot q A B j).support ⊆ range q :=
    supp_subset_range hdeg
  simp_rw [eval, eval₂]
  rw [sum_eq_of_subset _ (fun k => zero_mul ((y i) ^ k)) hsupp,
    ← Fin.sum_univ_eq_sum_range]
  congr
  ext k
  rw [RingHom.id_apply, mul_comm]

/-- Arbitrary-order sliding-root determinant, with polynomials as rows and
evaluation points as columns.  Transposition contributes no sign because a
square determinant is invariant under transpose. -/
theorem det_evalMatrix_eq_crossGapProduct_mul_det_vandermonde
    (q : ℕ) (A B : ℕ → R) (y : Fin q → R) :
    (evalMatrix q A B y).det =
      crossGapProduct q A B * (Matrix.vandermonde y).det := by
  calc
    (evalMatrix q A B y).det = (evalMatrix q A B y)ᵀ.det :=
      (Matrix.det_transpose _).symm
    _ = (Matrix.vandermonde y * coefficientMatrix q A B).det := by
      rw [transpose_evalMatrix_eq_vandermonde_mul_coefficientMatrix]
    _ = crossGapProduct q A B * (Matrix.vandermonde y).det := by
      rw [Matrix.det_mul, det_coefficientMatrix]
      ring

/-- Product form of the same determinant identity.  This fixes the
orientation as `prod_{i<j} (y_j-y_i)`, with no hidden seam sign. -/
theorem det_evalMatrix_eq_crossGapProduct_mul_vandermondeProduct
    (q : ℕ) (A B : ℕ → R) (y : Fin q → R) :
    (evalMatrix q A B y).det = crossGapProduct q A B *
      ∏ i : Fin q, ∏ j ∈ Ioi i, (y j - y i) := by
  rw [det_evalMatrix_eq_crossGapProduct_mul_det_vandermonde,
    Matrix.det_vandermonde]

section Ordered

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- The paper's strict cross ordering `A_j < B_i` for `i < j` makes every
factor in the coefficient determinant positive. -/
theorem crossGapProduct_pos (q : ℕ) (A B : ℕ → F)
    (hcross : ∀ i j : ℕ, i < j → j < q → A j < B i) :
    0 < crossGapProduct q A B := by
  rw [crossGapProduct]
  apply Finset.prod_pos
  intro i hi
  apply Finset.prod_pos
  intro j hj
  rw [sub_pos]
  exact hcross i j (by have := (Finset.mem_Ico.mp hj).1; omega)
    (Finset.mem_Ico.mp hj).2

/-- Increasing evaluation points give the positive Vandermonde orientation
`prod_{i<j} (y_j-y_i)`. -/
theorem det_vandermonde_pos {q : ℕ} {y : Fin q → F} (hy : StrictMono y) :
    0 < (Matrix.vandermonde y).det := by
  rw [Matrix.det_vandermonde]
  apply Finset.prod_pos
  intro i hi
  apply Finset.prod_pos
  intro j hj
  exact sub_pos.mpr (hy (Finset.mem_Ioi.mp hj))

/-- Strict cross ordering of the roots and strict increase of the evaluation
points make the row-polynomial/column-point determinant positive. -/
theorem det_evalMatrix_pos (q : ℕ) (A B : ℕ → F) (y : Fin q → F)
    (hcross : ∀ i j : ℕ, i < j → j < q → A j < B i)
    (hy : StrictMono y) :
    0 < (evalMatrix q A B y).det := by
  rw [det_evalMatrix_eq_crossGapProduct_mul_det_vandermonde]
  exact mul_pos (crossGapProduct_pos q A B hcross) (det_vandermonde_pos hy)

end Ordered

end

end ColomboGeneralK2.OddSlidingRootBasis
