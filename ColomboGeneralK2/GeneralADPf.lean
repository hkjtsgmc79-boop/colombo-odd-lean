import ColomboGeneralK2.ADPf
import Mathlib.Data.List.Sublists

/-!
# General anti-diagonal Pfaffian minor summation

This file extends the checked `4 x 2s` gate toward arbitrary `2m x 2s`.
The first layer below packages every selected list of `m` column pairs as a
genuine square matrix, rather than as a hand-written determinant polynomial.
-/

namespace ColomboGeneralK2

section TwoColumnLaplace

variable {R : Type*} [CommRing R]

/--
Laplace expansion through the first two columns, before grouping the two row
orders into a `2 x 2` minor.  The nested submatrix removes row `i`, then row
`j` from the remaining rows, and removes columns `0`, then `1`.
-/
theorem det_twoColumnLaplace {n : Nat}
    (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :
    M.det =
      ∑ i : Fin (n + 2), (-1 : R) ^ (i : Nat) * M i 0 *
        ∑ j : Fin (n + 1), (-1 : R) ^ (j : Nat) * M (i.succAbove j) 1 *
          ((M.submatrix i.succAbove Fin.succ).submatrix j.succAbove Fin.succ).det := by
  rw [Matrix.det_succ_column_zero]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Matrix.det_succ_column_zero]
  simp only [Matrix.submatrix_apply, Fin.succ_zero_eq_one]

end TwoColumnLaplace

section SelectedPairs

variable {R I : Type*} [CommRing R]

/-- Adjacent-pair column coordinates, with induction-friendly total size `2*m`. -/
def pairColumnEquiv (m : Nat) : Fin m × Fin 2 ≃ Fin (2 * m) :=
  (finProdFinEquiv (m := m) (n := 2)).trans (finCongr (Nat.mul_comm m 2))

/--
The square matrix whose adjacent column pairs are selected by `pairs`.
`finProdFinEquiv` sends `(q, side)` to `2*q + side`, so its columns are
`L_0, R_0, ..., L_(m-1), R_(m-1)` in exactly that order.
-/
def selectedPairMatrix {m : Nat} (Z : I → Fin (2 * m) → Fin 2 → R)
    (pairs : List.Vector I m) : Matrix (Fin (2 * m)) (Fin (2 * m)) R :=
  fun row col ↦
    let qside := (pairColumnEquiv m).symm col
    Z (pairs.get qside.1) row qside.2

omit [CommRing R] in
@[simp]
theorem selectedPairMatrix_apply {m : Nat} (Z : I → Fin (2 * m) → Fin 2 → R)
    (pairs : List.Vector I m) (row col : Fin (2 * m)) :
    selectedPairMatrix Z pairs row col =
      let qside := (pairColumnEquiv m).symm col
      Z (pairs.get qside.1) row qside.2 :=
  rfl

/-- The genuine determinant belonging to a vector of exactly `m` pairs. -/
def selectedPairDet {m : Nat} (Z : I → Fin (2 * m) → Fin 2 → R)
    (pairs : List.Vector I m) : R :=
  (selectedPairMatrix Z pairs).det

/--
List-facing wrapper for `selectedPairDet`.  A list of the wrong length
contributes zero; every member of `List.sublistsLen m` takes the true branch.
-/
def selectedPairDetOfList {m : Nat} (Z : I → Fin (2 * m) → Fin 2 → R)
    (pairs : List I) : R :=
  if h : pairs.length = m then selectedPairDet Z ⟨pairs, h⟩ else 0

theorem selectedPairDetOfList_eq {m : Nat} (Z : I → Fin (2 * m) → Fin 2 → R)
    (pairs : List I) (h : pairs.length = m) :
    selectedPairDetOfList Z pairs = selectedPairDet Z ⟨pairs, h⟩ := by
  simp [selectedPairDetOfList, h]

theorem selectedPairDetOfList_ne_length {m : Nat}
    (Z : I → Fin (2 * m) → Fin 2 → R) (pairs : List I)
    (h : pairs.length ≠ m) : selectedPairDetOfList Z pairs = 0 := by
  simp [selectedPairDetOfList, h]

/-- Product of the anti-diagonal block weights selected by a pair list. -/
def selectedPairWeight (w : I → R) (pairs : List I) : R :=
  (pairs.map w).prod

/-- The determinant side of general `AD-MS`, indexed by size-`m` sublists. -/
def generalADMSRhs {m : Nat} (Z : I → Fin (2 * m) → Fin 2 → R)
    (w : I → R) (pairs : List I) : R :=
  ((pairs.sublistsLen m).map fun chosen ↦
    selectedPairWeight w chosen * selectedPairDetOfList Z chosen).sum

end SelectedPairs

section OwnerLaplaceCoordinates

variable {R I ρ : Type*}

/-- The concrete column occupied by `side` of pair `q`. -/
def pairCol (m : Nat) (q : Fin m) (side : Fin 2) : Fin (2 * m) :=
  pairColumnEquiv m (q, side)

@[simp]
theorem selectedPairMatrix_pairCol {m : Nat}
    (Z : I → Fin (2 * m) → Fin 2 → R) (pairs : List.Vector I m)
    (row : Fin (2 * m)) (q : Fin m) (side : Fin 2) :
    selectedPairMatrix Z pairs row (pairCol m q side) = Z (pairs.get q) row side := by
  simp [selectedPairMatrix, pairCol]

/-- After deleting either column of pair `h`, its mate occupies this column. -/
def reducedPairCol {n : Nat} (h : Fin (n + 1)) : Fin (2 * n + 1) :=
  ⟨2 * (h : Nat), by omega⟩

/-- Delete one selected pair while retaining the original order of all others. -/
def erasePairVector {n : Nat} (pairs : List.Vector I (n + 1))
    (h : Fin (n + 1)) : List.Vector I n :=
  List.Vector.ofFn fun q ↦ pairs.get (h.succAbove q)

@[simp]
theorem erasePairVector_get {n : Nat} (pairs : List.Vector I (n + 1))
    (h : Fin (n + 1)) (q : Fin n) :
    (erasePairVector pairs h).get q = pairs.get (h.succAbove q) := by
  simp [erasePairVector]

/-- Delete row zero and then row `k` in the remaining row order. -/
def eraseFirstPartnerRows {n : Nat}
    (Z : I → Fin (2 * (n + 1)) → Fin 2 → R) (k : Fin (2 * n + 1)) :
    I → Fin (2 * n) → Fin 2 → R :=
  fun t row side ↦ Z t (Fin.succ (k.succAbove row)) side

theorem pairCol_delete_left {n : Nat} (h : Fin (n + 1))
    (q : Fin n) (side : Fin 2) :
    (pairCol (n + 1) h 0).succAbove
        ((reducedPairCol h).succAbove (pairCol n q side)) =
      pairCol (n + 1) (h.succAbove q) side := by
  ext
  simp only [pairCol, pairColumnEquiv, Equiv.trans_apply, finCongr_apply,
    reducedPairCol]
  simp only [Fin.succAbove, Fin.lt_def]
  split_ifs <;> simp_all <;> omega

theorem pairCol_delete_right {n : Nat} (h : Fin (n + 1))
    (q : Fin n) (side : Fin 2) :
    (pairCol (n + 1) h 1).succAbove
        ((reducedPairCol h).succAbove (pairCol n q side)) =
      pairCol (n + 1) (h.succAbove q) side := by
  ext
  simp only [pairCol, pairColumnEquiv, Equiv.trans_apply, finCongr_apply,
    reducedPairCol]
  simp only [Fin.succAbove, Fin.lt_def]
  split_ifs <;> simp_all <;> omega

/-- Deleting row zero, its partner, and the left/right columns of pair `h`. -/
theorem selectedPairMatrix_owner_cofactor_left {n : Nat}
    (Z : I → Fin (2 * (n + 1)) → Fin 2 → R)
    (pairs : List.Vector I (n + 1)) (h : Fin (n + 1)) (k : Fin (2 * n + 1)) :
    ((selectedPairMatrix Z pairs).submatrix Fin.succ
        (pairCol (n + 1) h 0).succAbove).submatrix
          k.succAbove (reducedPairCol h).succAbove =
      selectedPairMatrix (eraseFirstPartnerRows Z k) (erasePairVector pairs h) := by
  ext row col
  let qside := (pairColumnEquiv n).symm col
  have hc : col = pairCol n qside.1 qside.2 := by
    change col = pairColumnEquiv n qside
    exact ((pairColumnEquiv n).apply_symm_apply col).symm
  rw [hc]
  simp only [Matrix.submatrix_apply]
  rw [pairCol_delete_left, selectedPairMatrix_pairCol, selectedPairMatrix_pairCol]
  simp [eraseFirstPartnerRows, erasePairVector]

theorem selectedPairMatrix_owner_cofactor_right {n : Nat}
    (Z : I → Fin (2 * (n + 1)) → Fin 2 → R)
    (pairs : List.Vector I (n + 1)) (h : Fin (n + 1)) (k : Fin (2 * n + 1)) :
    ((selectedPairMatrix Z pairs).submatrix Fin.succ
        (pairCol (n + 1) h 1).succAbove).submatrix
          k.succAbove (reducedPairCol h).succAbove =
      selectedPairMatrix (eraseFirstPartnerRows Z k) (erasePairVector pairs h) := by
  ext row col
  let qside := (pairColumnEquiv n).symm col
  have hc : col = pairCol n qside.1 qside.2 := by
    change col = pairColumnEquiv n qside
    exact ((pairColumnEquiv n).apply_symm_apply col).symm
  rw [hc]
  simp only [Matrix.submatrix_apply]
  rw [pairCol_delete_right, selectedPairMatrix_pairCol, selectedPairMatrix_pairCol]
  simp [eraseFirstPartnerRows, erasePairVector]

theorem pairCol_left_mate {n : Nat} (h : Fin (n + 1)) :
    (pairCol (n + 1) h 0).succAbove (reducedPairCol h) = pairCol (n + 1) h 1 := by
  ext
  simp only [pairCol, pairColumnEquiv, Equiv.trans_apply, finCongr_apply,
    reducedPairCol]
  simp only [Fin.succAbove, Fin.lt_def]
  split_ifs <;> simp_all
  all_goals omega

theorem pairCol_right_mate {n : Nat} (h : Fin (n + 1)) :
    (pairCol (n + 1) h 1).succAbove (reducedPairCol h) = pairCol (n + 1) h 0 := by
  ext
  simp only [pairCol, pairColumnEquiv, Equiv.trans_apply, finCongr_apply,
    reducedPairCol]
  simp only [Fin.succAbove, Fin.lt_def]
  split_ifs <;> simp_all

theorem pairColumnEquiv_left_mate {n : Nat} (h : Fin (n + 1)) :
    ((pairColumnEquiv (n + 1)) (h, 0)).succAbove (reducedPairCol h) =
      (pairColumnEquiv (n + 1)) (h, 1) :=
  pairCol_left_mate h

theorem pairColumnEquiv_right_mate {n : Nat} (h : Fin (n + 1)) :
    ((pairColumnEquiv (n + 1)) (h, 1)).succAbove (reducedPairCol h) =
      (pairColumnEquiv (n + 1)) (h, 0) :=
  pairCol_right_mate h

theorem selectedPairMatrix_owner_cofactor_left' {n : Nat}
    (Z : I → Fin (2 * (n + 1)) → Fin 2 → R)
    (pairs : List.Vector I (n + 1)) (h : Fin (n + 1)) (k : Fin (2 * n + 1)) :
    ((selectedPairMatrix Z pairs).submatrix Fin.succ
        ((pairColumnEquiv (n + 1)) (h, 0)).succAbove).submatrix
          k.succAbove (reducedPairCol h).succAbove =
      selectedPairMatrix (eraseFirstPartnerRows Z k) (erasePairVector pairs h) :=
  selectedPairMatrix_owner_cofactor_left Z pairs h k

theorem selectedPairMatrix_owner_cofactor_right' {n : Nat}
    (Z : I → Fin (2 * (n + 1)) → Fin 2 → R)
    (pairs : List.Vector I (n + 1)) (h : Fin (n + 1)) (k : Fin (2 * n + 1)) :
    ((selectedPairMatrix Z pairs).submatrix Fin.succ
        ((pairColumnEquiv (n + 1)) (h, 1)).succAbove).submatrix
          k.succAbove (reducedPairCol h).succAbove =
      selectedPairMatrix (eraseFirstPartnerRows Z k) (erasePairVector pairs h) :=
  selectedPairMatrix_owner_cofactor_right Z pairs h k

/-- The decomposable two-form for an arbitrary finite row type. -/
def pairWedge [CommRing R] (Z : I → ρ → Fin 2 → R) (t : I) (i j : ρ) : R :=
  Z t i 0 * Z t j 1 - Z t i 1 * Z t j 0

end OwnerLaplaceCoordinates

section OwnerLaplace

variable {R I : Type*} [CommRing R]

/--
Row-zero Laplace expansion grouped by the selected pair owning the chosen
column.  The mate column is at reduced index `2*h` after deleting either the
left or right column.  Consequently its parity contributes no `h`-dependent
sign, and the two side choices combine to the displayed wedge.
-/
theorem selectedPairDet_owner_laplace {n : Nat}
    (Z : I → Fin (2 * (n + 1)) → Fin 2 → R)
    (pairs : List.Vector I (n + 1)) :
    selectedPairDet Z pairs =
      ∑ h : Fin (n + 1), ∑ k : Fin (2 * n + 1),
        (-1 : R) ^ (k : Nat) * pairWedge Z (pairs.get h) 0 (Fin.succ k) *
          selectedPairDet (eraseFirstPartnerRows Z k) (erasePairVector pairs h) := by
  rw [selectedPairDet, Matrix.det_succ_row_zero]
  let f : Fin (2 * (n + 1)) → R := fun j ↦
    (-1 : R) ^ (j : Nat) * selectedPairMatrix Z pairs 0 j *
      ((selectedPairMatrix Z pairs).submatrix Fin.succ j.succAbove).det
  change (∑ j : Fin (2 * (n + 1)), f j) = _
  rw [← (pairColumnEquiv (n + 1)).sum_comp f]
  rw [Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro h
  rw [Fin.sum_univ_two]
  dsimp [f]
  rw [Matrix.det_succ_column _ (reducedPairCol h),
    Matrix.det_succ_column _ (reducedPairCol h)]
  simp only [Matrix.submatrix_apply]
  simp_rw [pairColumnEquiv_left_mate, pairColumnEquiv_right_mate]
  simp only [selectedPairMatrix, Equiv.symm_apply_apply]
  simp_rw [selectedPairMatrix_owner_cofactor_left',
    selectedPairMatrix_owner_cofactor_right']
  simp only [selectedPairDet]
  simp only [reducedPairCol]
  simp only [pow_add, pow_mul, neg_sq, one_pow, mul_one]
  simp only [pairWedge]
  have hsign0 : (-1 : R) ^ ((pairColumnEquiv (n + 1)) (h, 0) : Nat) = 1 := by
    simp [pairColumnEquiv, pow_mul]
  have hsign1 : (-1 : R) ^ ((pairColumnEquiv (n + 1)) (h, 1) : Nat) = -1 := by
    simp [pairColumnEquiv, pow_mul, pow_add]
  rw [hsign0, hsign1]
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  ring

end OwnerLaplace

end ColomboGeneralK2
