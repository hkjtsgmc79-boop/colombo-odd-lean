import ColomboGeneralK2.OddDeBruijnSignatures
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.GroupTheory.Perm.Fin

/-!
# The odd de Bruijn column shuffle

This file compares the adjacent-pair column order
`[L₀, R₀, ..., Lₘ₋₁, Rₘ₋₁]` used by `selectedPairMatrix` with the
paper-facing grouped order `[L₀, ..., Lₘ₋₁, R₀, ..., Rₘ₋₁]`.
-/

namespace ColomboGeneralK2

open scoped BigOperators

noncomputable section

/-- Grouped left/right coordinates, enumerated with every left coordinate first. -/
def groupedPairColumnEquiv (m : Nat) : Fin m ⊕ Fin m ≃ Fin (2 * m) :=
  Odd.groupedColumnEquiv m

@[simp]
theorem groupedPairColumnEquiv_left_val (m : Nat) (q : Fin m) :
    ((groupedPairColumnEquiv m (Sum.inl q) : Fin (2 * m)) : Nat) = q := by
  simp [groupedPairColumnEquiv, Odd.groupedColumnEquiv]

@[simp]
theorem groupedPairColumnEquiv_right_val (m : Nat) (q : Fin m) :
    ((groupedPairColumnEquiv m (Sum.inr q) : Fin (2 * m)) : Nat) = q + m := by
  simp [groupedPairColumnEquiv, Odd.groupedColumnEquiv]

/-- Change a grouped left/right coordinate into an adjacent-pair coordinate. -/
def sumSideEquiv (m : Nat) : Fin m ⊕ Fin m ≃ Fin m × Fin 2 where
  toFun
    | Sum.inl q => (q, 0)
    | Sum.inr q => (q, 1)
  invFun qside := if qside.2 = 0 then Sum.inl qside.1 else Sum.inr qside.1
  left_inv x := by rcases x with q | q <;> simp
  right_inv qside := by
    rcases qside with ⟨q, side⟩
    fin_cases side <;> simp

@[simp]
theorem sumSideEquiv_inl (m : Nat) (q : Fin m) :
    sumSideEquiv m (Sum.inl q) = (q, 0) :=
  rfl

@[simp]
theorem sumSideEquiv_inr (m : Nat) (q : Fin m) :
    sumSideEquiv m (Sum.inr q) = (q, 1) :=
  rfl

@[simp]
private theorem finSumFinEquiv_symm_apply_addNat_self (m : Nat) (q : Fin m) :
    (@finSumFinEquiv m m).symm (q.addNat m) = Sum.inr q := by
  rw [show q.addNat m = Fin.natAdd m q by
    ext
    simp [Nat.add_comm]]
  exact finSumFinEquiv_symm_apply_natAdd q

/-- The perfect shuffle sending a grouped column position to its source in the
adjacent-pair ordering. -/
def perfectShufflePerm (m : Nat) : Equiv.Perm (Fin (2 * m)) :=
  ((groupedPairColumnEquiv m).symm.trans (sumSideEquiv m)).trans
    (pairColumnEquiv m)

@[simp]
theorem perfectShufflePerm_grouped_left (m : Nat) (q : Fin m) :
    perfectShufflePerm m (groupedPairColumnEquiv m (Sum.inl q)) =
      pairColumnEquiv m (q, 0) := by
  simp [perfectShufflePerm]

@[simp]
theorem perfectShufflePerm_grouped_right (m : Nat) (q : Fin m) :
    perfectShufflePerm m (groupedPairColumnEquiv m (Sum.inr q)) =
      pairColumnEquiv m (q, 1) := by
  simp [perfectShufflePerm]

@[simp]
theorem pairColumnEquiv_left_val (m : Nat) (q : Fin m) :
    ((pairColumnEquiv m (q, 0) : Fin (2 * m)) : Nat) = 2 * q := by
  simp [pairColumnEquiv, Nat.mul_comm]

@[simp]
theorem pairColumnEquiv_right_val (m : Nat) (q : Fin m) :
    ((pairColumnEquiv m (q, 1) : Fin (2 * m)) : Nat) = 2 * q + 1 := by
  simp [pairColumnEquiv, Nat.mul_comm, Nat.add_comm]

/-- The selected-pair matrix with columns genuinely grouped as
`[L₀, ..., Lₘ₋₁, R₀, ..., Rₘ₋₁]`. -/
def groupedSelectedPairMatrix {R I : Type*} {m : Nat}
    (Z : I → Fin (2 * m) → Fin 2 → R) (pairs : List.Vector I m) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) R :=
  fun row col ↦
    match (groupedPairColumnEquiv m).symm col with
    | Sum.inl q => Z (pairs.get q) row 0
    | Sum.inr q => Z (pairs.get q) row 1

@[simp]
theorem groupedSelectedPairMatrix_left {R I : Type*} {m : Nat}
    (Z : I → Fin (2 * m) → Fin 2 → R) (pairs : List.Vector I m)
    (row : Fin (2 * m)) (q : Fin m) :
    groupedSelectedPairMatrix Z pairs row
        (groupedPairColumnEquiv m (Sum.inl q)) =
      Z (pairs.get q) row 0 := by
  simp [groupedSelectedPairMatrix]

@[simp]
theorem groupedSelectedPairMatrix_right {R I : Type*} {m : Nat}
    (Z : I → Fin (2 * m) → Fin 2 → R) (pairs : List.Vector I m)
    (row : Fin (2 * m)) (q : Fin m) :
    groupedSelectedPairMatrix Z pairs row
        (groupedPairColumnEquiv m (Sum.inr q)) =
      Z (pairs.get q) row 1 := by
  simp [groupedSelectedPairMatrix]

theorem groupedSelectedPairMatrix_eq_submatrix {R I : Type*} {m : Nat}
    (Z : I → Fin (2 * m) → Fin 2 → R) (pairs : List.Vector I m) :
    groupedSelectedPairMatrix Z pairs =
      (selectedPairMatrix Z pairs).submatrix id (perfectShufflePerm m) := by
  ext row col
  let side := (groupedPairColumnEquiv m).symm col
  have hcol : col = groupedPairColumnEquiv m side :=
    (groupedPairColumnEquiv m).apply_symm_apply col |>.symm
  rw [hcol]
  rcases side with q | q <;>
    simp [groupedSelectedPairMatrix, Matrix.submatrix_apply, perfectShufflePerm,
      selectedPairMatrix]

/-- The generic grouped matrix in the paper-facing signature is the same
matrix as the vector-based grouped matrix used by the shuffle proof. -/
theorem Odd.groupedPairMatrix_eq_groupedSelectedPairMatrix
    {R I : Type*} {m : Nat}
    (Z : I → Fin (2 * m) → Fin 2 → R) (t : Fin m → I) :
    Odd.groupedPairMatrix Z t =
      groupedSelectedPairMatrix Z (List.Vector.ofFn t) := by
  ext row col
  let side := (groupedPairColumnEquiv m).symm col
  have hcol : col = groupedPairColumnEquiv m side :=
    (groupedPairColumnEquiv m).apply_symm_apply col |>.symm
  rw [hcol]
  rcases side with q | q <;>
    simp [Odd.groupedPairMatrix, groupedSelectedPairMatrix,
      groupedPairColumnEquiv]

/-- The sign of the perfect shuffle is its number of left/right crossings. -/
theorem perfectShufflePerm_sign (m : Nat) :
    Equiv.Perm.sign (perfectShufflePerm m) = (-1 : ℤˣ) ^ (m.choose 2) := by
  rw [Equiv.Perm.sign_eq_prod_prod_Ioi]
  simp_rw [← (groupedPairColumnEquiv m).prod_comp,
    ← Finset.prod_map_equiv (groupedPairColumnEquiv m).symm]
  simp only [Equiv.symm_symm, ← Fin.val_fin_lt, Function.comp_apply,
    ← Finset.prod_ite_mem_eq (Finset.map _ _), Finset.mem_map_equiv,
    Finset.mem_Ioi, Fintype.prod_sum_type,
    perfectShufflePerm_grouped_left, perfectShufflePerm_grouped_right,
    groupedPairColumnEquiv_left_val, groupedPairColumnEquiv_right_val,
    pairColumnEquiv_left_val, pairColumnEquiv_right_val]
  have hleftRight (x y : Fin m) : (x : Nat) < (y : Nat) + m := by omega
  have hevenOdd (x y : Fin m) :
      2 * (x : Nat) < 2 * (y : Nat) + 1 ↔ x ≤ y := by omega
  have hdouble (x y : Fin m) :
      2 * (x : Nat) < 2 * (y : Nat) ↔ x < y := by omega
  have hodd (x y : Fin m) :
      2 * (x : Nat) + 1 < 2 * (y : Nat) + 1 ↔ x < y := by omega
  have hadd (x y : Fin m) :
      (x : Nat) + m < (y : Nat) + m ↔ x < y := by omega
  have hrightLeft (x y : Fin m) : ¬((x : Nat) + m < (y : Nat)) := by omega
  simp only [hleftRight, if_true, hevenOdd, hrightLeft, if_false]
  simp only [hdouble, hodd, hadd]
  have hsame (p : Prop) [Decidable p] :
      (if p then (if p then (1 : ℤˣ) else -1) else 1) = 1 := by
    simp
  simp only [Fin.val_fin_lt, hsame, Finset.prod_const_one, mul_one, one_mul]
  have hinner (x : Fin m) :
      (∏ y : Fin m, if x ≤ y then (1 : ℤˣ) else -1) = (-1) ^ (x : Nat) := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const, one_pow, one_mul]
    rw [show {y ∈ (Finset.univ : Finset (Fin m)) | ¬x ≤ y} = Finset.Iio x by
      ext y
      simp]
    rw [Fin.card_Iio]
  simp_rw [hinner]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  calc
    ∑ i : Fin m, (i : Nat) = ∑ i ∈ Finset.range m, i := by
      simpa using Fin.sum_univ_eq_sum_range id m
    _ = m * (m - 1) / 2 := Finset.sum_range_id m
    _ = m.choose 2 := (Nat.choose_two_right m).symm

/-- Grouping the columns contributes exactly the de Bruijn shuffle sign. -/
theorem groupedSelectedPairMatrix_det {R I : Type*} [CommRing R] {m : Nat}
    (Z : I → Fin (2 * m) → Fin 2 → R) (pairs : List.Vector I m) :
    (groupedSelectedPairMatrix Z pairs).det =
      (-1 : R) ^ (m.choose 2) * (selectedPairMatrix Z pairs).det := by
  rw [groupedSelectedPairMatrix_eq_submatrix, Matrix.det_permute',
    perfectShufflePerm_sign]
  norm_cast

/-- Paper-facing grouped/paired determinant relation, now connected directly
to `Odd.groupedPairMatrix` from the frozen analytic signatures. -/
theorem Odd.groupedPairMatrix_det {R I : Type*} [CommRing R] {m : Nat}
    (Z : I → Fin (2 * m) → Fin 2 → R) (t : Fin m → I) :
    (Odd.groupedPairMatrix Z t).det =
      (-1 : R) ^ (m.choose 2) *
        (selectedPairMatrix Z (List.Vector.ofFn t)).det := by
  rw [Odd.groupedPairMatrix_eq_groupedSelectedPairMatrix]
  exact groupedSelectedPairMatrix_det Z (List.Vector.ofFn t)

/-! Low-rank anchors. -/

@[simp] theorem perfectShufflePerm_sign_one :
    Equiv.Perm.sign (perfectShufflePerm 1) = 1 := by
  rw [perfectShufflePerm_sign]
  norm_num [Nat.choose]

@[simp] theorem perfectShufflePerm_sign_two :
    Equiv.Perm.sign (perfectShufflePerm 2) = -1 := by
  rw [perfectShufflePerm_sign]
  norm_num [Nat.choose]

@[simp] theorem perfectShufflePerm_sign_three :
    Equiv.Perm.sign (perfectShufflePerm 3) = -1 := by
  rw [perfectShufflePerm_sign]
  decide

@[simp]
theorem groupedSelectedPairMatrix_det_one {R I : Type*} [CommRing R]
    (Z : I → Fin 2 → Fin 2 → R) (pairs : List.Vector I 1) :
    (groupedSelectedPairMatrix Z pairs).det =
      (selectedPairMatrix Z pairs).det := by
  simpa [Nat.choose] using groupedSelectedPairMatrix_det Z pairs

@[simp]
theorem groupedSelectedPairMatrix_det_two {R I : Type*} [CommRing R]
    (Z : I → Fin 4 → Fin 2 → R) (pairs : List.Vector I 2) :
    (groupedSelectedPairMatrix Z pairs).det =
      -(selectedPairMatrix Z pairs).det := by
  simpa [Nat.choose] using groupedSelectedPairMatrix_det Z pairs

@[simp]
theorem groupedSelectedPairMatrix_det_three {R I : Type*} [CommRing R]
    (Z : I → Fin 6 → Fin 2 → R) (pairs : List.Vector I 3) :
    (groupedSelectedPairMatrix Z pairs).det =
      -(selectedPairMatrix Z pairs).det := by
  rw [groupedSelectedPairMatrix_det]
  norm_num [Nat.choose, pow_succ]

end

end ColomboGeneralK2
