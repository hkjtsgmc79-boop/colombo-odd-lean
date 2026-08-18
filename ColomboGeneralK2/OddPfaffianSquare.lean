import ColomboGeneralK2.OddMVP1Signatures
import ColomboGeneralK2.PfAgreement
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# The square of the recursive Pfaffian

This file supplies the missing arbitrary-size algebraic interface between the
recursive Pfaffian used by the odd de Bruijn development and `Matrix.det`.

The first part proves the congruence law for `recursivePf` over `Real`.  It is
derived from the already proved arbitrary-size anti-diagonal minor-summation
theorem, rather than postulated as a new Pfaffian API.
-/

namespace ColomboGeneralK2

open scoped BigOperators

noncomputable section

set_option maxRecDepth 10000

/-- Simultaneously apply a matrix to the row vectors of a family of paired
columns. -/
def pfRowTransform {n : Nat} {I : Type*}
    (P : Matrix (Fin n) (Fin n) Real)
    (Z : I → Fin n → Fin 2 → Real) : I → Fin n → Fin 2 → Real :=
  fun t i side ↦ ∑ k, P i k * Z t k side

theorem selectedPairMatrix_pfRowTransform {m : Nat} {I : Type*}
    (P : Matrix (Fin (2 * m)) (Fin (2 * m)) Real)
    (Z : I → Fin (2 * m) → Fin 2 → Real) (pairs : List.Vector I m) :
    selectedPairMatrix (pfRowTransform P Z) pairs =
      P * selectedPairMatrix Z pairs := by
  ext i j
  simp [selectedPairMatrix, pfRowTransform, Matrix.mul_apply]

theorem selectedPairDetFinset_pfRowTransform {m : Nat} {I : Type*}
    [LinearOrder I]
    (P : Matrix (Fin (2 * m)) (Fin (2 * m)) Real)
    (Z : I → Fin (2 * m) → Fin 2 → Real) (S : Finset I) :
    selectedPairDetFinset (pfRowTransform P Z) S =
      P.det * selectedPairDetFinset Z S := by
  rw [selectedPairDetFinset, selectedPairDetFinset]
  split_ifs with h
  · rw [selectedPairDet, selectedPairDet,
      selectedPairMatrix_pfRowTransform, Matrix.det_mul]
  · simp

theorem finsetADMSRhs_pfRowTransform {m : Nat} {I : Type*}
    [LinearOrder I]
    (P : Matrix (Fin (2 * m)) (Fin (2 * m)) Real)
    (Z : I → Fin (2 * m) → Fin 2 → Real) (w : I → Real) (U : Finset I) :
    finsetADMSRhs m (pfRowTransform P Z) w U =
      P.det * finsetADMSRhs m Z w U := by
  simp only [finsetADMSRhs, selectedPairDetFinset_pfRowTransform]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  ring

theorem pairWedge_pfRowTransform {n : Nat} {I : Type*}
    (P : Matrix (Fin n) (Fin n) Real)
    (Z : I → Fin n → Fin 2 → Real) (t : I) (i j : Fin n) :
    pairWedge (pfRowTransform P Z) t i j =
      ∑ a, ∑ b, P i a * P j b * pairWedge Z t a b := by
  simp only [pairWedge, pfRowTransform]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  calc
    (∑ a, ∑ b, P i a * Z t a 0 * (P j b * Z t b 1)) -
        ∑ a, ∑ b, P i a * Z t a 1 * (P j b * Z t b 0) =
        ∑ a, ((∑ b, P i a * Z t a 0 * (P j b * Z t b 1)) -
          ∑ b, P i a * Z t a 1 * (P j b * Z t b 0)) := by
      rw [Finset.sum_sub_distrib]
    _ = ∑ a, ∑ b,
        (P i a * Z t a 0 * (P j b * Z t b 1) -
          P i a * Z t a 1 * (P j b * Z t b 0)) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_sub_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring

/-- Coordinate two-columns indexed by all ordered pairs.  The redundant
ordered-pair presentation is intentional: division by two makes every real
skew matrix a literal `pullbackFinset`, with no choice of an ordering on
unordered pairs. -/
def coordinatePair (n : Nat) : Fin (n * n) → Fin n → Fin 2 → Real :=
  fun t i side ↦
    let q := (finProdFinEquiv (m := n) (n := n)).symm t
    if side = 0 then (if i = q.1 then 1 else 0)
    else (if i = q.2 then 1 else 0)

def coordinateWeight {n : Nat} (A : Matrix (Fin n) (Fin n) Real) :
    Fin (n * n) → Real :=
  fun t ↦
    let q := (finProdFinEquiv (m := n) (n := n)).symm t
    A q.1 q.2 / 2

theorem pullbackFinset_coordinatePair {m : Nat}
    (A : Matrix (Fin (2 * m)) (Fin (2 * m)) Real)
    (hA : ∀ i j, A j i = -A i j) :
    pullbackFinset (coordinatePair (2 * m)) (coordinateWeight A) Finset.univ = A := by
  ext i j
  simp only [pullbackFinset, coordinateWeight]
  rw [← (finProdFinEquiv (m := 2 * m) (n := 2 * m)).sum_comp]
  simp only [pairWedge, coordinatePair]
  rw [Fintype.sum_prod_type]
  simp only [Equiv.symm_apply_apply, one_ne_zero, if_false]
  simp_rw [mul_ite, ite_mul, mul_one, mul_zero]
  ring_nf
  simp only [if_true]
  simp_rw [mul_ite, ite_mul, mul_one, mul_zero]
  simp_rw [Finset.sum_add_distrib]
  simp [eq_comm]
  rw [hA]
  ring

@[simp]
theorem pfRowTransform_coordinatePair_apply {n : Nat}
    (P : Matrix (Fin n) (Fin n) Real) (t : Fin (n * n))
    (i : Fin n) (side : Fin 2) :
    pfRowTransform P (coordinatePair n) t i side =
      let q := (finProdFinEquiv (m := n) (n := n)).symm t
      if side = 0 then P i q.1 else P i q.2 := by
  simp [pfRowTransform, coordinatePair]

theorem pullbackFinset_pfRowTransform_coordinatePair {m : Nat}
    (A P : Matrix (Fin (2 * m)) (Fin (2 * m)) Real)
    (hA : ∀ i j, A j i = -A i j) :
    pullbackFinset (pfRowTransform P (coordinatePair (2 * m)))
        (coordinateWeight A) Finset.univ =
      P * A * P.transpose := by
  ext i j
  simp only [pullbackFinset, coordinateWeight]
  rw [← (finProdFinEquiv (m := 2 * m) (n := 2 * m)).sum_comp]
  simp only [pairWedge, pfRowTransform_coordinatePair_apply, Matrix.mul_apply,
    Matrix.transpose_apply]
  rw [Fintype.sum_prod_type]
  simp only [Equiv.symm_apply_apply, one_ne_zero, if_false, if_true]
  have hswap :
      (∑ x, ∑ y, A x y * P i y * P j x) =
        -(∑ x, ∑ y, A x y * P i x * P j y) := by
    rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro y hy
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rw [hA]
    ring
  have hrhs :
      (∑ x, ∑ y, A y x * P i y * P j x) =
        -(∑ x, ∑ y, A x y * P i y * P j x) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro y hy
    rw [hA]
    ring
  rw [show (∑ x, (∑ y, P i y * A y x) * P j x) =
      ∑ x, ∑ y, A y x * P i y * P j x by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro y hy
        ring]
  ring_nf
  simp_rw [Finset.sum_add_distrib]
  have hleft :
      (∑ x, ∑ y, A x y * P i x * P j y * (1 / 2)) =
        (1 / 2) * (∑ x, ∑ y, A x y * P i x * P j y) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    ring
  have hright :
      (∑ x, ∑ y, A x y * P i y * P j x * (-1 / 2)) =
        (-1 / 2) * (∑ x, ∑ y, A x y * P i y * P j x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    ring
  rw [hleft, hright, hrhs, hswap]
  ring

/-- Congruence covariance of the project's recursive Pfaffian.  The proof is
an application of `recursivePf_pullbackFinset` to the ordered-coordinate
two-form decomposition. -/
theorem recursivePf_congruence {m : Nat}
    (A P : Matrix (Fin (2 * m)) (Fin (2 * m)) Real)
    (hA : ∀ i j, A j i = -A i j) :
    recursivePf m (P * A * P.transpose) = P.det * recursivePf m A := by
  let Z := coordinatePair (2 * m)
  let w := coordinateWeight A
  have hrepr : pullbackFinset Z w Finset.univ = A :=
    pullbackFinset_coordinatePair A hA
  calc
    recursivePf m (P * A * P.transpose) =
        recursivePf m (pullbackFinset (pfRowTransform P Z) w Finset.univ) := by
      rw [pullbackFinset_pfRowTransform_coordinatePair A P hA]
    _ = finsetADMSRhs m (pfRowTransform P Z) w Finset.univ :=
      recursivePf_pullbackFinset m _ _ _
    _ = P.det * finsetADMSRhs m Z w Finset.univ :=
      finsetADMSRhs_pfRowTransform P Z w Finset.univ
    _ = P.det * recursivePf m A := by
      rw [← recursivePf_pullbackFinset m Z w Finset.univ, hrepr]

theorem skew_congruence {n : Nat}
    (A P : Matrix (Fin n) (Fin n) Real)
    (hA : ∀ i j, A j i = -A i j) :
    ∀ i j, (P * A * P.transpose) j i = -(P * A * P.transpose) i j := by
  have hAt : A.transpose = -A := by
    ext i j
    exact hA i j
  have hBt : (P * A * P.transpose).transpose = -(P * A * P.transpose) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hAt]
    simp only [Matrix.mul_neg, Matrix.neg_mul]
    rw [Matrix.mul_assoc]
  intro i j
  exact congrFun (congrFun hBt i) j

/-- The tail after the first two coordinates. -/
def pfTailIndex (n : Nat) : Fin (2 * n) → Fin (2 * (n + 1)) :=
  fun i ↦ ⟨(i : Nat) + 2, by omega⟩

/-- A determinant-one lower shear adapted to a nonzero `A 0 1` pivot. -/
def pfPivotShear {n : Nat}
    (A : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) Real) :
    Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) Real :=
  fun i j ↦
    if i = 0 then if j = 0 then 1 else 0
    else if i = 1 then if j = 1 then 1 else 0
    else if j = 0 then A 1 i / A 0 1
    else if j = 1 then -A 0 i / A 0 1
    else if i = j then 1 else 0

@[simp]
theorem pfPivotShear_zero {n : Nat}
    (A : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) Real)
    (j : Fin (2 * (n + 1))) :
    pfPivotShear A 0 j = if j = 0 then 1 else 0 := by
  simp [pfPivotShear]

@[simp]
theorem pfPivotShear_one {n : Nat}
    (A : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) Real)
    (j : Fin (2 * (n + 1))) :
    pfPivotShear A 1 j = if j = 1 then 1 else 0 := by
  simp [pfPivotShear]

@[simp]
theorem pfTailIndex_ne_zero {n : Nat} (i : Fin (2 * n)) :
    pfTailIndex n i ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp [pfTailIndex] at this

@[simp]
theorem pfTailIndex_ne_one {n : Nat} (i : Fin (2 * n)) :
    pfTailIndex n i ≠ 1 := by
  intro h
  have hh := congrArg Fin.val h
  change (i : Nat) + 2 = 1 at hh
  omega

@[simp]
theorem pfPivotShear_tail {n : Nat}
    (A : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) Real)
    (i : Fin (2 * n)) (j : Fin (2 * (n + 1))) :
    pfPivotShear A (pfTailIndex n i) j =
      if j = 0 then A 1 (pfTailIndex n i) / A 0 1
      else if j = 1 then -A 0 (pfTailIndex n i) / A 0 1
      else if pfTailIndex n i = j then 1 else 0 := by
  simp [pfPivotShear]

theorem pfPivotShear_det {n : Nat}
    (A : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) Real) :
    (pfPivotShear A).det = 1 := by
  rw [Matrix.det_of_lowerTriangular (pfPivotShear A)]
  · have hdiag : ∀ i, pfPivotShear A i i = 1 := by
      intro i
      by_cases hi0 : i = 0
      · simp [pfPivotShear, hi0]
      by_cases hi1 : i = 1
      · simp [pfPivotShear, hi1]
      simp [pfPivotShear, hi0, hi1]
    simp_rw [hdiag]
    simp
  · intro i j hij
    change i < j at hij
    simp [pfPivotShear]
    split_ifs with hi0 hi1 hj0 hj1 hij' <;> subst_vars <;> simp_all

theorem sum_mul_pfPivotShear_tail {n : Nat}
    (A : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) Real)
    (v : Fin (2 * (n + 1)) → Real) (i : Fin (2 * n)) :
    (∑ x, v x * pfPivotShear A (pfTailIndex n i) x) =
      v 0 * (A 1 (pfTailIndex n i) / A 0 1) +
        v 1 * (-A 0 (pfTailIndex n i) / A 0 1) + v (pfTailIndex n i) := by
  simp only [pfPivotShear_tail]
  simp_rw [mul_ite, mul_one, mul_zero]
  calc
    _ = ∑ x,
        ((if x = 0 then v 0 * (A 1 (pfTailIndex n i) / A 0 1) else 0) +
          (if x = 1 then v 1 * (-A 0 (pfTailIndex n i) / A 0 1) else 0) +
          (if x = pfTailIndex n i then v (pfTailIndex n i) else 0)) := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h0 : x = 0
      · subst x
        have ht0 : (0 : Fin (2 * (n + 1))) ≠ pfTailIndex n i :=
          (pfTailIndex_ne_zero i).symm
        simp [ht0]
      by_cases h1 : x = 1
      · subst x
        have ht1 : (1 : Fin (2 * (n + 1))) ≠ pfTailIndex n i :=
          (pfTailIndex_ne_one i).symm
        simp [h0, ht1]
      by_cases ht : x = pfTailIndex n i
      · subst x
        simp [h0, h1]
      have htx : pfTailIndex n i ≠ x := Ne.symm ht
      simp [h0, h1, ht, htx]
    _ = _ := by
      simp only [Finset.sum_add_distrib, Fintype.sum_ite_eq', add_assoc]

theorem pfPivotBlock_zero_tail {n : Nat}
    (A : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) Real)
    (hA : ∀ i j, A j i = -A i j) (hp : A 0 1 ≠ 0)
    (i : Fin (2 * n)) :
    (pfPivotShear A * A * (pfPivotShear A).transpose) 0 (pfTailIndex n i) = 0 := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  have hrow : ∀ x, (∑ k, pfPivotShear A 0 k * A k x) = A 0 x := by
    intro x
    simp [pfPivotShear]
  simp_rw [hrow]
  rw [sum_mul_pfPivotShear_tail]
  have h00 : A 0 0 = 0 := by
    have := hA 0 0
    linarith
  rw [h00]
  field_simp
  ring

theorem pfPivotBlock_one_tail {n : Nat}
    (A : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) Real)
    (hA : ∀ i j, A j i = -A i j) (hp : A 0 1 ≠ 0)
    (i : Fin (2 * n)) :
    (pfPivotShear A * A * (pfPivotShear A).transpose) 1 (pfTailIndex n i) = 0 := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  have hrow : ∀ x, (∑ k, pfPivotShear A 1 k * A k x) = A 1 x := by
    intro x
    simp [pfPivotShear]
  simp_rw [hrow]
  rw [sum_mul_pfPivotShear_tail]
  have h11 : A 1 1 = 0 := by
    have := hA 1 1
    linarith
  rw [h11, hA 0 1]
  field_simp
  ring

theorem pfPivotBlock_zero_one {n : Nat}
    (A : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) Real) :
    (pfPivotShear A * A * (pfPivotShear A).transpose) 0 1 = A 0 1 := by
  simp [Matrix.mul_apply, pfPivotShear]

@[simp]
theorem pfTailIndex_eq_succ_succ {n : Nat} (i : Fin (2 * n)) :
    pfTailIndex n i = Fin.succ (Fin.succ i) := by
  apply Fin.ext
  rfl

theorem skew_diagonal_zero {n : Nat}
    (A : Matrix (Fin n) (Fin n) Real)
    (hA : ∀ i j, A j i = -A i j) (i : Fin n) : A i i = 0 := by
  have := hA i i
  linarith

theorem pfPivotBlock_tail_zero {n : Nat}
    (A : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) Real)
    (hA : ∀ i j, A j i = -A i j) (hp : A 0 1 ≠ 0)
    (i : Fin (2 * n)) :
    (pfPivotShear A * A * (pfPivotShear A).transpose) (pfTailIndex n i) 0 = 0 := by
  rw [skew_congruence A (pfPivotShear A) hA 0 (pfTailIndex n i),
    pfPivotBlock_zero_tail A hA hp]
  simp

theorem pfPivotBlock_tail_one {n : Nat}
    (A : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) Real)
    (hA : ∀ i j, A j i = -A i j) (hp : A 0 1 ≠ 0)
    (i : Fin (2 * n)) :
    (pfPivotShear A * A * (pfPivotShear A).transpose) (pfTailIndex n i) 1 = 0 := by
  rw [skew_congruence A (pfPivotShear A) hA 1 (pfTailIndex n i),
    pfPivotBlock_one_tail A hA hp]
  simp

theorem recursivePf_pivotBlock {n : Nat}
    (A : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) Real)
    (hA : ∀ i j, A j i = -A i j) (hp : A 0 1 ≠ 0) :
    let B := pfPivotShear A * A * (pfPivotShear A).transpose
    recursivePf (n + 1) B =
      A 0 1 * recursivePf n (B.submatrix (pfTailIndex n) (pfTailIndex n)) := by
  dsimp only
  simp only [recursivePf, Fin.sum_univ_succ, Fin.val_zero, pow_zero, one_mul]
  have hone : Fin.succ (0 : Fin (2 * n + 1)) = (1 : Fin (2 * (n + 1))) := rfl
  rw [hone, pfPivotBlock_zero_one]
  have hsub :
      (pfPivotShear A * A * (pfPivotShear A).transpose).submatrix
          (fun i ↦ Fin.succ ((0 : Fin (2 * n + 1)).succAbove i))
          (fun j ↦ Fin.succ ((0 : Fin (2 * n + 1)).succAbove j)) =
        (pfPivotShear A * A * (pfPivotShear A).transpose).submatrix
          (pfTailIndex n) (pfTailIndex n) := by
    ext i j
    rfl
  rw [hsub]
  have hzero : (∑ k : Fin (2 * n),
      (-1 : Real) ^ ((Fin.succ k : Fin (2 * n + 1)) : Nat) *
        (pfPivotShear A * A * (pfPivotShear A).transpose) 0
          (Fin.succ (Fin.succ k)) *
        recursivePf n
          ((pfPivotShear A * A * (pfPivotShear A).transpose).submatrix
            (fun i ↦ Fin.succ ((Fin.succ k).succAbove i))
            (fun j ↦ Fin.succ ((Fin.succ k).succAbove j)))) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [← pfTailIndex_eq_succ_succ k, pfPivotBlock_zero_tail A hA hp]
    ring
  rw [hzero, add_zero]

theorem det_pivotBlock {n : Nat}
    (A : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) Real)
    (hA : ∀ i j, A j i = -A i j) (hp : A 0 1 ≠ 0) :
    let B := pfPivotShear A * A * (pfPivotShear A).transpose
    B.det = (A 0 1) ^ 2 *
      (B.submatrix (pfTailIndex n) (pfTailIndex n)).det := by
  dsimp only
  let B := pfPivotShear A * A * (pfPivotShear A).transpose
  have hBskew : ∀ i j, B j i = -B i j :=
    skew_congruence A (pfPivotShear A) hA
  change B.det = (A 0 1) ^ 2 *
    (B.submatrix (pfTailIndex n) (pfTailIndex n)).det
  rw [Matrix.det_succ_row_zero]
  rw [Fin.sum_univ_succ]
  have h00 : B 0 0 = 0 := skew_diagonal_zero B hBskew 0
  rw [h00]
  simp only [mul_zero, zero_mul, zero_add]
  rw [Fin.sum_univ_succ]
  have htail : ∀ k : Fin (2 * n), B 0 (Fin.succ (Fin.succ k)) = 0 := by
    intro k
    rw [← pfTailIndex_eq_succ_succ k]
    exact pfPivotBlock_zero_tail A hA hp k
  simp_rw [htail]
  simp only [mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  have hone : Fin.succ (0 : Fin (2 * n + 1)) = (1 : Fin (2 * (n + 1))) := rfl
  rw [hone, show B 0 1 = A 0 1 by exact pfPivotBlock_zero_one A]
  let C := B.submatrix Fin.succ (Fin.succ (0 : Fin (2 * n + 1))).succAbove
  change (-1 : Real) ^ (1 : Nat) * A 0 1 * C.det = _
  rw [Matrix.det_succ_row_zero]
  rw [Fin.sum_univ_succ]
  have hC00 : C 0 0 = -A 0 1 := by
    change B 1 0 = -A 0 1
    rw [hBskew 0 1]
    have hB01 : B 0 1 = A 0 1 := by
      dsimp only [B]
      exact pfPivotBlock_zero_one A
    rw [hB01]
  rw [hC00]
  have hminor : C.submatrix Fin.succ (0 : Fin (2 * n + 1)).succAbove =
      B.submatrix (pfTailIndex n) (pfTailIndex n) := by
    dsimp only [C]
    ext i j
    rfl
  rw [hminor]
  have hCtail : ∀ k : Fin (2 * n), C 0 (Fin.succ k) = 0 := by
    intro k
    change B 1 (pfTailIndex n k) = 0
    exact pfPivotBlock_one_tail A hA hp k
  simp_rw [hCtail]
  simp only [mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  norm_num
  ring

theorem recursivePf_sq_eq_det_of_pivot {n : Nat}
    (A : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) Real)
    (hA : ∀ i j, A j i = -A i j) (hp : A 0 1 ≠ 0)
    (ih : ∀ (C : Matrix (Fin (2 * n)) (Fin (2 * n)) Real),
      (∀ i j, C j i = -C i j) → C.det = (recursivePf n C) ^ 2) :
    A.det = (recursivePf (n + 1) A) ^ 2 := by
  let P := pfPivotShear A
  let B := P * A * P.transpose
  let C := B.submatrix (pfTailIndex n) (pfTailIndex n)
  have hPdet : P.det = 1 := pfPivotShear_det A
  have hBskew : ∀ i j, B j i = -B i j := skew_congruence A P hA
  have hCskew : ∀ i j, C j i = -C i j := by
    intro i j
    exact hBskew (pfTailIndex n i) (pfTailIndex n j)
  have hdetB : B.det = A.det := by
    dsimp only [B]
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hPdet]
    ring
  have hpfB : recursivePf (n + 1) B = recursivePf (n + 1) A := by
    dsimp only [B, P]
    rw [recursivePf_congruence A (pfPivotShear A) hA, pfPivotShear_det]
    simp
  have hdetBlock : B.det = (A 0 1) ^ 2 * C.det := by
    dsimp only [B, C, P]
    exact det_pivotBlock A hA hp
  have hpfBlock : recursivePf (n + 1) B = A 0 1 * recursivePf n C := by
    dsimp only [B, C, P]
    exact recursivePf_pivotBlock A hA hp
  calc
    A.det = B.det := hdetB.symm
    _ = (A 0 1) ^ 2 * C.det := hdetBlock
    _ = (A 0 1) ^ 2 * (recursivePf n C) ^ 2 := by rw [ih C hCskew]
    _ = (recursivePf (n + 1) B) ^ 2 := by rw [hpfBlock]; ring
    _ = (recursivePf (n + 1) A) ^ 2 := by rw [hpfB]

/-- Add `t` to the `(0,1)` entry and `-t` to `(1,0)`. -/
def pfPivotPerturb {n : Nat}
    (A : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) Real) (t : Real) :
    Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) Real :=
  fun i j ↦
    if i = 0 ∧ j = 1 then A i j + t
    else if i = 1 ∧ j = 0 then A i j - t
    else A i j

theorem pfPivotPerturb_skew {n : Nat}
    (A : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) Real)
    (hA : ∀ i j, A j i = -A i j) (t : Real) :
    ∀ i j, pfPivotPerturb A t j i = -pfPivotPerturb A t i j := by
  intro i j
  simp only [pfPivotPerturb]
  have h01 : (0 : Fin (2 * (n + 1))) ≠ 1 := Fin.zero_ne_one
  by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;>
    by_cases hj0 : j = 0 <;> by_cases hj1 : j = 1 <;>
      simp [hi0, hi1, hj0, hj1, h01] <;> subst_vars <;>
        first | exact hA _ _ | (rw [hA]; ring)

@[simp]
theorem pfPivotPerturb_zero_one {n : Nat}
    (A : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) Real) (t : Real) :
    pfPivotPerturb A t 0 1 = A 0 1 + t := by
  simp [pfPivotPerturb]

theorem tendsto_pfPivotPerturb {n : Nat}
    (A : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) Real)
    {f : ℕ → Real} (hf : Filter.Tendsto f Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun k ↦ pfPivotPerturb A (f k)) Filter.atTop (nhds A) := by
  change Filter.Tendsto (fun k i j ↦ pfPivotPerturb A (f k) i j)
    Filter.atTop (nhds (fun i j ↦ A i j))
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  simp only [pfPivotPerturb]
  split_ifs
  · simpa using tendsto_const_nhds.add hf
  · simpa using tendsto_const_nhds.sub hf
  · exact tendsto_const_nhds

theorem continuous_recursivePf : ∀ m : Nat,
    Continuous (fun A : Matrix (Fin (2 * m)) (Fin (2 * m)) Real ↦ recursivePf m A) := by
  intro m
  induction m with
  | zero => exact continuous_const
  | succ n ih =>
      simp only [recursivePf]
      fun_prop

theorem continuous_matrix_det (n : Nat) :
    Continuous (fun A : Matrix (Fin n) (Fin n) Real ↦ A.det) := by
  simp only [Matrix.det_apply]
  fun_prop

/-- The determinant of every even real skew matrix is the square of the
project's recursive Pfaffian, at arbitrary size. -/
theorem det_eq_recursivePf_sq : ∀ (m : Nat)
    (A : Matrix (Fin (2 * m)) (Fin (2 * m)) Real),
    (∀ i j, A j i = -A i j) → A.det = (recursivePf m A) ^ 2 := by
  intro m
  induction m with
  | zero =>
      intro A hA
      simp [recursivePf]
  | succ n ih =>
      intro A hA
      by_cases hp : A 0 1 ≠ 0
      · exact recursivePf_sq_eq_det_of_pivot A hA hp ih
      · let ε : ℕ → Real := fun k ↦ 1 / ((k : Real) + 1)
        let Aε : ℕ → Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) Real :=
          fun k ↦ pfPivotPerturb A (ε k)
        have hε : Filter.Tendsto ε Filter.atTop (nhds 0) := by
          simpa only [ε] using
            (tendsto_one_div_add_atTop_nhds_zero_nat :
              Filter.Tendsto (fun k : ℕ ↦ 1 / ((k : Real) + 1))
                Filter.atTop (nhds 0))
        have hAε : Filter.Tendsto Aε Filter.atTop (nhds A) := by
          exact tendsto_pfPivotPerturb A hε
        have hskew (k : ℕ) : ∀ i j, Aε k j i = -Aε k i j :=
          pfPivotPerturb_skew A hA (ε k)
        have hpivot (k : ℕ) : Aε k 0 1 ≠ 0 := by
          rw [show Aε k 0 1 = A 0 1 + ε k by
            exact pfPivotPerturb_zero_one A (ε k)]
          rw [not_ne_iff.mp hp, zero_add]
          dsimp only [ε]
          positivity
        have heq (k : ℕ) : (Aε k).det = (recursivePf (n + 1) (Aε k)) ^ 2 :=
          recursivePf_sq_eq_det_of_pivot (Aε k) (hskew k) (hpivot k) ih
        have hdet : Filter.Tendsto (fun k ↦ (Aε k).det) Filter.atTop (nhds A.det) :=
          (continuous_matrix_det (2 * (n + 1))).continuousAt.tendsto.comp hAε
        have hpf : Filter.Tendsto
            (fun k ↦ recursivePf (n + 1) (Aε k))
            Filter.atTop (nhds (recursivePf (n + 1) A)) :=
          (continuous_recursivePf (n + 1)).continuousAt.tendsto.comp hAε
        have hsq : Filter.Tendsto
            (fun k ↦ (recursivePf (n + 1) (Aε k)) ^ 2)
            Filter.atTop (nhds ((recursivePf (n + 1) A) ^ 2)) := hpf.pow 2
        have hdet' : Filter.Tendsto
            (fun k ↦ (recursivePf (n + 1) (Aε k)) ^ 2)
            Filter.atTop (nhds A.det) :=
          hdet.congr' (Filter.Eventually.of_forall heq)
        exact tendsto_nhds_unique hdet' hsq

theorem det_pos_of_recursivePf_ne_zero {m : Nat}
    (A : Matrix (Fin (2 * m)) (Fin (2 * m)) Real)
    (hA : ∀ i j, A j i = -A i j)
    (hpf : recursivePf m A ≠ 0) : 0 < A.det := by
  rw [det_eq_recursivePf_sq m A hA]
  exact sq_pos_of_ne_zero hpf

theorem Odd.powerDifference_skew {m : Nat} (r : Nat)
    (x : Fin (2 * m) → Real) :
    ∀ i j, powerDifference x (2 * r + 1) j i =
      -powerDifference x (2 * r + 1) i j := by
  intro i j
  simp only [powerDifference]
  rw [show x i - x j = -(x j - x i) by ring, neg_pow]
  have hodd : Odd (2 * r + 1) := ⟨r, by omega⟩
  rw [hodd.neg_one_pow]
  ring

theorem Odd.det_powerDifference_eq_recursivePf_sq {m : Nat} (r : Nat)
    (x : Fin (2 * m) → Real) :
    (powerDifference x (2 * r + 1)).det =
      (recursivePf m (powerDifference x (2 * r + 1))) ^ 2 :=
  det_eq_recursivePf_sq m _ (powerDifference_skew r x)

theorem Odd.oddDeterminantPositive_of_pfaffianSign {m : Nat} (r : Nat)
    (x : Fin (2 * m) → Real) :
    OddPfaffianSignTarget r x → OddDeterminantPositiveTarget r x := by
  intro hsign hm hr hx hnonneg
  have hpos := hsign hm hr hx hnonneg
  have hpf : recursivePf m (powerDifference x (2 * r + 1)) ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hpos
    exact (lt_irrefl 0) hpos
  exact det_pos_of_recursivePf_ne_zero _ (powerDifference_skew r x) hpf


end

end ColomboGeneralK2
