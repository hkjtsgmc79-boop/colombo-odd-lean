import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Order.Interval.Finset.Fin
import ColomboGeneralK2.OddBSplineRefinement
import ColomboGeneralK2.OddFiniteBSpline
import ColomboGeneralK2.OddCriticalSplitBridge
import ColomboGeneralK2.OddTwoFanData

/-!
# B-spline collocation matrix for the odd branch

This module assembles the refinement of the open knot vector along the repeated
sampling points and proves that every maximal minor of the collocation matrix
`bsplineCollocation D x` is nonnegative via Cauchy--Binet.
-/

open scoped BigOperators

namespace ColomboGeneralK2.Odd

noncomputable section

/-- Insert every value of a list into a knot vector, left to right. -/
def insertList (L : List ℝ) {n : Nat} [NeZero n] (K : Fin n → ℝ) :
    Fin (n + L.length) → ℝ :=
  match L with
  | [] => fun i => K ⟨(i : Nat), by simpa using i.isLt⟩
  | τ :: L' => fun i =>
      insertList L' (insertKnot K τ) ⟨(i : Nat), by
        have hi : (i : Nat) < n + L'.length + 1 := by
          have h := i.isLt
          change (i : Nat) < n + (L'.length + 1) at h
          omega
        omega⟩

/-- `Fin.castLE` as an order embedding. -/
def finCastLEOrderEmb {m n : Nat} (h : m ≤ n) : Fin m ↪o Fin n :=
  OrderEmbedding.ofStrictMono (Fin.castLE h) (by
    intro a b hab
    exact Fin.lt_iff_val_lt_val.mpr (by
      simpa [Fin.castLE] using Fin.lt_iff_val_lt_val.mp hab))

/-- The product of the one-step refinement matrices along a list of insertions. -/
def refineList (L : List ℝ) {n : Nat} [NeZero n] (K : Fin n → ℝ) (k : Nat) :
    Matrix (Fin (n - k - 1)) (Fin (n + L.length - k - 1)) ℝ :=
  match L with
  | [] => fun i j => if (j : Nat) = (i : Nat) then 1 else 0
  | τ :: L' =>
      let R := refineList L' (insertKnot K τ) k
      let hrow : n - k ≤ (n + 1) - k - 1 := by omega
      let hcol : n + L'.length + 1 - k - 1 ≤ (n + 1) + L'.length - k - 1 := by omega
      ((refineMatrix K τ k * R.submatrix (finCastLEOrderEmb hrow) id).submatrix id (finCastLEOrderEmb hcol))

/-- At a fixed flat block of knots equal to `τ` (with strictly smaller/larger
neighbors), the degree-`k` B-spline is a single selector: it is `1` exactly at
window `b - k` and `0` elsewhere. -/
theorem splineOn_flat_selector {n : Nat} [NeZero n] {K : Fin n → ℝ} (hK : Monotone K)
    (τ : ℝ) (k : Nat) {a b : Nat} (hab : a ≤ b) (hbn : b + 1 < n) (hbk : k ≤ b - a)
    (hflat : ∀ j, a ≤ j → j ≤ b → knotAt K j = τ)
    (hleft : knotAt K (a - 1) < τ) (hright : τ < knotAt K (b + 1)) :
    ∀ i : Nat, i + k + 1 ≤ n → splineOn K i k τ = if i = b - k then 1 else 0 := by
  revert hbk
  induction k with
  | zero =>
      intro hbk i hi
      rw [splineOn_zero]
      by_cases hib : i = b
      · rw [hib]
        have hKi : knotAt K b = τ := hflat b hab (by omega)
        have hcond : knotAt K b ≤ τ ∧ τ < knotAt K (b + 1) := ⟨hKi.le, hright⟩
        simp [hcond]
      · have hnot : ¬ (knotAt K i ≤ τ ∧ τ < knotAt K (i + 1)) := by
          rintro ⟨hle, hlt⟩
          have hne : i ≠ b := by intro h; exact hib h
          by_cases hil : i < b
          · have hmono : knotAt K (i + 1) ≤ knotAt K b := knotAt_mono hK (by omega)
            have hKb : knotAt K b = τ := hflat b hab (by omega)
            exact not_lt_of_ge (le_trans hmono (le_of_eq hKb)) hlt
          · have hgt : b < i := lt_of_le_of_ne (le_of_not_gt hil) (Ne.symm hne)
            have hmono : knotAt K (b + 1) ≤ knotAt K i := knotAt_mono hK (by omega)
            exact not_le_of_gt hright (le_trans hmono hle)
        simp [hnot, hib]
  | succ k ih =>
      intro hbk i hi
      rw [splineOn_succ]
      have hbk' : k ≤ b - a := by omega
      have hih_i : splineOn K i k τ = if i = b - k then 1 else 0 :=
        ih hbk' i (by omega)
      have hih_i1 : splineOn K (i + 1) k τ = if i + 1 = b - k then 1 else 0 :=
        ih hbk' (i + 1) (by omega)
      rw [hih_i, hih_i1]
      by_cases h1 : i = b - (k + 1)
      · subst h1
        have hnot_i : ¬ (b - (k + 1) = b - k) := by omega
        have hpos_i1 : b - (k + 1) + 1 = b - k := by omega
        simp [hnot_i, hpos_i1]
        unfold wRK
        rw [show b - (k + 1) + k + 2 = b + 1 by omega, show b - (k + 1) + 1 = b - k by omega]
        have hKbk : knotAt K (b - k) = τ := hflat (b - k) (by omega) (by omega)
        rw [hKbk]
        have hnum : knotAt K (b + 1) - τ ≠ 0 := sub_ne_zero.mpr (ne_of_gt hright)
        simp [hnum]
      · by_cases h2 : i = b - k
        · subst h2
          have hi1_not : ¬ (b - k + 1 = b - k) := by omega
          simp [hi1_not, h1]
          unfold wLK
          rw [show b - k + k + 1 = b + 1 by omega]
          have hKbk : knotAt K (b - k) = τ := hflat (b - k) (by omega) (by omega)
          rw [hKbk]
          simp
        · have hi_not : ¬ (i = b - k) := h2
          have hi1_not : ¬ (i + 1 = b - k) := by omega
          simp [hi_not, hi1_not, h1]

/-- Submatrix by increasing embeddings preserves total nonnegativity. -/

lemma isTotallyNonnegative_submatrix {r c r' c' : Nat} (A : Matrix (Fin r) (Fin c) ℝ)
    (f : Fin r' ↪o Fin r) (g : Fin c' ↪o Fin c) (hA : IsTotallyNonnegative A) :
    IsTotallyNonnegative (A.submatrix f g) := by
  intro k rows cols
  unfold matrixMinor
  rw [Matrix.submatrix_submatrix]
  exact hA k (rows.comp f) (cols.comp g)

/-- A selector matrix with strictly increasing columns is totally nonnegative. -/
theorem selectorMatrix_isTotallyNonnegative {r N : Nat} (p : Fin r → Fin N) (hp : StrictMono p) :
    IsTotallyNonnegative (fun i j => if j = p i then 1 else 0) := by
  intro k rows cols
  unfold matrixMinor
  rw [Matrix.det_apply']
  let A : Matrix (Fin r) (Fin N) ℝ := fun i j => if j = p i then 1 else 0
  have hA_nonzero : ∀ i j, A i j ≠ 0 → j = p i := by
    intro i j h
    unfold A at h
    by_cases hjp : j = p i
    · exact hjp
    · simp [hjp] at h
  have hsum : (∑ σ : Equiv.Perm (Fin k), Equiv.Perm.sign σ * ∏ t : Fin k, (A.submatrix rows cols) (σ t) t) =
      ∏ t : Fin k, (A.submatrix rows cols) t t := by
    rw [Finset.sum_eq_single 1]
    · simp
    · intro σ hσ hσ1
      have hprod : ∏ t : Fin k, (A.submatrix rows cols) (σ t) t = 0 := by
        by_contra hnot
        have hne : ∀ t : Fin k, (A.submatrix rows cols) (σ t) t ≠ 0 := by
          intro t
          exact (Finset.prod_ne_zero_iff.mp hnot) t (Finset.mem_univ t)
        have hmono : StrictMono (σ : Fin k → Fin k) := by
          apply strictMono_fin_of_succ
          intro a b hb1
          have hca : A (rows (σ a)) (cols a) ≠ 0 := by
            simpa [Matrix.submatrix_apply] using hne a
          have hcb : A (rows (σ b)) (cols b) ≠ 0 := by
            simpa [Matrix.submatrix_apply] using hne b
          have hcola : cols a = p (rows (σ a)) := hA_nonzero (rows (σ a)) (cols a) hca
          have hcolb : cols b = p (rows (σ b)) := hA_nonzero (rows (σ b)) (cols b) hcb
          have hcols_lt : cols a < cols b := cols.strictMono (Fin.lt_iff_val_lt_val.mpr (by omega))
          have hp_lt : p (rows (σ a)) < p (rows (σ b)) := by
            rwa [hcola, hcolb] at hcols_lt
          have hrows_lt : rows (σ a) < rows (σ b) := by
            by_contra hnot
            have hle : rows (σ b) ≤ rows (σ a) := le_of_not_gt hnot
            have hple : p (rows (σ b)) ≤ p (rows (σ a)) := hp.monotone hle
            exact not_lt_of_ge hple hp_lt
          by_contra hnot
          have hle : σ b ≤ σ a := le_of_not_gt hnot
          have hrows_le : rows (σ b) ≤ rows (σ a) := rows.strictMono.monotone hle
          exact not_lt_of_ge hrows_le hrows_lt
        have hσ_eq := perm_strictMono_eq_one σ hmono
        exact hσ1 hσ_eq
      rw [hprod, mul_zero]
    · intro h
      exact False.elim (h (Finset.mem_univ 1))
  rw [hsum]
  simp only [Matrix.submatrix_apply]
  apply Finset.prod_nonneg
  intro t _
  unfold A
  by_cases h : cols t = p (rows t) <;> simp [h]

/-- The product of the one-step refinement matrices is totally nonnegative. -/
theorem refineList_isTotallyNonnegative (L : List ℝ) {n : Nat} [NeZero n] (K : Fin n → ℝ)
    (hK : Monotone K) (k : Nat) : IsTotallyNonnegative (refineList L K k) := by
  induction L generalizing n K hK k with
  | nil =>
      let p : Fin (n - k - 1) → Fin (n - k - 1) := id
      have hp : StrictMono p := by
        intro a b hab
        exact hab
      have hsel := selectorMatrix_isTotallyNonnegative p hp
      simpa [refineList, p, Fin.ext_iff] using hsel
  | cons τ L' ih =>
      have hK' : Monotone (insertKnot K τ) := insertKnot_mono hK τ
      have hR : IsTotallyNonnegative (refineList L' (insertKnot K τ) k) := ih (insertKnot K τ) hK' k
      let hrow : n - k ≤ (n + 1) - k - 1 := by omega
      let hcol : n + L'.length + 1 - k - 1 ≤ (n + 1) + L'.length - k - 1 := by omega
      have hR' : IsTotallyNonnegative ((refineList L' (insertKnot K τ) k).submatrix (finCastLEOrderEmb hrow) id) :=
        isTotallyNonnegative_submatrix (refineList L' (insertKnot K τ) k)
          (finCastLEOrderEmb hrow) (OrderEmbedding.id _) hR
      have hmul : IsTotallyNonnegative
          (refineMatrix K τ k * (refineList L' (insertKnot K τ) k).submatrix (finCastLEOrderEmb hrow) id) :=
        isTotallyNonnegative_mul (refineMatrix K τ k)
          ((refineList L' (insertKnot K τ) k).submatrix (finCastLEOrderEmb hrow) id)
          (refineMatrix_isTotallyNonnegative hK τ k) hR'
      let M : Matrix (Fin (n - k - 1)) (Fin ((n + 1) + L'.length - k - 1)) ℝ :=
        refineMatrix K τ k * (refineList L' (insertKnot K τ) k).submatrix (finCastLEOrderEmb hrow) id
      have hres : IsTotallyNonnegative (M.submatrix id (finCastLEOrderEmb hcol)) :=
        isTotallyNonnegative_submatrix M (OrderEmbedding.id _) (finCastLEOrderEmb hcol) hmul
      simpa [refineList, hrow, hcol] using hres

/-- The empty insertion does not change the clamped knots. -/
lemma insertList_nil_knotAt {n : Nat} [NeZero n] (K : Fin n → ℝ) :
    knotAt (insertList [] K) = knotAt K := by
  apply knotAt_congr
  intro i
  simp [insertList]

/-- The two nonzero entries of a row of `refineMatrix`. -/
lemma refineMatrix_sum_collapse {n : Nat} [NeZero n] (K : Fin n → ℝ) (τ : ℝ) (k : Nat)
    (g : Nat → ℝ) (i : Nat) (hi : i < n - k - 1) :
    (∑ u : Fin (n - k), refineMatrix K τ k ⟨i, hi⟩ u * g (u : Nat)) =
      aCoeff K τ i k * g i + bCoeff K τ i k * g (i + 1) := by
  have hi0 : i < n - k := by omega
  have hi1 : i + 1 < n - k := by omega
  let i0 : Fin (n - k) := ⟨i, hi0⟩
  let i1 : Fin (n - k) := ⟨i + 1, hi1⟩
  let f : Fin (n - k) → ℝ := fun u => refineMatrix K τ k ⟨i, hi⟩ u * g (u : Nat)
  let s0 : Finset (Fin (n - k)) := Finset.univ.erase i0
  let s1 : Finset (Fin (n - k)) := s0.erase i1
  change (∑ u : Fin (n - k), f u) = aCoeff K τ i k * g i + bCoeff K τ i k * g (i + 1)
  rw [Finset.sum_eq_add_sum_diff_singleton i0 f (fun h => False.elim (h (Finset.mem_univ i0)))]
  rw [Finset.sdiff_singleton_eq_erase]
  change f i0 + (∑ x ∈ s0, f x) = aCoeff K τ i k * g i + bCoeff K τ i k * g (i + 1)
  have hmem : i1 ∈ s0 := by
    simp [s0, i0, i1, Fin.ext_iff, Nat.succ_ne_self]
  rw [Finset.sum_eq_add_sum_diff_singleton i1 f (fun h => False.elim (h hmem))]
  rw [Finset.sdiff_singleton_eq_erase]
  change f i0 + (f i1 + (∑ x ∈ s1, f x)) = aCoeff K τ i k * g i + bCoeff K τ i k * g (i + 1)
  have hzero : (∑ x ∈ s1, f x) = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    have hu' : u ∈ s0.erase i1 := by simpa [s1] using hu
    have hu_ne_i1 : u ≠ i1 := (Finset.mem_erase.mp hu').1
    have hu_in_s0 : u ∈ s0 := (Finset.mem_erase.mp hu').2
    have hu_ne_i0 : u ≠ i0 := (Finset.mem_erase.mp hu_in_s0).1
    have hun0 : (u : Nat) ≠ i := by intro h; exact hu_ne_i0 (Fin.ext h)
    have hun1 : (u : Nat) ≠ i + 1 := by intro h; exact hu_ne_i1 (Fin.ext h)
    simp [f, refineMatrix, hun0, hun1]
  rw [hzero]
  simp [f, refineMatrix, i0, i1]

/-- Reindexing a sum along `Fin.castLE` when the lengths are equal. -/
lemma sum_reindex_finCastLEOrderEmb {a b : Nat} (h : a ≤ b) (heq : a = b)
    (F : Fin b → ℝ) :
    (∑ j : Fin a, F (finCastLEOrderEmb h j)) = ∑ j : Fin b, F j := by
  have hfg : ∀ j ∈ (Finset.univ : Finset (Fin a)), F (finCastLEOrderEmb h j) = F (finCongr heq j) := by
    intro j hj
    have hval : (finCastLEOrderEmb h j : Nat) = (finCongr heq j : Nat) := by
      simp [finCastLEOrderEmb, finCongr]
    exact congrArg F (Fin.ext hval)
  simpa using (Finset.sum_equiv (finCongr heq) (by intro i; simp) hfg)

/-- The product of a `refineMatrix` row with a matrix is the two-term Boehm blend. -/
lemma refineMatrix_mul_apply {n : Nat} [NeZero n] (K : Fin n → ℝ) (τ : ℝ) (k : Nat)
    {c : Nat} (R' : Matrix (Fin (n - k)) (Fin c) ℝ) (i : Nat) (hi : i < n - k - 1)
    (hi0 : i < n - k) (hi1 : i + 1 < n - k) (j : Fin c) :
    (refineMatrix K τ k * R') ⟨i, hi⟩ j =
      aCoeff K τ i k * R' ⟨i, hi0⟩ j + bCoeff K τ i k * R' ⟨i + 1, hi1⟩ j := by
  rw [Matrix.mul_apply]
  let g : Nat → ℝ := fun u => if hu : u < n - k then R' ⟨u, hu⟩ j else 0
  have h := refineMatrix_sum_collapse K τ k g i hi
  simpa [g, hi0, hi1] using h

/-- The recursive insertion list agrees with the one-step insertion. -/
lemma insertList_cons_knotAt {n : Nat} [NeZero n] (K : Fin n → ℝ) (τ : ℝ) (L' : List ℝ) :
    knotAt (insertList (τ :: L') K) = knotAt (insertList L' (insertKnot K τ)) := by
  funext j
  unfold knotAt
  have hcongr : n + L'.length + 1 = n + (L'.length + 1) := by omega
  by_cases hj : j < n + L'.length + 1
  · have hj' : j < (n + 1) + L'.length := by omega
    rw [hcongr] at hj
    simp [insertList, hj, hj']
  · have hj' : ¬ j < (n + 1) + L'.length := by omega
    have hlast1 : n + L'.length + 1 - 1 = n + L'.length := by omega
    have hlast2 : (n + 1) + L'.length - 1 = n + L'.length := by omega
    have hj'' : ¬ j < n + (L'.length + 1) := by omega
    simp [insertList, hj'', hj', hlast1, hlast2]

/-- One step of the product refinement matrix: the row at the head of the
insertion list. -/
lemma refineList_cons_apply {n : Nat} [NeZero n] (K : Fin n → ℝ) (τ : ℝ) (L' : List ℝ)
    (k i : Nat) (hi : i < n - k - 1)
    (hiL : i < (n + 1) - k - 1) (hiR : i + 1 < (n + 1) - k - 1)
    (j : Fin ((n + 1) + L'.length - k - 1))
    (hj' : (j : Nat) < n + (τ :: L').length - k - 1) :
    refineList (τ :: L') K k ⟨i, hi⟩ ⟨(j : Nat), hj'⟩ =
      aCoeff K τ i k * refineList L' (insertKnot K τ) k ⟨i, hiL⟩ j +
        bCoeff K τ i k * refineList L' (insertKnot K τ) k ⟨i + 1, hiR⟩ j := by
  rw [refineList]
  have hrow : n - k ≤ (n + 1) - k - 1 := by omega
  have hcol : n + (τ :: L').length - k - 1 ≤ (n + 1) + L'.length - k - 1 := by
    simp only [List.length_cons]
    exact Nat.sub_le_sub_right (Nat.sub_le_sub_right (by omega) k) 1
  change ((refineMatrix K τ k * (refineList L' (insertKnot K τ) k).submatrix
      (finCastLEOrderEmb hrow) id).submatrix id (finCastLEOrderEmb hcol)) ⟨i, hi⟩
      ⟨(j : Nat), hj'⟩ =
    aCoeff K τ i k * refineList L' (insertKnot K τ) k ⟨i, hiL⟩ j +
      bCoeff K τ i k * refineList L' (insertKnot K τ) k ⟨i + 1, hiR⟩ j
  simp only [Matrix.submatrix_apply]
  have hi0 : i < n - k := by omega
  have hi1 : i + 1 < n - k := by omega
  have hmul := refineMatrix_mul_apply K τ k
    (R' := (refineList L' (insertKnot K τ) k).submatrix (finCastLEOrderEmb hrow) id)
    (i := i) (hi := hi) (hi0 := hi0) (hi1 := hi1)
    (j := (finCastLEOrderEmb hcol) ⟨(j : Nat), hj'⟩)
  change (refineMatrix K τ k * (refineList L' (insertKnot K τ) k).submatrix
      (finCastLEOrderEmb hrow) id) ⟨i, hi⟩ ((finCastLEOrderEmb hcol) ⟨(j : Nat), hj'⟩) =
    aCoeff K τ i k * refineList L' (insertKnot K τ) k ⟨i, hiL⟩ j +
      bCoeff K τ i k * refineList L' (insertKnot K τ) k ⟨i + 1, hiR⟩ j
  rw [hmul]
  simp only [Matrix.submatrix_apply]
  have h1 : (finCastLEOrderEmb hrow) ⟨i, hi0⟩ = ⟨i, hiL⟩ := by
    apply Fin.ext
    simp [finCastLEOrderEmb]
  have h2 : (finCastLEOrderEmb hcol) ⟨(j : Nat), hj'⟩ = j := by
    apply Fin.ext
    simp [finCastLEOrderEmb]
  have h3 : (finCastLEOrderEmb hrow) ⟨i + 1, hi1⟩ = ⟨i + 1, hiR⟩ := by
    apply Fin.ext
    simp [finCastLEOrderEmb]
  rw [h1, h2, h3]
  rfl

/-- The B-spline recursion depends only on the clamped knot sequence, even
across different vector lengths. -/
lemma splineOn_congr' {n n' : Nat} [NeZero n] [NeZero n'] {K : Fin n → ℝ} {K' : Fin n' → ℝ}
    (h : knotAt K = knotAt K') (i k : Nat) (y : ℝ) :
    splineOn K i k y = splineOn K' i k y := by
  induction k generalizing i with
  | zero => simp [h]
  | succ k ih => simp [wLK, wRK, h, ih i, ih (i + 1)]

theorem splineOn_refineList : ∀ {n : Nat} [NeZero n] (K : Fin n → ℝ) (hK : Monotone K),
    (L : List ℝ) → (k : Nat) → (i : Nat) → (hi : i < n - k - 1) → (y : ℝ) →
    splineOn K i k y = ∑ j : Fin (n + L.length - k - 1),
      refineList L K k ⟨i, hi⟩ j * splineOn (insertList L K) (j : Nat) k y := by
  intro n _ K hK L
  induction L generalizing n K hK with
  | nil =>
      intro k i hi y
      have hnil : knotAt (insertList [] K) = knotAt K := insertList_nil_knotAt K
      have hi' : i < n + 0 - k - 1 := by omega
      calc
        splineOn K i k y
            = ∑ j : Fin (n + 0 - k - 1),
                (if (j : Nat) = (i : Nat) then (1 : ℝ) else 0) * splineOn K (j : Nat) k y := by
                rw [Finset.sum_eq_single ⟨i, hi'⟩]
                · simp
                · intro b hb hne
                  have hne' : (b : Nat) ≠ (i : Nat) := by
                    intro h
                    exact hne (Fin.ext h)
                  simp [hne']
                · intro h
                  simp at h
            _ = ∑ j : Fin (n + 0 - k - 1),
                refineList [] K k ⟨i, hi⟩ j * splineOn (insertList [] K) (j : Nat) k y := by
                apply Finset.sum_congr rfl
                intro j _
                simp [refineList]
                rw [splineOn_congr hnil]
  | cons τ L' ih =>
      intro k i hi y
      have hboehm := boehmIdentity hK τ i k y (by omega : i + k + 2 ≤ n)
      have hcons : knotAt (insertList (τ :: L') K) = knotAt (insertList L' (insertKnot K τ)) :=
        insertList_cons_knotAt K τ L'
      have hiL : i < (n + 1) - k - 1 := by omega
      have hiR : i + 1 < (n + 1) - k - 1 := by omega
      have hihL : splineOn (insertKnot K τ) i k y =
          ∑ j : Fin ((n + 1) + L'.length - k - 1),
            refineList L' (insertKnot K τ) k ⟨i, hiL⟩ j *
              splineOn (insertList L' (insertKnot K τ)) (j : Nat) k y :=
        ih (n := n + 1) (K := insertKnot K τ) (hK := insertKnot_mono hK τ) k i hiL y
      have hihR : splineOn (insertKnot K τ) (i + 1) k y =
          ∑ j : Fin ((n + 1) + L'.length - k - 1),
            refineList L' (insertKnot K τ) k ⟨i + 1, hiR⟩ j *
              splineOn (insertList L' (insertKnot K τ)) (j : Nat) k y :=
        ih (n := n + 1) (K := insertKnot K τ) (hK := insertKnot_mono hK τ) k (i + 1) hiR y
      calc
        splineOn K i k y
            = aCoeff K τ i k * splineOn (insertKnot K τ) i k y +
                bCoeff K τ i k * splineOn (insertKnot K τ) (i + 1) k y := hboehm
        _ = aCoeff K τ i k *
              (∑ j : Fin ((n + 1) + L'.length - k - 1),
                refineList L' (insertKnot K τ) k ⟨i, hiL⟩ j *
                  splineOn (insertList L' (insertKnot K τ)) (j : Nat) k y) +
            bCoeff K τ i k *
              (∑ j : Fin ((n + 1) + L'.length - k - 1),
                refineList L' (insertKnot K τ) k ⟨i + 1, hiR⟩ j *
                  splineOn (insertList L' (insertKnot K τ)) (j : Nat) k y) := by
              rw [hihL, hihR]
        _ = ∑ j : Fin ((n + 1) + L'.length - k - 1),
              (aCoeff K τ i k * refineList L' (insertKnot K τ) k ⟨i, hiL⟩ j +
                bCoeff K τ i k * refineList L' (insertKnot K τ) k ⟨i + 1, hiR⟩ j) *
                splineOn (insertList L' (insertKnot K τ)) (j : Nat) k y := by
              rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro j _
              ring
        _ = ∑ j : Fin (n + (τ :: L').length - k - 1),
              refineList (τ :: L') K k ⟨i, hi⟩ j *
                splineOn (insertList (τ :: L') K) (j : Nat) k y := by
              have hlen : (n + 1) + L'.length - k - 1 = n + (τ :: L').length - k - 1 := by
                simp only [List.length_cons]
                omega
              rw [sum_finCast hlen.symm (fun j : Fin (n + (τ :: L').length - k - 1) ↦
                refineList (τ :: L') K k ⟨i, hi⟩ j *
                  splineOn (insertList (τ :: L') K) (j : Nat) k y)]
              apply Finset.sum_congr rfl
              intro j _
              have hj' : (j : Nat) < n + (τ :: L').length - k - 1 := by
                exact lt_of_lt_of_le j.isLt (by
                  simp only [List.length_cons]
                  exact Nat.sub_le_sub_right (Nat.sub_le_sub_right (by omega) k) 1)
              rw [refineList_cons_apply K τ L' k i hi hiL hiR j hj']
              rw [splineOn_congr' hcons.symm (j : Nat) k y]

/-- The insertion sequence: `m-1` copies of every sample, in order. -/
def sampleInsertions {m : Nat} (x : Fin (2 * m) → ℝ) : List ℝ :=
  (List.finRange (2 * m)).flatMap (fun r : Fin (2 * m) ↦
    List.replicate (m - 1) (x r))

/-- Inserting one copy of `τ` does not change the number of knots below `τ`. -/
lemma insertPos_insertKnot_same {n : Nat} [NeZero n] {K : Fin n → ℝ} (hK : Monotone K)
    (τ : ℝ) : insertPos (insertKnot K τ) τ = insertPos K τ := by
  have hK' : Monotone (insertKnot K τ) := insertKnot_mono hK τ
  have hpn : insertPos K τ ≤ n := insertPos_le K τ
  have hle : insertPos (insertKnot K τ) τ ≤ insertPos K τ := by
    by_contra hnot
    have hlt : insertPos K τ < insertPos (insertKnot K τ) τ := lt_of_not_ge hnot
    have hpn1 : insertPos K τ < n + 1 := Nat.lt_succ_of_le hpn
    have htau := insertPos_lt_of_lt hK' τ (i := ⟨insertPos K τ, hpn1⟩) hlt
    have hval : (insertKnot K τ) ⟨insertPos K τ, hpn1⟩ = τ := by
      simpa [knotAt_lt (insertKnot K τ) (insertPos K τ) hpn1] using
        (knotAt_insertKnot_eq K τ)
    exact lt_irrefl τ (by simpa [hval] using htau)
  have hge : insertPos K τ ≤ insertPos (insertKnot K τ) τ := by
    by_cases hp0 : insertPos K τ = 0
    · omega
    · have hppos : 0 < insertPos K τ := Nat.pos_of_ne_zero hp0
      have hpp : insertPos K τ - 1 < insertPos K τ := Nat.sub_one_lt hp0
      have hpn1' : insertPos K τ - 1 < n + 1 := by omega
      have hbelow : (insertKnot K τ) ⟨insertPos K τ - 1, hpn1'⟩ < τ := by
        rw [insertKnot_eq_knotAt K τ ⟨insertPos K τ - 1, hpn1'⟩]
        exact knotAt_insertKnot_lt_tau hK τ hpp
      have hpos : (⟨insertPos K τ - 1, hpn1'⟩ : Fin (n + 1)).val <
          insertPos (insertKnot K τ) τ :=
        (insertPos_lt_iff hK' τ ⟨insertPos K τ - 1, hpn1'⟩).mp hbelow
      change insertPos K τ - 1 < insertPos (insertKnot K τ) τ at hpos
      omega
  exact le_antisymm hle hge
theorem insertReplicate_block {n : Nat} [NeZero n] {K : Fin n → ℝ} (hK : Monotone K)
    (τ : ℝ) (t : Nat) {μ : Nat} (hμlen : insertPos K τ + μ ≤ n)
    (hμflat : ∀ j, insertPos K τ ≤ j → j < insertPos K τ + μ → knotAt K j = τ)
    (hμlt : 0 < insertPos K τ → knotAt K (insertPos K τ - 1) < τ)
    (hμgt : insertPos K τ + μ < n → τ < knotAt K (insertPos K τ + μ)) :
    (∀ j, insertPos K τ ≤ j → j < insertPos K τ + μ + t →
      knotAt (insertList (List.replicate t τ) K) j = τ) ∧
    (0 < insertPos K τ →
      knotAt (insertList (List.replicate t τ) K) (insertPos K τ - 1) < τ) ∧
    (insertPos K τ + μ + t < n + t →
      τ < knotAt (insertList (List.replicate t τ) K) (insertPos K τ + μ + t)) := by
  induction t generalizing n K hK τ μ hμlen hμflat hμlt hμgt with
  | zero =>
      have hrep : List.replicate 0 τ = [] := rfl
      rw [hrep]
      constructor
      · intro j hj1 hj2
        rw [insertList_nil_knotAt]
        exact hμflat j hj1 hj2
      · constructor
        · intro hp0
          rw [insertList_nil_knotAt]
          exact hμlt hp0
        · intro hgt
          rw [insertList_nil_knotAt]
          have hgt' : insertPos K τ + μ < n := by omega
          exact hμgt hgt'
  | succ t ih =>
      have hp : insertPos (insertKnot K τ) τ = insertPos K τ :=
        insertPos_insertKnot_same hK τ
      have hμ'flat : ∀ j, insertPos (insertKnot K τ) τ ≤ j →
          j < insertPos (insertKnot K τ) τ + (μ + 1) →
          knotAt (insertKnot K τ) j = τ := by
        intro j hj1 hj2
        rw [hp] at hj1 hj2
        by_cases hje : j = insertPos K τ
        · rw [hje, knotAt_insertKnot_eq]
        · have hjgt : insertPos K τ < j := by omega
          have hjlen : j ≤ n := by omega
          rw [knotAt_insertKnot_gt K τ hjgt hjlen]
          have hj1m : j - 1 < n := by omega
          rw [knotAt_lt K (j - 1) hj1m]
          simpa [knotAt_lt K (j - 1) hj1m] using
            (hμflat (j - 1) (by omega) (by omega))
      have hμ'lt : 0 < insertPos (insertKnot K τ) τ →
          knotAt (insertKnot K τ) (insertPos (insertKnot K τ) τ - 1) < τ := by
        intro hp0
        rw [hp] at hp0 ⊢
        have hlt : insertPos K τ - 1 < insertPos K τ := by omega
        rw [knotAt_insertKnot_lt K τ hlt]
        exact hμlt hp0
      have hμ'gt : insertPos (insertKnot K τ) τ + (μ + 1) < n + 1 →
          τ < knotAt (insertKnot K τ) (insertPos (insertKnot K τ) τ + (μ + 1)) := by
        intro hgt
        rw [hp] at hgt ⊢
        have hidx : insertPos K τ + (μ + 1) = insertPos K τ + μ + 1 := by omega
        rw [hidx]
        have hjgt : insertPos K τ < insertPos K τ + μ + 1 := by omega
        have hjlen : insertPos K τ + μ + 1 ≤ n := by omega
        rw [knotAt_insertKnot_gt K τ hjgt hjlen]
        have hj1 : insertPos K τ + μ + 1 - 1 < n := by omega
        have hidx : insertPos K τ + μ + 1 - 1 = insertPos K τ + μ := by omega
        rw [hidx]
        rw [knotAt_lt K (insertPos K τ + μ) hj1]
        have hgt' : insertPos K τ + μ < n := by omega
        simpa [knotAt_lt K (insertPos K τ + μ) hj1] using hμgt hgt'
      have hih := ih (n := n + 1) (K := insertKnot K τ) (insertKnot_mono hK τ) τ
        (μ := μ + 1) (show insertPos (insertKnot K τ) τ + (μ + 1) ≤ n + 1 by omega)
        hμ'flat hμ'lt hμ'gt
      have hcons : knotAt (insertList (τ :: List.replicate t τ) K) =
          knotAt (insertList (List.replicate t τ) (insertKnot K τ)) :=
        insertList_cons_knotAt K τ (List.replicate t τ)
      constructor
      · intro j hj1 hj2
        rw [show List.replicate (t + 1) τ = τ :: List.replicate t τ by rfl]
        rw [hcons]
        exact hih.1 j (by rwa [hp]) (by
          rw [hp]
          omega)
      · constructor
        · intro hp0
          rw [show List.replicate (t + 1) τ = τ :: List.replicate t τ by rfl]
          rw [hcons, ← hp]
          exact hih.2.1 (by rwa [hp])
        · intro hgt
          rw [show List.replicate (t + 1) τ = τ :: List.replicate t τ by rfl]
          rw [hcons]
          have hidx : insertPos K τ + μ + (t + 1) = insertPos K τ + (μ + 1) + t := by omega
          rw [hidx, ← hp]
          exact hih.2.2 (by
            rw [hp]
            omega)

/-! ## Fine-vector block structure -/

/-- Number of entries of K equal to τ. -/
def eqCount {n : Nat} (K : Fin n → ℝ) (τ : ℝ) : Nat :=
  (Finset.univ.filter (fun i : Fin n => K i = τ)).card


/-- The Fin index shuffle order embedding for equal index types. -/
def finCastShuffleEmb {n m : Nat} (h : n = m) : Fin n ↪o Fin m :=
  OrderEmbedding.ofStrictMono (fun i => ⟨(i : Nat), by omega⟩) (by
    intro x y hxy
    exact Fin.lt_iff_val_lt_val.mpr (by simpa using Fin.lt_iff_val_lt_val.mp hxy))

/-- The filter of a value predicate is stable under the Fin index shuffle. -/
lemma filter_comp_finCast_lt {n m : Nat} [NeZero n] [NeZero m] (K : Fin m → ℝ) (τ : ℝ)
    (h : n = m) :
    (Finset.univ.filter (fun i : Fin n => K ⟨(i : Nat), by omega⟩ < τ)) =
      (Finset.univ.filter (fun i : Fin m => K i < τ)).map (finCastShuffleEmb h.symm).toEmbedding := by
  ext j
  rw [Finset.mem_map]
  constructor
  · intro hi
    refine ⟨finCastShuffleEmb h j, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hvj : K ⟨(j : Nat), by omega⟩ < τ := (Finset.mem_filter.mp hi).2
      simpa [finCastShuffleEmb] using hvj
    · ext
      rfl
  · intro hi
    rcases hi with ⟨i, hj, hij⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hvi : K i < τ := (Finset.mem_filter.mp hj).2
    have hcast : finCastShuffleEmb h.symm i = j := hij
    rw [← hcast]
    simpa [finCastShuffleEmb] using hvi

/-- The filter of an equality predicate is stable under the Fin index shuffle. -/
lemma filter_comp_finCast_eq {n m : Nat} [NeZero n] [NeZero m] (K : Fin m → ℝ) (τ : ℝ)
    (h : n = m) :
    (Finset.univ.filter (fun i : Fin n => K ⟨(i : Nat), by omega⟩ = τ)) =
      (Finset.univ.filter (fun i : Fin m => K i = τ)).map (finCastShuffleEmb h.symm).toEmbedding := by
  ext j
  rw [Finset.mem_map]
  constructor
  · intro hi
    refine ⟨finCastShuffleEmb h j, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hvj : K ⟨(j : Nat), by omega⟩ = τ := (Finset.mem_filter.mp hi).2
      simpa [finCastShuffleEmb] using hvj
    · ext
      rfl
  · intro hi
    rcases hi with ⟨i, hj, hij⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hvi : K i = τ := (Finset.mem_filter.mp hj).2
    have hcast : finCastShuffleEmb h.symm i = j := hij
    rw [← hcast]
    simpa [finCastShuffleEmb] using hvi

/-- insertPos is stable under the Fin index shuffle. -/
theorem insertPos_comp_finCast {n m : Nat} [NeZero n] [NeZero m] (K : Fin m → ℝ) (τ : ℝ)
    (h : n = m) :
    insertPos (fun i : Fin n => K ⟨(i : Nat), by omega⟩) τ = insertPos K τ := by
  unfold insertPos
  rw [filter_comp_finCast_lt K τ h]
  simp

/-- eqCount is stable under the Fin index shuffle. -/
theorem eqCount_comp_finCast {n m : Nat} [NeZero n] [NeZero m] (K : Fin m → ℝ) (τ : ℝ)
    (h : n = m) :
    eqCount (fun i : Fin n => K ⟨(i : Nat), by omega⟩) τ = eqCount K τ := by
  unfold eqCount
  rw [filter_comp_finCast_eq K τ h]
  simp

/-- Inserting a whole list preserves monotonicity of the knot vector. -/
theorem insertList_mono {n : Nat} [NeZero n] {K : Fin n → ℝ} (hK : Monotone K)
    (L : List ℝ) : Monotone (insertList L K) := by
  induction L generalizing n K hK with
  | nil =>
      intro a b hab
      simp only [insertList]
      exact hK (Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp hab))
  | cons τ L' ih =>
      intro a b hab
      simp only [insertList]
      have ha : (a : Nat) < n + 1 + L'.length := by
        have h := a.isLt
        simp only [List.length_cons] at h
        omega
      have hb : (b : Nat) < n + 1 + L'.length := by
        have h := b.isLt
        simp only [List.length_cons] at h
        omega
      exact ih (insertKnot_mono hK τ) (a := ⟨(a : Nat), ha⟩) (b := ⟨(b : Nat), hb⟩)
        (Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp hab))

/-- Inserting a value strictly below τ increases insertPos by one. -/
theorem insertPos_insertKnot_lt {n : Nat} [NeZero n] {K : Fin n → ℝ} (hK : Monotone K)
    (σ τ : ℝ) (hστ : σ < τ) :
    insertPos (insertKnot K σ) τ = insertPos K τ + 1 := by
  have hpσ : insertPos K σ ≤ insertPos K τ := by
    unfold insertPos
    refine Finset.card_le_card ?_
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨Finset.mem_univ _, lt_trans hi.2 hστ⟩
  have hS : (Finset.univ.filter (fun i : Fin (n + 1) => (insertKnot K σ) i < τ)) =
      Finset.univ.filter (fun i : Fin (n + 1) => (i : Nat) ≤ insertPos K τ) := by
    ext i
    constructor
    · intro hi
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hvi : (insertKnot K σ) i < τ := (Finset.mem_filter.mp hi).2
      rw [insertKnot_eq_knotAt K σ i] at hvi
      by_cases h1 : (i : Nat) < insertPos K σ
      · rw [knotAt_insertKnot_lt K σ h1] at hvi
        have hin : (i : Nat) < n := lt_of_lt_of_le h1 (insertPos_le K σ)
        rw [knotAt_lt K (i : Nat) hin] at hvi
        have hiτ : (i : Nat) < insertPos K τ := (insertPos_lt_iff hK τ ⟨(i : Nat), hin⟩).mp hvi
        omega
      · by_cases h2 : (i : Nat) = insertPos K σ
        · rw [h2, knotAt_insertKnot_eq] at hvi
          omega
        · have h3 : insertPos K σ < (i : Nat) := by omega
          have hle : (i : Nat) ≤ n := by omega
          rw [knotAt_insertKnot_gt K σ h3 hle] at hvi
          have hin : (i : Nat) - 1 < n := by omega
          rw [knotAt_lt K ((i : Nat) - 1) hin] at hvi
          have hiτ : (i : Nat) - 1 < insertPos K τ :=
            (insertPos_lt_iff hK τ ⟨(i : Nat) - 1, hin⟩).mp hvi
          have hi' : (i : Nat) < insertPos K τ + 1 :=
            (Nat.sub_lt_iff_lt_add (by omega : 1 ≤ (i : Nat))).mp hiτ
          omega
    · intro hi
      have hiτ : (i : Nat) ≤ insertPos K τ := (Finset.mem_filter.mp hi).2
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      by_cases h1 : (i : Nat) < insertPos K σ
      · have hin : (i : Nat) < n := lt_of_lt_of_le h1 (insertPos_le K σ)
        have hKσ : K ⟨(i : Nat), hin⟩ < σ := insertPos_lt_of_lt hK σ h1
        rw [insertKnot_eq_knotAt K σ i, knotAt_insertKnot_lt K σ h1, knotAt_lt K (i : Nat) hin]
        exact lt_trans hKσ hστ
      · by_cases h2 : (i : Nat) = insertPos K σ
        · rw [insertKnot_eq_knotAt K σ i, h2, knotAt_insertKnot_eq]
          exact hστ
        · have h3 : insertPos K σ < (i : Nat) := by omega
          have hle : (i : Nat) ≤ n := by omega
          have hin : (i : Nat) - 1 < n := by omega
          have hi1 : (i : Nat) - 1 < insertPos K τ := by
            rw [Nat.sub_lt_iff_lt_add (by omega : 1 ≤ (i : Nat))]
            omega
          have hKτ : K ⟨(i : Nat) - 1, hin⟩ < τ := insertPos_lt_of_lt hK τ hi1
          rw [insertKnot_eq_knotAt K σ i, knotAt_insertKnot_gt K σ h3 hle,
            knotAt_lt K ((i : Nat) - 1) hin]
          exact hKτ
  unfold insertPos
  rw [hS]
  rw [show (Finset.univ.filter (fun i : Fin (n + 1) => (i : Nat) ≤ insertPos K τ)) =
      Finset.univ.filter (fun i : Fin (n + 1) => (i : Nat) < insertPos K τ + 1) by
    ext i
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨Finset.mem_univ _, Nat.lt_succ_of_le h.2⟩,
      fun h => ⟨Finset.mem_univ _, Nat.le_of_lt_succ h.2⟩⟩]
  exact card_fin_below (n + 1) (insertPos K τ + 1) (by
    have hp := insertPos_le K τ
    omega)

/-- Inserting a value ≥ τ leaves insertPos unchanged. -/
theorem insertPos_insertKnot_ge {n : Nat} [NeZero n] {K : Fin n → ℝ} (hK : Monotone K)
    (σ τ : ℝ) (hτσ : τ ≤ σ) :
    insertPos (insertKnot K σ) τ = insertPos K τ := by
  have hpσ : insertPos K τ ≤ insertPos K σ := by
    unfold insertPos
    refine Finset.card_le_card ?_
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨Finset.mem_univ _, lt_of_lt_of_le hi.2 hτσ⟩
  have hS : (Finset.univ.filter (fun i : Fin (n + 1) => (insertKnot K σ) i < τ)) =
      Finset.univ.filter (fun i : Fin (n + 1) => (i : Nat) < insertPos K τ) := by
    ext i
    constructor
    · intro hi
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hvi : (insertKnot K σ) i < τ := (Finset.mem_filter.mp hi).2
      rw [insertKnot_eq_knotAt K σ i] at hvi
      by_cases h1 : (i : Nat) < insertPos K σ
      · rw [knotAt_insertKnot_lt K σ h1] at hvi
        have hin : (i : Nat) < n := lt_of_lt_of_le h1 (insertPos_le K σ)
        rw [knotAt_lt K (i : Nat) hin] at hvi
        exact (insertPos_lt_iff hK τ ⟨(i : Nat), hin⟩).mp hvi
      · by_cases h2 : (i : Nat) = insertPos K σ
        · rw [h2, knotAt_insertKnot_eq] at hvi
          exact False.elim (lt_irrefl σ (lt_of_lt_of_le hvi hτσ))
        · have h3 : insertPos K σ < (i : Nat) := by omega
          have hle : (i : Nat) ≤ n := by omega
          rw [knotAt_insertKnot_gt K σ h3 hle] at hvi
          have hin : (i : Nat) - 1 < n := by omega
          rw [knotAt_lt K ((i : Nat) - 1) hin] at hvi
          have hiτ : (i : Nat) - 1 < insertPos K τ :=
            (insertPos_lt_iff hK τ ⟨(i : Nat) - 1, hin⟩).mp hvi
          have hi' : (i : Nat) < insertPos K τ + 1 :=
            (Nat.sub_lt_iff_lt_add (by omega : 1 ≤ (i : Nat))).mp hiτ
          omega
    · intro hi
      have hiτ : (i : Nat) < insertPos K τ := (Finset.mem_filter.mp hi).2
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      by_cases h1 : (i : Nat) < insertPos K σ
      · have hin : (i : Nat) < n := lt_of_lt_of_le h1 (insertPos_le K σ)
        have hKτ : K ⟨(i : Nat), hin⟩ < τ := insertPos_lt_of_lt hK τ hiτ
        rw [insertKnot_eq_knotAt K σ i, knotAt_insertKnot_lt K σ h1, knotAt_lt K (i : Nat) hin]
        exact hKτ
      · by_cases h2 : (i : Nat) = insertPos K σ
        · have hfalse : False := by omega
          exact False.elim hfalse
        · have h3 : insertPos K σ < (i : Nat) := by omega
          have hle : (i : Nat) ≤ n := by omega
          have hin : (i : Nat) - 1 < n := by omega
          have hi1 : (i : Nat) - 1 < insertPos K τ := by
            rw [Nat.sub_lt_iff_lt_add (by omega : 1 ≤ (i : Nat))]
            omega
          have hKτ : K ⟨(i : Nat) - 1, hin⟩ < τ := insertPos_lt_of_lt hK τ hi1
          rw [insertKnot_eq_knotAt K σ i, knotAt_insertKnot_gt K σ h3 hle,
            knotAt_lt K ((i : Nat) - 1) hin]
          exact hKτ
  unfold insertPos
  rw [hS]
  exact card_fin_below (n + 1) (insertPos K τ) (by
    have hp := insertPos_le K τ
    omega)

/-- insertPos after a list insertion counts the inserted values below τ. -/
theorem insertPos_insertList {n : Nat} [NeZero n] {K : Fin n → ℝ} (hK : Monotone K)
    (L : List ℝ) (τ : ℝ) :
    insertPos (insertList L K) τ = insertPos K τ + (L.filter (fun σ => σ < τ)).length := by
  induction L generalizing n K hK with
  | nil =>
      simp [insertList]
  | cons σ L' ih =>
      rw [insertList]
      rw [insertPos_comp_finCast (insertList L' (insertKnot K σ)) τ
        (by rw [List.length_cons]; ac_rfl : n + (σ :: L').length = (n + 1) + L'.length)]
      rw [ih (insertKnot_mono hK σ)]
      by_cases hστ : σ < τ
      · rw [insertPos_insertKnot_lt hK σ τ hστ]
        simp [List.filter_cons, hστ]
        ac_rfl
      · rw [insertPos_insertKnot_ge hK σ τ (le_of_not_gt hστ)]
        simp [List.filter_cons, hστ]

/-- Inserting one value changes the equality count only when it equals τ. -/
theorem eqCount_insertKnot {n : Nat} [NeZero n] (K : Fin n → ℝ) (σ τ : ℝ) :
    eqCount (insertKnot K σ) τ = eqCount K τ + (if σ = τ then 1 else 0) := by
  have hcardS : (Finset.univ.filter (fun i : Fin (n + 1) => (insertKnot K σ) i = τ)).card =
      ∑ i : Fin (n + 1), (if (insertKnot K σ) i = τ then (1 : Nat) else 0) := by
    rw [Finset.card_filter]
  have hp : insertPos K σ < n + 1 := Nat.lt_succ_of_le (insertPos_le K σ)
  calc
    eqCount (insertKnot K σ) τ
        = ∑ i : Fin (n + 1), (if (insertKnot K σ) i = τ then (1 : Nat) else 0) := by
            unfold eqCount
            rw [hcardS]
        _ = (if σ = τ then 1 else 0) + ∑ j : Fin n, (if K j = τ then 1 else 0) := by
            rw [Fin.sum_univ_succAbove (f := fun i : Fin (n + 1) =>
              if (insertKnot K σ) i = τ then (1 : Nat) else 0) (x := ⟨insertPos K σ, hp⟩)]
            have hval : (if (insertKnot K σ) ⟨insertPos K σ, hp⟩ = τ then 1 else 0) =
                (if σ = τ then 1 else 0) := by
              have hσ : (insertKnot K σ) ⟨insertPos K σ, hp⟩ = σ := by
                rw [insertKnot_eq_knotAt K σ ⟨insertPos K σ, hp⟩]
                rw [knotAt_insertKnot_eq]
              rw [hσ]
            rw [hval]
            congr 1
            apply Finset.sum_congr rfl
            intro j _
            have hsucc : (insertKnot K σ) ((⟨insertPos K σ, hp⟩ : Fin (n + 1)).succAbove j) = K j := by
              rw [insertKnot_eq_knotAt K σ ((⟨insertPos K σ, hp⟩ : Fin (n + 1)).succAbove j)]
              by_cases hj : (j : Nat) < insertPos K σ
              · have hv : (((⟨insertPos K σ, hp⟩ : Fin (n + 1)).succAbove j : Fin (n + 1))).val = (j : Nat) := by
                  simp [Fin.succAbove, Fin.lt_iff_val_lt_val, hj]
                rw [hv]
                rw [knotAt_insertKnot_lt K σ hj, knotAt_lt K (j : Nat) j.isLt]
              · have hv : (((⟨insertPos K σ, hp⟩ : Fin (n + 1)).succAbove j : Fin (n + 1))).val = (j : Nat) + 1 := by
                  simp [Fin.succAbove, Fin.lt_iff_val_lt_val, hj]
                rw [hv]
                rw [knotAt_insertKnot_gt K σ (by omega) (by omega : (j : Nat) + 1 ≤ n)]
                rw [knotAt_lt K ((j : Nat) + 1 - 1) (by simpa using j.isLt)]
                rfl
            rw [hsucc]
        _ = eqCount K τ + (if σ = τ then 1 else 0) := by
            unfold eqCount
            rw [Finset.card_filter]
            rw [Nat.add_comm]

/-- eqCount after a list insertion counts the inserted copies of τ. -/
theorem eqCount_insertList {n : Nat} [NeZero n] (K : Fin n → ℝ) (L : List ℝ) (τ : ℝ) :
    eqCount (insertList L K) τ = eqCount K τ + (L.filter (fun σ => σ = τ)).length := by
  induction L generalizing n K with
  | nil =>
      simp [insertList]
  | cons σ L' ih =>
      rw [insertList]
      rw [eqCount_comp_finCast (insertList L' (insertKnot K σ)) τ
        (by rw [List.length_cons]; ac_rfl : n + (σ :: L').length = (n + 1) + L'.length)]
      rw [ih (insertKnot K σ)]
      rw [eqCount_insertKnot K σ τ]
      by_cases h : σ = τ
      · simp [List.filter_cons, h]
        ac_rfl
      · simp [List.filter_cons, h]

/-- The count of finite-ordinal entries in a half-open index interval. -/
lemma card_fin_between {n a b : Nat} (hab : a ≤ b) (hbn : b ≤ n) :
    (Finset.univ.filter (fun i : Fin n => a ≤ (i : Nat) ∧ (i : Nat) < b)).card = b - a := by
  let e : Fin (b - a) ↪ Fin n :=
    ⟨fun i => ⟨a + (i : Nat), by omega⟩, by
      intro x y h
      exact Fin.ext (by simpa using congrArg Fin.val h)⟩
  have hE : Finset.univ.filter (fun i : Fin n => a ≤ (i : Nat) ∧ (i : Nat) < b) =
      Finset.univ.map e := by
    ext i
    constructor
    · intro hi
      have h := (Finset.mem_filter.mp hi).2
      rw [Finset.mem_map]
      refine ⟨⟨(i : Nat) - a, by omega⟩, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      simp [e]
      omega
    · intro hi
      rw [Finset.mem_map] at hi
      rcases hi with ⟨j, _, hj⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hv : a + (j : Nat) = (i : Nat) := by simpa [e] using congrArg Fin.val hj
      omega
  rw [hE]
  simp [e]

/-- The count of finite-ordinal entries in a closed index interval. -/
lemma card_fin_between_cc {n a b : Nat} (hab : a ≤ b) (hbn : b < n) :
    (Finset.univ.filter (fun i : Fin n => a ≤ (i : Nat) ∧ (i : Nat) ≤ b)).card = b + 1 - a := by
  have hsub : (Finset.univ.filter (fun i : Fin n => a ≤ (i : Nat) ∧ (i : Nat) ≤ b)) =
      Finset.univ.filter (fun i : Fin n => a ≤ (i : Nat) ∧ (i : Nat) < b + 1) := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · intro h
      exact ⟨h.1, by omega⟩
    · intro h
      exact ⟨h.1, by omega⟩
  rw [hsub]
  exact card_fin_between (n := n) (a := a) (b := b + 1) (by omega) (by omega)

/-- In a monotone vector, entries in [insertPos, insertPos + eqCount) are τ. -/
theorem knotAt_eq_of_between {n : Nat} [NeZero n] {K : Fin n → ℝ} (hK : Monotone K)
    (τ : ℝ) {j : Nat} (hp : insertPos K τ ≤ j)
    (hj : j < insertPos K τ + eqCount K τ) (hjn : j < n) : knotAt K j = τ := by
  have hge : τ ≤ knotAt K j := by
    rw [knotAt_lt K j hjn]
    exact insertPos_ge_of_le hK τ (i := ⟨j, hjn⟩) hp
  have hle : knotAt K j ≤ τ := by
    by_contra hgt
    have hτlt : τ < knotAt K j := lt_of_not_ge hgt
    have hsub : (Finset.univ.filter (fun i : Fin n => K i = τ)) ⊆
        Finset.univ.filter (fun i : Fin n => insertPos K τ ≤ (i : Nat) ∧ (i : Nat) < j) := by
      intro i hi
      have hiτ : K i = τ := (Finset.mem_filter.mp hi).2
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      constructor
      · by_contra hnoti
        have hK : K i < τ := insertPos_lt_of_lt hK τ (lt_of_not_ge hnoti)
        exact (ne_of_lt hK) hiτ
      · by_contra hnoti
        have hji : j ≤ (i : Nat) := le_of_not_gt hnoti
        have hmono : knotAt K j ≤ knotAt K (i : Nat) := knotAt_mono hK hji
        rw [knotAt_lt K (i : Nat) i.isLt, hiτ] at hmono
        exact not_lt_of_ge hmono hτlt
    have hcard : (Finset.univ.filter (fun i : Fin n => insertPos K τ ≤ (i : Nat) ∧ (i : Nat) < j)).card =
        j - insertPos K τ := by
      exact card_fin_between hp (le_of_lt hjn)
    have hcardle : eqCount K τ ≤ j - insertPos K τ := by
      unfold eqCount
      rw [← hcard]
      exact Finset.card_le_card hsub
    omega
  exact le_antisymm hle hge

/-- An entry equal to τ lies at or above insertPos. -/
theorem knotAt_eq_ge_insertPos {n : Nat} [NeZero n] {K : Fin n → ℝ} (hK : Monotone K)
    (τ : ℝ) {j : Nat} (hjn : j < n) (hjτ : knotAt K j = τ) :
    insertPos K τ ≤ j := by
  by_contra hnot
  have hjlt : j < insertPos K τ := lt_of_not_ge hnot
  have hKj : knotAt K j < τ := by
    rw [knotAt_lt K j hjn]
    exact insertPos_lt_of_lt hK τ hjlt
  exact (ne_of_lt hKj) hjτ

/-- An entry equal to τ lies strictly below insertPos + eqCount. -/
theorem knotAt_eq_lt_add {n : Nat} [NeZero n] {K : Fin n → ℝ} (hK : Monotone K)
    (τ : ℝ) {j : Nat} (hjn : j < n) (hjτ : knotAt K j = τ) :
    j < insertPos K τ + eqCount K τ := by
  by_contra hnot
  have hge : insertPos K τ + eqCount K τ ≤ j := le_of_not_gt hnot
  have hp : insertPos K τ ≤ j := by omega
  have hsub : Finset.univ.filter (fun i : Fin n => insertPos K τ ≤ (i : Nat) ∧
      (i : Nat) < insertPos K τ + eqCount K τ) ⊆
      Finset.univ.filter (fun i : Fin n => K i = τ) := by
    intro i hi
    have h := (Finset.mem_filter.mp hi).2
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa [knotAt_lt K (i : Nat) i.isLt] using knotAt_eq_of_between hK τ h.1 h.2 i.isLt
  have hmem : ⟨j, hjn⟩ ∈ Finset.univ.filter (fun i : Fin n => K i = τ) := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa [knotAt_lt K j hjn] using hjτ
  have hdis : Disjoint (Finset.univ.filter (fun i : Fin n => insertPos K τ ≤ (i : Nat) ∧
      (i : Nat) < insertPos K τ + eqCount K τ)) ({⟨j, hjn⟩} : Finset (Fin n)) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    have hi : (i : Nat) < insertPos K τ + eqCount K τ := (Finset.mem_filter.mp hi1).2.2
    have hij : i = ⟨j, hjn⟩ := Finset.mem_singleton.mp hi2
    have hval : (i : Nat) = j := by simpa using congrArg Fin.val hij
    omega
  have hsubU : Finset.univ.filter (fun i : Fin n => insertPos K τ ≤ (i : Nat) ∧
      (i : Nat) < insertPos K τ + eqCount K τ) ∪ ({⟨j, hjn⟩} : Finset (Fin n)) ⊆
      Finset.univ.filter (fun i : Fin n => K i = τ) := by
    intro i hi
    rw [Finset.mem_union] at hi
    rcases hi with h1 | h2
    · exact hsub h1
    · rw [Finset.mem_singleton] at h2
      rw [h2]
      exact hmem
  have hcard : (Finset.univ.filter (fun i : Fin n => insertPos K τ ≤ (i : Nat) ∧
      (i : Nat) < insertPos K τ + eqCount K τ)).card = eqCount K τ := by
    simpa [Nat.add_sub_cancel_left] using
      (card_fin_between (n := n) (a := insertPos K τ) (b := insertPos K τ + eqCount K τ)
        (by omega) (by omega))
  have hcardU : (Finset.univ.filter (fun i : Fin n => insertPos K τ ≤ (i : Nat) ∧
      (i : Nat) < insertPos K τ + eqCount K τ) ∪ ({⟨j, hjn⟩} : Finset (Fin n))).card =
      eqCount K τ + 1 := by
    rw [Finset.card_union_of_disjoint hdis]
    rw [hcard]
    simp
  have hle : eqCount K τ + 1 ≤ eqCount K τ := by
    rw [← hcardU]
    unfold eqCount
    exact Finset.card_le_card hsubU
  omega

/-- In a monotone vector the τ entries form exactly the interval
[insertPos, insertPos + eqCount). -/
theorem knotAt_eq_iff_between {n : Nat} [NeZero n] {K : Fin n → ℝ} (hK : Monotone K)
    (τ : ℝ) {j : Nat} (hjn : j < n) :
    knotAt K j = τ ↔ insertPos K τ ≤ j ∧ j < insertPos K τ + eqCount K τ := by
  constructor
  · intro hjτ
    exact ⟨knotAt_eq_ge_insertPos hK τ hjn hjτ, knotAt_eq_lt_add hK τ hjn hjτ⟩
  · intro h
    exact knotAt_eq_of_between hK τ h.1 h.2 hjn

/-- Entries at or above the flat block end are strictly above τ. -/
theorem knotAt_gt_of_ge_add {n : Nat} [NeZero n] {K : Fin n → ℝ} (hK : Monotone K)
    (τ : ℝ) {j : Nat} (hjn : j < n)
    (hpq : insertPos K τ + eqCount K τ ≤ j) : τ < knotAt K j := by
  have hne : knotAt K j ≠ τ := by
    intro hjτ
    have hlt : j < insertPos K τ + eqCount K τ := knotAt_eq_lt_add hK τ hjn hjτ
    exact (not_lt_of_ge hpq) hlt
  have hge : τ ≤ knotAt K j := by
    rw [knotAt_lt K j hjn]
    exact insertPos_ge_of_le hK τ (i := ⟨j, hjn⟩)
      (le_trans (Nat.le_add_right (insertPos K τ) (eqCount K τ)) hpq)
  exact lt_of_le_of_ne hge hne.symm

/-- Entries strictly below insertPos are strictly below τ. -/
theorem knotAt_lt_of_lt_insertPos {n : Nat} [NeZero n] {K : Fin n → ℝ} (hK : Monotone K)
    (τ : ℝ) {j : Nat} (hjn : j < n) (hj : j < insertPos K τ) : knotAt K j < τ := by
  rw [knotAt_lt K j hjn]
  exact insertPos_lt_of_lt hK τ hj

/-- If the last entry exceeds τ, the values below-or-equal τ number at
most n - 1. -/
theorem insertPos_add_eqCount_le_pred {n : Nat} [NeZero n] {K : Fin n → ℝ} (hK : Monotone K)
    (τ : ℝ) (hlast : τ < knotAt K (n - 1)) :
    insertPos K τ + eqCount K τ ≤ n - 1 := by
  have hdis : Disjoint (Finset.univ.filter (fun i : Fin n => K i < τ))
      (Finset.univ.filter (fun i : Fin n => K i = τ)) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    have h1 : K i < τ := (Finset.mem_filter.mp hi1).2
    have h2 : K i = τ := (Finset.mem_filter.mp hi2).2
    exact (ne_of_lt h1) h2
  have hunion : Finset.univ.filter (fun i : Fin n => K i < τ) ∪
      Finset.univ.filter (fun i : Fin n => K i = τ) =
      Finset.univ.filter (fun i : Fin n => K i ≤ τ) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro (⟨_, hlt⟩ | ⟨_, heq⟩)
      · exact ⟨Finset.mem_univ _, le_of_lt hlt⟩
      · exact ⟨Finset.mem_univ _, le_of_eq heq⟩
    · intro h
      rcases lt_or_eq_of_le h.2 with hlt | heq
      · exact Or.inl ⟨Finset.mem_univ _, hlt⟩
      · exact Or.inr ⟨Finset.mem_univ _, heq⟩
  have hcardU : (Finset.univ.filter (fun i : Fin n => K i ≤ τ)).card =
      (Finset.univ.filter (fun i : Fin n => K i < τ)).card +
        (Finset.univ.filter (fun i : Fin n => K i = τ)).card := by
    rw [← hunion]
    exact Finset.card_union_of_disjoint hdis
  have hsub : Finset.univ.filter (fun i : Fin n => K i ≤ τ) ⊆
      Finset.univ.erase ⟨n - 1, Nat.sub_one_lt (NeZero.ne n)⟩ := by
    intro i hi
    rw [Finset.mem_erase]
    refine ⟨?hne, Finset.mem_univ _⟩
    intro hie
    have hiτ : K i ≤ τ := (Finset.mem_filter.mp hi).2
    have hKi : knotAt K (n - 1) ≤ τ := by
      rw [knotAt_lt K (n - 1) (Nat.sub_one_lt (NeZero.ne n))]
      rw [← hie]
      exact hiτ
    exact lt_irrefl τ (lt_of_lt_of_le hlast hKi)
  have hcardle : (Finset.univ.filter (fun i : Fin n => K i ≤ τ)).card ≤ n - 1 := by
    have hle' := Finset.card_le_card hsub
    simpa [Finset.card_erase_of_mem (Finset.mem_univ (⟨n - 1, Nat.sub_one_lt (NeZero.ne n)⟩ : Fin n)), Fintype.card_fin] using hle'
  unfold insertPos eqCount
  exact (by simpa [hcardU] using hcardle)

/-- Values up to σ (inclusive) all count as strictly below a larger τ. -/
theorem insertPos_add_eqCount_le_insertPos {n : Nat} [NeZero n] {K : Fin n → ℝ} (hK : Monotone K)
    (σ τ : ℝ) (hστ : σ < τ) :
    insertPos K σ + eqCount K σ ≤ insertPos K τ := by
  have hdis : Disjoint (Finset.univ.filter (fun i : Fin n => K i < σ))
      (Finset.univ.filter (fun i : Fin n => K i = σ)) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    have h1 : K i < σ := (Finset.mem_filter.mp hi1).2
    have h2 : K i = σ := (Finset.mem_filter.mp hi2).2
    exact (ne_of_lt h1) h2
  have hsub : Finset.univ.filter (fun i : Fin n => K i < σ) ∪
      Finset.univ.filter (fun i : Fin n => K i = σ) ⊆
      Finset.univ.filter (fun i : Fin n => K i < τ) := by
    intro i hi
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Finset.mem_union] at hi
    rcases hi with h1 | h2
    · exact lt_trans (Finset.mem_filter.mp h1).2 hστ
    · have h2' : K i = σ := (Finset.mem_filter.mp h2).2
      simpa [h2'] using hστ
  have hcardU : (Finset.univ.filter (fun i : Fin n => K i < σ) ∪
      Finset.univ.filter (fun i : Fin n => K i = σ)).card =
      (Finset.univ.filter (fun i : Fin n => K i < σ)).card +
        (Finset.univ.filter (fun i : Fin n => K i = σ)).card :=
    Finset.card_union_of_disjoint hdis
  unfold insertPos eqCount
  rw [← hcardU]
  exact Finset.card_le_card hsub


/-- Filtering a constant list is all or nothing. -/
lemma List_filter_replicate {α : Type u} (p : α → Bool) (n : Nat) (a : α) :
    (List.replicate n a).filter p = if p a then List.replicate n a else [] := by
  induction n with
  | zero => simp
  | succ n ih =>
      by_cases h : p a
      · simp [h, ih]
      · simp [h, ih]

/-- The sum of a Fin-indexed function over finRange. -/
lemma List_sum_finRange_map {n : Nat} (f : Fin n → Nat) :
    ((List.finRange n).map f).sum = ∑ i : Fin n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.finRange_succ]
      rw [List.map_cons, List.sum_cons]
      rw [List.map_map]
      change f 0 + ((List.finRange n).map (fun i => f (Fin.succ i))).sum = ∑ i, f i
      rw [ih (fun i : Fin n => f (Fin.succ i))]
      rw [Fin.sum_univ_succ]

/-- The insertion list has one block of m-1 copies per sample. -/
lemma sampleInsertions_length {m : Nat} (x : Fin (2 * m) → ℝ) :
    (sampleInsertions x).length = 2 * m * (m - 1) := by
  unfold sampleInsertions
  rw [List.length_flatMap]
  have hmap : (List.finRange (2 * m)).map (fun r : Fin (2 * m) => (List.replicate (m - 1) (x r)).length) =
      (List.finRange (2 * m)).map (fun _ : Fin (2 * m) => m - 1) := by
    apply List.map_congr_left
    intro r _
    simp
  rw [hmap]
  rw [List_sum_finRange_map (fun _ : Fin (2 * m) => m - 1)]
  simp

/-- The inserted copies strictly below a sample number (r : Nat) * (m - 1). -/
lemma sampleInsertions_count_lt {m : Nat} (x : Fin (2 * m) → ℝ) (hx : StrictMono x)
    (r : Fin (2 * m)) :
    ((sampleInsertions x).filter (fun σ => σ < x r)).length = (r : Nat) * (m - 1) := by
  unfold sampleInsertions
  rw [List.filter_flatMap]
  simp only [List_filter_replicate]
  rw [List.length_flatMap]
  have hmap : (List.finRange (2 * m)).map (fun s : Fin (2 * m) =>
      (if decide (x s < x r) then List.replicate (m - 1) (x s) else []).length) =
      (List.finRange (2 * m)).map (fun s : Fin (2 * m) => if x s < x r then m - 1 else 0) := by
    apply List.map_congr_left
    intro s _
    by_cases hs : x s < x r <;> simp [hs]
  rw [hmap]
  rw [List_sum_finRange_map (fun s : Fin (2 * m) => if x s < x r then m - 1 else 0)]
  calc
    (∑ s : Fin (2 * m), (if x s < x r then m - 1 else 0))
        = ∑ s : Fin (2 * m), (m - 1) * (if x s < x r then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro s _
            by_cases hs : x s < x r <;> simp [hs]
    _ = (m - 1) * ∑ s : Fin (2 * m), (if x s < x r then 1 else 0) := by
            rw [Finset.mul_sum]
    _ = (m - 1) * (Finset.univ.filter (fun s : Fin (2 * m) => x s < x r)).card := by
            congr 1
            rw [Finset.card_filter]
    _ = (m - 1) * (Finset.univ.filter (fun s : Fin (2 * m) => (s : Nat) < (r : Nat))).card := by
            congr 1
            have hf : Finset.univ.filter (fun s : Fin (2 * m) => x s < x r) =
                Finset.univ.filter (fun s : Fin (2 * m) => (s : Nat) < (r : Nat)) := by
              ext s
              simp only [Finset.mem_filter]
              have hiff : x s < x r ↔ (s : Nat) < (r : Nat) :=
                (hx.lt_iff_lt.trans Fin.lt_iff_val_lt_val)
              exact ⟨fun h => ⟨Finset.mem_univ _, hiff.mp h.2⟩,
                fun h => ⟨Finset.mem_univ _, hiff.mpr h.2⟩⟩
            rw [hf]
    _ = (m - 1) * (r : Nat) := by
            rw [card_fin_below (2 * m) (r : Nat) (by omega)]
    _ = (r : Nat) * (m - 1) := by rw [Nat.mul_comm]

/-- The inserted copies equal to a sample number exactly m - 1. -/
lemma sampleInsertions_count_eq {m : Nat} (x : Fin (2 * m) → ℝ) (hx : StrictMono x)
    (r : Fin (2 * m)) :
    ((sampleInsertions x).filter (fun σ => σ = x r)).length = m - 1 := by
  unfold sampleInsertions
  rw [List.filter_flatMap]
  simp only [List_filter_replicate]
  rw [List.length_flatMap]
  have hmap : (List.finRange (2 * m)).map (fun s : Fin (2 * m) =>
      (if decide (x s = x r) then List.replicate (m - 1) (x s) else []).length) =
      (List.finRange (2 * m)).map (fun s : Fin (2 * m) => if x s = x r then m - 1 else 0) := by
    apply List.map_congr_left
    intro s _
    by_cases hs : x s = x r <;> simp [hs]
  rw [hmap]
  rw [List_sum_finRange_map (fun s : Fin (2 * m) => if x s = x r then m - 1 else 0)]
  calc
    (∑ s : Fin (2 * m), (if x s = x r then m - 1 else 0))
        = ∑ s : Fin (2 * m), (m - 1) * (if x s = x r then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro s _
            by_cases hs : x s = x r <;> simp [hs]
    _ = (m - 1) * ∑ s : Fin (2 * m), (if x s = x r then 1 else 0) := by
            rw [Finset.mul_sum]
    _ = (m - 1) * (Finset.univ.filter (fun s : Fin (2 * m) => x s = x r)).card := by
            congr 1
            rw [Finset.card_filter]
    _ = (m - 1) * 1 := by
            congr 1
            have hf : Finset.univ.filter (fun s : Fin (2 * m) => x s = x r) = ({r} : Finset (Fin (2 * m))) := by
              ext s
              simp only [Finset.mem_filter, Finset.mem_singleton]
              constructor
              · intro hs
                by_contra hne
                rcases lt_or_gt_of_ne hne with hlt | hgt
                · have hx' : x s < x r := hx hlt
                  exact lt_irrefl (x s) (lt_of_lt_of_le hx' hs.2.symm.le)
                · have hx' : x r < x s := hx hgt
                  exact lt_irrefl (x r) (lt_of_lt_of_le hx' hs.2.le)
              · intro hs
                rw [hs]
                simp
            rw [hf]
            simp
    _ = m - 1 := by simp


/-! ## Fine vector and the sample flat blocks -/

/-- The fine knot vector with m-1 copies of every sample inserted. -/
noncomputable def fineKnotVector {m : Nat} (D : TwoFanData m) (x : Fin (2 * m) → ℝ) :
    Fin (4 * m - 2 + 2 * m * (m - 1)) → ℝ := by
  letI : NeZero (4 * m - 2) := ⟨by have hm := D.hm; omega⟩
  exact fun i => insertList (sampleInsertions x) D.openKnot ⟨(i : Nat), by
    have hlen := sampleInsertions_length x
    omega⟩

/-- The fine vector is monotone. -/
theorem fineKnotVector_mono {m : Nat} (D : TwoFanData m) (x : Fin (2 * m) → ℝ) :
    Monotone (fineKnotVector D x) := by
  letI : NeZero (4 * m - 2) := ⟨by have hm := D.hm; omega⟩
  intro a b hab
  unfold fineKnotVector
  exact insertList_mono D.openKnot_mono (sampleInsertions x) (a := ⟨(a : Nat), by
    have hlen := sampleInsertions_length x
    omega⟩) (b := ⟨(b : Nat), by
    have hlen := sampleInsertions_length x
    omega⟩) (Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp hab))

/-- The start of the flat block of x r in the fine vector. -/
noncomputable def fineSampleAnchor {m : Nat} (D : TwoFanData m) (x : Fin (2 * m) → ℝ)
    (r : Fin (2 * m)) : Nat := by
  letI : NeZero (4 * m - 2) := ⟨by have hm := D.hm; omega⟩
  exact insertPos D.openKnot (x r) + (r : Nat) * (m - 1)

/-- The number of open-vector entries equal to x r. -/
noncomputable def fineSampleEqCount {m : Nat} (D : TwoFanData m) (x : Fin (2 * m) → ℝ)
    (r : Fin (2 * m)) : Nat := by
  letI : NeZero (4 * m - 2) := ⟨by have hm := D.hm; omega⟩
  exact eqCount D.openKnot (x r)

/-- insertPos in the fine vector at a sample. -/
theorem insertPos_fineKnotVector {m : Nat} (D : TwoFanData m) (x : Fin (2 * m) → ℝ)
    [instN : NeZero (4 * m - 2 + 2 * m * (m - 1))]
    (hx : StrictMono x) (r : Fin (2 * m)) :
    insertPos (fineKnotVector D x) (x r) = fineSampleAnchor D x r := by
  letI : NeZero (4 * m - 2) := ⟨by have hm := D.hm; omega⟩
  letI : NeZero (4 * m - 2 + (sampleInsertions x).length) := ⟨by have hm := D.hm; omega⟩
  letI : NeZero (4 * m - 2 + 2 * m * (m - 1)) := ⟨by have hm := D.hm; omega⟩
  unfold fineSampleAnchor fineKnotVector
  rw [insertPos_comp_finCast (insertList (sampleInsertions x) D.openKnot) (x r)
    (by rw [sampleInsertions_length x] : 4 * m - 2 + 2 * m * (m - 1) = 4 * m - 2 + (sampleInsertions x).length)]
  rw [insertPos_insertList D.openKnot_mono (sampleInsertions x) (x r)]
  rw [sampleInsertions_count_lt x hx r]

/-- eqCount in the fine vector at a sample. -/
theorem eqCount_fineKnotVector {m : Nat} (D : TwoFanData m) (x : Fin (2 * m) → ℝ)
    [instN : NeZero (4 * m - 2 + 2 * m * (m - 1))]
    (hx : StrictMono x) (r : Fin (2 * m)) :
    eqCount (fineKnotVector D x) (x r) = fineSampleEqCount D x r + (m - 1) := by
  letI : NeZero (4 * m - 2) := ⟨by have hm := D.hm; omega⟩
  letI : NeZero (4 * m - 2 + (sampleInsertions x).length) := ⟨by have hm := D.hm; omega⟩
  letI : NeZero (4 * m - 2 + 2 * m * (m - 1)) := ⟨by have hm := D.hm; omega⟩
  unfold fineSampleEqCount fineKnotVector
  rw [eqCount_comp_finCast (insertList (sampleInsertions x) D.openKnot) (x r)
    (by rw [sampleInsertions_length x] : 4 * m - 2 + 2 * m * (m - 1) = 4 * m - 2 + (sampleInsertions x).length)]
  rw [eqCount_insertList D.openKnot (sampleInsertions x) (x r)]
  rw [sampleInsertions_count_eq x hx r]

/-- The last open-vector entry is the right anchor. -/
theorem knotAt_openKnot_last {m : Nat} (D : TwoFanData m) [inst : NeZero (4 * m - 2)] :
    knotAt D.openKnot (4 * m - 3) = D.rightAnchor := by
  letI : NeZero (4 * m - 2) := ⟨by have hm := D.hm; omega⟩
  rw [knotAt_lt D.openKnot (4 * m - 3) (by have hm := D.hm; omega)]
  simp only [TwoFanData.openKnot]
  have hm := D.hm
  by_cases h1 : 4 * m - 3 < m - 1
  · exfalso; omega
  · by_cases h2 : 4 * m - 3 < 3 * m - 1
    · exfalso; omega
    · simp [h1, h2]

/-- The first open-vector entry is the left anchor. -/
theorem knotAt_openKnot_first {m : Nat} (D : TwoFanData m) [inst : NeZero (4 * m - 2)] :
    knotAt D.openKnot 0 = D.leftAnchor := by
  letI : NeZero (4 * m - 2) := ⟨by have hm := D.hm; omega⟩
  rw [knotAt_lt D.openKnot 0 (by have hm := D.hm; omega)]
  simp only [TwoFanData.openKnot]
  have hm := D.hm
  by_cases h1 : 0 < m - 1
  · simp [h1]
  · exfalso; omega

/-- The fine anchor sits strictly below the fine length. -/
theorem fineSampleAnchor_lt_length {m : Nat} (D : TwoFanData m) (x : Fin (2 * m) → ℝ)
    (hx : StrictMono x) (hinside : SamplesInsideAnchors D x) (r : Fin (2 * m)) :
    fineSampleAnchor D x r + fineSampleEqCount D x r + (m - 1) ≤
      4 * m - 2 + 2 * m * (m - 1) - 1 := by
  letI : NeZero (4 * m - 2) := ⟨by have hm := D.hm; omega⟩
  have hlast : x r < knotAt D.openKnot (4 * m - 3) := by
    rw [knotAt_openKnot_last D]
    exact (hinside r).2
  have hle0 : insertPos D.openKnot (x r) + eqCount D.openKnot (x r) ≤ 4 * m - 3 :=
    insertPos_add_eqCount_le_pred D.openKnot_mono (x r) hlast
  have hmul : (r : Nat) * (m - 1) + (m - 1) ≤ 2 * m * (m - 1) := by
    have hmul' : (r : Nat) * (m - 1) + (m - 1) = ((r : Nat) + 1) * (m - 1) := by
      rw [Nat.add_mul]
      simp
    rw [hmul']
    exact Nat.mul_le_mul_right (m - 1) (by omega : (r : Nat) + 1 ≤ 2 * m)
  unfold fineSampleAnchor fineSampleEqCount
  have hm := D.hm
  omega

/-- Each sample sits in a flat block of its copies with strict neighbours. -/
theorem fineSample_block {m : Nat} (D : TwoFanData m) (x : Fin (2 * m) → ℝ)
    [instN : NeZero (4 * m - 2 + 2 * m * (m - 1))]
    (hx : StrictMono x) (hinside : SamplesInsideAnchors D x) (r : Fin (2 * m)) :
    (∀ j, fineSampleAnchor D x r ≤ j → j < fineSampleAnchor D x r + fineSampleEqCount D x r + (m - 1) →
      knotAt (fineKnotVector D x) j = x r) ∧
    (0 < fineSampleAnchor D x r → knotAt (fineKnotVector D x) (fineSampleAnchor D x r - 1) < x r) ∧
    (fineSampleAnchor D x r + fineSampleEqCount D x r + (m - 1) < 4 * m - 2 + 2 * m * (m - 1) →
      x r < knotAt (fineKnotVector D x) (fineSampleAnchor D x r + fineSampleEqCount D x r + (m - 1))) := by
  letI : NeZero (4 * m - 2) := ⟨by have hm := D.hm; omega⟩
  letI : NeZero (4 * m - 2 + 2 * m * (m - 1)) := ⟨by have hm := D.hm; omega⟩
  have hp := insertPos_fineKnotVector D x hx r
  have hq := eqCount_fineKnotVector D x hx r
  have hleN := fineSampleAnchor_lt_length D x hx hinside r
  have hmono := fineKnotVector_mono D x
  constructor
  · intro j hj1 hj2
    have hj' : j < insertPos (fineKnotVector D x) (x r) + eqCount (fineKnotVector D x) (x r) := by
      rw [hp, hq]
      omega
    have hj1' : insertPos (fineKnotVector D x) (x r) ≤ j := by
      rw [hp]
      exact hj1
    have hjn : j < 4 * m - 2 + 2 * m * (m - 1) := by
      have hle' : insertPos (fineKnotVector D x) (x r) + eqCount (fineKnotVector D x) (x r) ≤
          4 * m - 2 + 2 * m * (m - 1) - 1 := by
        rw [hp, hq]
        simpa [Nat.add_assoc] using hleN
      omega
    exact knotAt_eq_of_between hmono (x r) hj1' hj' hjn
  · constructor
    · intro hp0
      have hlt : fineSampleAnchor D x r - 1 < insertPos (fineKnotVector D x) (x r) := by
        rw [hp]
        exact Nat.sub_one_lt (Nat.ne_of_gt hp0)
      have hjn : fineSampleAnchor D x r - 1 < 4 * m - 2 + 2 * m * (m - 1) := by
        have hle' : fineSampleAnchor D x r ≤ 4 * m - 2 + 2 * m * (m - 1) - 1 := by omega
        omega
      exact knotAt_lt_of_lt_insertPos hmono (x r) hjn hlt
    · intro hgt
      have hb : fineSampleAnchor D x r + fineSampleEqCount D x r + (m - 1) ≤
          4 * m - 2 + 2 * m * (m - 1) - 1 := hleN
      have hpq : insertPos (fineKnotVector D x) (x r) + eqCount (fineKnotVector D x) (x r) ≤
          fineSampleAnchor D x r + fineSampleEqCount D x r + (m - 1) := by
        rw [hp, hq]
        omega
      exact knotAt_gt_of_ge_add hmono (x r) hgt hpq


/-! ## Selector structure and the maximal-minor theorem -/

/-- The selector column value of sample r. -/
noncomputable def fineSelectorVal {m : Nat} (D : TwoFanData m) (x : Fin (2 * m) → ℝ)
    (r : Fin (2 * m)) : Nat :=
  fineSampleAnchor D x r + fineSampleEqCount D x r

/-- The selector column of sample r in the fine collocation matrix. -/
noncomputable def fineSelectorPos {m : Nat} (D : TwoFanData m) (x : Fin (2 * m) → ℝ)
    (hinside : SamplesInsideAnchors D x) :
    Fin (2 * m) → Fin (3 * m - 1 + 2 * m * (m - 1)) := by
  letI : NeZero (4 * m - 2) := ⟨by have hm := D.hm; omega⟩
  intro r
  refine ⟨fineSampleAnchor D x r + fineSampleEqCount D x r, ?_⟩
  have hle0 : insertPos D.openKnot (x r) + eqCount D.openKnot (x r) ≤ 4 * m - 3 := by
    have hlast : x r < knotAt D.openKnot (4 * m - 3) := by
      rw [knotAt_openKnot_last D]
      exact (hinside r).2
    exact insertPos_add_eqCount_le_pred D.openKnot_mono (x r) hlast
  have hmul : (r : Nat) * (m - 1) ≤ (2 * m - 1) * (m - 1) :=
    Nat.mul_le_mul_right (m - 1) (by omega : (r : Nat) ≤ 2 * m - 1)
  have hmul' : (2 * m - 1) * (m - 1) + (m - 1) = 2 * m * (m - 1) := by
    calc
      (2 * m - 1) * (m - 1) + (m - 1) = ((2 * m - 1) + 1) * (m - 1) := by
        rw [Nat.add_mul]
        simp
      _ = 2 * m * (m - 1) := by
        congr 1
        exact Nat.sub_add_cancel (by have hm := D.hm; omega : 1 ≤ 2 * m)
  unfold fineSampleAnchor fineSampleEqCount
  have hm := D.hm
  have hm1 : 1 ≤ m - 1 := by omega
  have hsum : insertPos D.openKnot (x r) + (r : Nat) * (m - 1) + eqCount D.openKnot (x r) ≤
      4 * m - 3 + (2 * m - 1) * (m - 1) := by
    have hre : insertPos D.openKnot (x r) + (r : Nat) * (m - 1) + eqCount D.openKnot (x r) =
        insertPos D.openKnot (x r) + eqCount D.openKnot (x r) + (r : Nat) * (m - 1) := by
      ac_rfl
    rw [hre]
    exact Nat.add_le_add hle0 hmul
  have hlt : 4 * m - 3 + (2 * m - 1) * (m - 1) < 3 * m - 1 + 2 * m * (m - 1) := by
    rw [← hmul']
    omega
  exact lt_of_le_of_lt hsum hlt

/-- The selector values are strictly increasing across samples. -/
theorem fineSelector_strictMono {m : Nat} (D : TwoFanData m) (x : Fin (2 * m) → ℝ)
    (hx : StrictMono x) : StrictMono (fun r => fineSelectorVal D x r) := by
  letI : NeZero (4 * m - 2) := ⟨by have hm := D.hm; omega⟩
  intro r s hrs
  unfold fineSelectorVal fineSampleAnchor fineSampleEqCount
  have hm := D.hm
  have hge : insertPos D.openKnot (x r) + eqCount D.openKnot (x r) ≤ insertPos D.openKnot (x s) :=
    insertPos_add_eqCount_le_insertPos D.openKnot_mono (x r) (x s) (hx hrs)
  have hmul : (r : Nat) * (m - 1) + (m - 1) ≤ (s : Nat) * (m - 1) := by
    have hmul' : (r : Nat) * (m - 1) + (m - 1) = ((r : Nat) + 1) * (m - 1) := by
      rw [Nat.add_mul]
      simp
    rw [hmul']
    exact Nat.mul_le_mul_right (m - 1) (by omega : (r : Nat) + 1 ≤ (s : Nat))
  have hsum : insertPos D.openKnot (x r) + eqCount D.openKnot (x r) + (r : Nat) * (m - 1) <
      insertPos D.openKnot (x s) + (s : Nat) * (m - 1) := by
    have hlt : (r : Nat) * (m - 1) < (r : Nat) * (m - 1) + (m - 1) := by
      omega
    have h2 : insertPos D.openKnot (x s) + (r : Nat) * (m - 1) <
        insertPos D.openKnot (x s) + (s : Nat) * (m - 1) := by
      omega
    have h1 : insertPos D.openKnot (x r) + eqCount D.openKnot (x r) + (r : Nat) * (m - 1) ≤
        insertPos D.openKnot (x s) + (r : Nat) * (m - 1) := by
      omega
    exact lt_of_le_of_lt h1 h2
  change (insertPos D.openKnot (x r) + (r : Nat) * (m - 1) + eqCount D.openKnot (x r)) <
    (insertPos D.openKnot (x s) + (s : Nat) * (m - 1) + eqCount D.openKnot (x s))
  omega

/-- The degree m-2 B-spline at a sample is the selector at the block start. -/
theorem fineSelector_apply {m : Nat} (D : TwoFanData m) (x : Fin (2 * m) → ℝ)
    [instN : NeZero (4 * m - 2 + 2 * m * (m - 1))]
    (hx : StrictMono x) (hinside : SamplesInsideAnchors D x) (r : Fin (2 * m)) (j : Nat)
    (hj : j + (m - 2) + 1 ≤ 4 * m - 2 + 2 * m * (m - 1)) :
    splineOn (fineKnotVector D x) j (m - 2) (x r) = if j = fineSelectorVal D x r then 1 else 0 := by
  letI : NeZero (4 * m - 2) := ⟨by have hm := D.hm; omega⟩
  have hblock := fineSample_block D x hx hinside r
  have hleN := fineSampleAnchor_lt_length D x hx hinside r
  have hm0 : 2 ≤ m := D.hm
  have ha0 : 0 < fineSampleAnchor D x r := by
    have hmem : ⟨0, by have hm := D.hm; omega⟩ ∈
        Finset.univ.filter (fun i : Fin (4 * m - 2) => D.openKnot i < x r) := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← knotAt_lt D.openKnot 0 (by have hm := D.hm; omega)]
      rw [knotAt_openKnot_first D]
      exact (hinside r).1
    have hpos : 0 < (Finset.univ.filter (fun i : Fin (4 * m - 2) => D.openKnot i < x r)).card :=
      Finset.card_pos.mpr ⟨⟨0, by have hm := D.hm; omega⟩, hmem⟩
    change 0 < insertPos D.openKnot (x r) + (r : Nat) * (m - 1)
    exact Nat.lt_of_lt_of_le hpos (Nat.le_add_right _ ((r : Nat) * (m - 1)))
  have hsum1 : 1 ≤ fineSampleAnchor D x r + fineSampleEqCount D x r + (m - 1) := by omega
  have hb1 : (fineSampleAnchor D x r + fineSampleEqCount D x r + (m - 1) - 1) + 1 =
      fineSampleAnchor D x r + fineSampleEqCount D x r + (m - 1) := by omega
  have hbn : fineSampleAnchor D x r + fineSampleEqCount D x r + (m - 1) - 1 + 1 <
      4 * m - 2 + 2 * m * (m - 1) := by
    rw [hb1]
    omega
  have hb : fineSampleAnchor D x r ≤
      fineSampleAnchor D x r + fineSampleEqCount D x r + (m - 1) - 1 := by
    have hm := D.hm
    omega
  have hleft' : knotAt (fineKnotVector D x) (fineSampleAnchor D x r - 1) < x r := by
    have hlt : fineSampleAnchor D x r - 1 < insertPos (fineKnotVector D x) (x r) := by
      rw [insertPos_fineKnotVector D x hx r]
      exact Nat.sub_one_lt (Nat.ne_of_gt ha0)
    have hjn : fineSampleAnchor D x r - 1 < 4 * m - 2 + 2 * m * (m - 1) := by omega
    exact knotAt_lt_of_lt_insertPos (fineKnotVector_mono D x) (x r) hjn hlt
  have hright' : x r < knotAt (fineKnotVector D x)
      (fineSampleAnchor D x r + fineSampleEqCount D x r + (m - 1) - 1 + 1) := by
    rw [hb1]
    exact hblock.2.2 (by omega : fineSampleAnchor D x r + fineSampleEqCount D x r + (m - 1) <
      4 * m - 2 + 2 * m * (m - 1))
  have hsel := splineOn_flat_selector (fineKnotVector_mono D x) (x r) (m - 2) hb hbn
    (by
      have hm := D.hm
      omega : m - 2 ≤ fineSampleAnchor D x r + fineSampleEqCount D x r + (m - 1) - 1 - fineSampleAnchor D x r)
    (by
      intro j hj1 hj2
      exact hblock.1 j hj1 (by omega : j < fineSampleAnchor D x r + fineSampleEqCount D x r + (m - 1)))
    hleft' hright'
  have hselval : fineSampleAnchor D x r + fineSampleEqCount D x r + (m - 1) - 1 - (m - 2) = fineSelectorVal D x r := by
    unfold fineSelectorVal
    omega
  simpa [hselval] using hsel j hj

/-- The fine collocation matrix. -/
noncomputable def fineCollocation {m : Nat} (D : TwoFanData m) (x : Fin (2 * m) → ℝ) :
    Matrix (Fin (2 * m)) (Fin (3 * m - 1 + 2 * m * (m - 1))) ℝ := by
  letI : NeZero (4 * m - 2 + 2 * m * (m - 1)) := ⟨by have hm := D.hm; omega⟩
  exact fun r j => splineOn (fineKnotVector D x) (j : Nat) (m - 2) (x r)

/-- The transpose of the fine refinement matrix. -/
noncomputable def fineRefineMatrix {m : Nat} (D : TwoFanData m) (x : Fin (2 * m) → ℝ) :
    Matrix (Fin (3 * m - 1 + 2 * m * (m - 1))) (Fin (3 * m - 1)) ℝ := by
  letI : NeZero (4 * m - 2) := ⟨by have hm := D.hm; omega⟩
  exact fun j i => refineList (sampleInsertions x) D.openKnot (m - 2)
    ⟨(i : Nat), by have hm := D.hm; omega⟩ ⟨(j : Nat), by
      have hlen := sampleInsertions_length x
      have hm := D.hm
      omega⟩

/-- The fine collocation matrix is a selector matrix. -/
theorem fineCollocation_selector {m : Nat} (D : TwoFanData m) (x : Fin (2 * m) → ℝ)
    [instN : NeZero (4 * m - 2 + 2 * m * (m - 1))]
    (hx : StrictMono x) (hinside : SamplesInsideAnchors D x) :
    (fun r j => if j = (fineSelectorPos D x hinside r) then (1 : ℝ) else 0) = fineCollocation D x := by
  funext r j
  symm
  unfold fineCollocation
  have hsel := fineSelector_apply D x hx hinside r (j : Nat) (by
    have hlen := sampleInsertions_length x
    have hm := D.hm
    omega : (j : Nat) + (m - 2) + 1 ≤ 4 * m - 2 + 2 * m * (m - 1))
  rw [hsel]
  by_cases hj : j = fineSelectorPos D x hinside r
  · subst hj
    simp [fineSelectorPos, fineSelectorVal]
  · have hjn : ¬ (j : Nat) = fineSelectorVal D x r := by
      intro h
      exact hj (by
        apply Fin.ext
        simpa [fineSelectorPos, fineSelectorVal] using h)
    simp [hjn, hj]

/-- The fine collocation matrix is totally nonnegative. -/
theorem fineCollocation_tn {m : Nat} (D : TwoFanData m) (x : Fin (2 * m) → ℝ)
    [instN : NeZero (4 * m - 2 + 2 * m * (m - 1))]
    (hx : StrictMono x) (hinside : SamplesInsideAnchors D x) :
    IsTotallyNonnegative (fineCollocation D x) := by
  have hsel := fineCollocation_selector D x hx hinside
  have hsm : StrictMono (fun r => fineSelectorVal D x r) := fineSelector_strictMono D x hx
  have hsm' : StrictMono (fineSelectorPos D x hinside) := by
    intro r s hrs
    apply Fin.lt_def.mpr
    have h := hsm hrs
    simpa [fineSelectorPos] using h
  have htn := selectorMatrix_isTotallyNonnegative (fineSelectorPos D x hinside) hsm'
  rw [← hsel]
  exact htn

/-- The transpose of the refinement matrix is totally nonnegative. -/
theorem fineRefineMatrix_tn {m : Nat} (D : TwoFanData m) (x : Fin (2 * m) → ℝ) :
    IsTotallyNonnegative (fineRefineMatrix D x) := by
  letI : NeZero (4 * m - 2) := ⟨by have hm := D.hm; omega⟩
  have htn := refineList_isTotallyNonnegative (sampleInsertions x) D.openKnot D.openKnot_mono (m - 2)
  have hC : 3 * m - 1 + 2 * m * (m - 1) = 4 * m - 2 + (sampleInsertions x).length - (m - 2) - 1 := by
    have hlen := sampleInsertions_length x
    have hm := D.hm
    have hm2 : (m - 2) + 1 = m - 1 := by omega
    omega
  have hR : 3 * m - 1 = 4 * m - 2 - (m - 2) - 1 := by
    have hm := D.hm
    have hm2 : (m - 2) + 1 = m - 1 := by omega
    omega
  have htranspose : fineRefineMatrix D x =
      (Matrix.transpose (refineList (sampleInsertions x) D.openKnot (m - 2))).submatrix
        (finCastShuffleEmb hC) (finCastShuffleEmb hR) := by
    ext j i
    unfold fineRefineMatrix
    rfl
  rw [htranspose]
  exact isTotallyNonnegative_submatrix
    (Matrix.transpose (refineList (sampleInsertions x) D.openKnot (m - 2)))
    (finCastShuffleEmb hC) (finCastShuffleEmb hR)
    ((isTotallyNonnegative_transpose_iff (refineList (sampleInsertions x) D.openKnot (m - 2))).mpr htn)

/-- The fine collocation matrix factorizes the paper collocation matrix. -/
theorem fineFactor_eq {m : Nat} (D : TwoFanData m) (x : Fin (2 * m) → ℝ) :
    bsplineCollocation D x = fineCollocation D x * fineRefineMatrix D x := by
  letI : NeZero (4 * m - 2) := ⟨by have hm := D.hm; omega⟩
  letI : NeZero (4 * m - 2 + (sampleInsertions x).length) := ⟨by have hm := D.hm; omega⟩
  letI : NeZero (4 * m - 2 + 2 * m * (m - 1)) := ⟨by have hm := D.hm; omega⟩
  ext r i
  unfold bsplineCollocation paperBSpline fineCollocation fineRefineMatrix
  rw [splineOn_refineList D.openKnot D.openKnot_mono (sampleInsertions x) (m - 2) (i : Nat)
    (by have hm := D.hm; omega : (i : Nat) < 4 * m - 2 - (m - 2) - 1) (x r)]
  rw [sum_finCast (by
    have hlen := sampleInsertions_length x
    have hm := D.hm
    have hm2 : (m - 2) + 1 = m - 1 := by omega
    omega : 4 * m - 2 + (sampleInsertions x).length - (m - 2) - 1 = 3 * m - 1 + 2 * m * (m - 1))
    (fun j : Fin (4 * m - 2 + (sampleInsertions x).length - (m - 2) - 1) =>
      refineList (sampleInsertions x) D.openKnot (m - 2) ⟨(i : Nat), by have hm := D.hm; omega⟩ j *
        splineOn (insertList (sampleInsertions x) D.openKnot) (j : Nat) (m - 2) (x r))]
  apply Finset.sum_congr rfl
  intro j _
  have hknot : knotAt (fineKnotVector D x) = knotAt (insertList (sampleInsertions x) D.openKnot) := by
    funext z
    unfold fineKnotVector
    simp [knotAt, sampleInsertions_length x]
  rw [← splineOn_congr' hknot (j : Nat) (m - 2) (x r)]
  ring

/-- Every maximal minor of the paper B-spline collocation matrix is nonnegative. -/
theorem bsplineCollocation_maximalMinor_nonneg
    {m : Nat} (D : TwoFanData m) (hm : 3 ≤ m)
    (x : Fin (2 * m) → ℝ) (hx : StrictMono x)
    (hinside : SamplesInsideAnchors D x)
    (cols : Fin (2 * m) ↪o Fin (3 * m - 1)) :
    0 ≤ matrixMinor (bsplineCollocation D x)
      (OrderEmbedding.id _) cols := by
  letI : NeZero (4 * m - 2 + 2 * m * (m - 1)) := ⟨by have hm := D.hm; omega⟩
  have hfac := fineFactor_eq D x
  have hB := fineCollocation_tn D x hx hinside
  have hC := fineRefineMatrix_tn D x
  rw [hfac]
  exact matrixMinor_mul_nonneg (fineCollocation D x) (fineRefineMatrix D x) hB hC
    (OrderEmbedding.id _) cols

end

end ColomboGeneralK2.Odd
