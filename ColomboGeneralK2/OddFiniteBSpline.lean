import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Ring.Finset
import ColomboGeneralK2.OddTwoFanKnotOrder
import ColomboGeneralK2.OddDeBruijnSignatures

/-!
# Finite normalized B-splines on the open two-fan knot vector

This module builds the finite Cox--de Boor layer used by the Marsden
factorization.  The recursion is defined for an arbitrary finite knot
vector `K : Fin n → ℝ` and Nat-indexed degree/index parameters; knot access
beyond the vector is clamped to the last knot, so the monotone-support
lemmas behave like an infinite nondecreasing extension.

The public paper interface is `paperBSpline`, the normalized degree `m-2`
B-spline on `TwoFanData.openKnot`.
-/

open scoped BigOperators

namespace ColomboGeneralK2.Odd

noncomputable section

/-- Knot access clamped to the last entry of a nonempty finite vector. -/
def knotAt {n : Nat} [NeZero n] (K : Fin n → ℝ) (j : Nat) : ℝ :=
  if h : j < n then K ⟨j, h⟩ else K ⟨n - 1, Nat.sub_one_lt (NeZero.ne n)⟩

@[simp]
theorem knotAt_lt {n : Nat} [NeZero n] (K : Fin n → ℝ) (j : Nat) (h : j < n) :
    knotAt K j = K ⟨j, h⟩ := by
  simp [knotAt, h]

@[simp]
theorem knotAt_ge {n : Nat} [NeZero n] (K : Fin n → ℝ) (j : Nat) (h : n ≤ j) :
    knotAt K j = K ⟨n - 1, Nat.sub_one_lt (NeZero.ne n)⟩ := by
  simp [knotAt, not_lt_of_ge h]

/-- Clamping preserves monotonicity. -/
theorem knotAt_mono {n : Nat} [NeZero n] {K : Fin n → ℝ} (hK : Monotone K) :
    Monotone (knotAt K) := by
  intro a b hab
  unfold knotAt
  by_cases ha : a < n
  · by_cases hb : b < n
    · simp [ha, hb]
      exact hK (by omega)
    · simp [ha, hb]
      exact hK (Fin.le_iff_val_le_val.mpr (Nat.le_pred_of_lt ha))
  · by_cases hb : b < n
    · omega
    · simp [ha, hb]

/-- The one-step shift of a finite vector, dropping the last slot. -/
def shiftVec {n : Nat} (K : Fin (n + 1) → ℝ) : Fin n → ℝ :=
  fun i ↦ K ⟨i + 1, Nat.succ_lt_succ i.isLt⟩

/-- The clamped extension of the shifted finite vector is the shifted clamped
extension. -/
theorem knotAt_shiftVec {n : Nat} [NeZero n] (K : Fin (n + 1) → ℝ) (j : Nat) :
    knotAt (shiftVec K) j = knotAt K (j + 1) := by
  unfold knotAt
  by_cases hj : j < n
  · have hj' : j + 1 < n + 1 := by omega
    simp [hj, hj', shiftVec]
  · have hj' : ¬(j + 1 < n + 1) := by omega
    simp [hj, hj', shiftVec]
    have hn : n - 1 + 1 = n := by
      have h1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne n))
      omega
    simp [hn]
/-- Left Cox--de Boor weight, with the standard zero-denominator convention. -/
def wLK {n : Nat} [NeZero n] (K : Fin n → ℝ) (i k : Nat) (y : ℝ) : ℝ :=
  if knotAt K (i + k + 1) - knotAt K i = 0 then 0
  else (y - knotAt K i) / (knotAt K (i + k + 1) - knotAt K i)

/-- Right Cox--de Boor weight, with the standard zero-denominator convention. -/
def wRK {n : Nat} [NeZero n] (K : Fin n → ℝ) (i k : Nat) (y : ℝ) : ℝ :=
  if knotAt K (i + k + 2) - knotAt K (i + 1) = 0 then 0
  else (knotAt K (i + k + 2) - y) / (knotAt K (i + k + 2) - knotAt K (i + 1))

/-- The finite Cox--de Boor recursion.  `splineOn K i k y` is the normalized
degree-`k` B-spline with window `(K i, ..., K (i+k+1))`, evaluated at `y`.
The degree-zero base uses the half-open convention `[K i, K (i+1))`. -/
def splineOn {n : Nat} [NeZero n] (K : Fin n → ℝ) : Nat → Nat → ℝ → ℝ
  | i, 0, y => if knotAt K i ≤ y ∧ y < knotAt K (i + 1) then 1 else 0
  | i, k + 1, y =>
      wLK K i k y * splineOn K i k y + wRK K i k y * splineOn K (i + 1) k y

@[simp]
theorem splineOn_succ {n : Nat} [NeZero n] (K : Fin n → ℝ) (i k : Nat) (y : ℝ) :
    splineOn K i (k + 1) y =
      wLK K i k y * splineOn K i k y + wRK K i k y * splineOn K (i + 1) k y := by
  simp only [splineOn]

@[simp]
theorem splineOn_zero {n : Nat} [NeZero n] (K : Fin n → ℝ) (i : Nat) (y : ℝ) :
    splineOn K i 0 y = if knotAt K i ≤ y ∧ y < knotAt K (i + 1) then 1 else 0 := by
  simp only [splineOn]

/-- Support: a nonzero B-spline value forces the half-open window. -/
theorem splineOn_support {n : Nat} [NeZero n] {K : Fin n → ℝ} (hK : Monotone K)
    (i k : Nat) (y : ℝ) (h : splineOn K i k y ≠ 0) :
    knotAt K i ≤ y ∧ y < knotAt K (i + k + 1) := by
  induction k generalizing i with
  | zero =>
      by_cases hc : knotAt K i ≤ y ∧ y < knotAt K (i + 1)
      · exact hc
      · simp [hc] at h
  | succ k ih =>
      rw [splineOn_succ] at h
      have hsum : wLK K i k y * splineOn K i k y ≠ 0 ∨
          wRK K i k y * splineOn K (i + 1) k y ≠ 0 := by
        by_contra hnot
        push_neg at hnot
        exact h (by rw [hnot.1, hnot.2, zero_add])
      rcases hsum with hL | hR
      · have hN : splineOn K i k y ≠ 0 := right_ne_zero_of_mul hL
        have hs := ih i hN
        exact ⟨hs.1, lt_of_lt_of_le hs.2 ((knotAt_mono hK)
          (show i + k + 1 ≤ i + k + 2 by omega))⟩
      · have hN : splineOn K (i + 1) k y ≠ 0 := right_ne_zero_of_mul hR
        have hs := ih (i + 1) hN
        exact ⟨le_trans ((knotAt_mono hK) (show i ≤ i + 1 by omega)) hs.1, by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs.2⟩

/-- A flat window produces the identically zero spline. -/
theorem splineOn_eq_zero_of_flat {n : Nat} [NeZero n] {K : Fin n → ℝ} (hK : Monotone K)
    (i k : Nat) (y : ℝ) (h : knotAt K i = knotAt K (i + k + 1)) :
    splineOn K i k y = 0 := by
  induction k generalizing i with
  | zero =>
      rw [splineOn_zero]
      have hz : ¬(knotAt K i ≤ y ∧ y < knotAt K (i + 1)) := by
        rintro ⟨_hle, hlt⟩
        rw [← h] at hlt
        exact not_lt_of_ge _hle hlt
      simp [hz]
  | succ k ih =>
      rw [splineOn_succ]
      have hwL : wLK K i k y = 0 := by
        unfold wLK
        have hle1' : knotAt K i ≤ knotAt K (i + k + 1) :=
          (knotAt_mono hK) (show i ≤ i + k + 1 by omega)
        have hle2' : knotAt K (i + k + 1) ≤ knotAt K i := by
          rw [h]
          exact (knotAt_mono hK) (show i + k + 1 ≤ i + (k + 1) + 1 by omega)
        have hden : knotAt K (i + k + 1) - knotAt K i = 0 :=
          sub_eq_zero.mpr (le_antisymm hle2' hle1')
        simp [hden]
      have hflat : knotAt K (i + 1) = knotAt K ((i + 1) + k + 1) := by
        have hle2 : knotAt K (i + 1) ≤ knotAt K ((i + 1) + k + 1) :=
          (knotAt_mono hK) (show i + 1 ≤ (i + 1) + k + 1 by omega)
        have hle3 : knotAt K ((i + 1) + k + 1) ≤ knotAt K i := by
          have : (i + 1) + k + 1 = i + (k + 1) + 1 := by omega
          rw [this, ← h]
        have hle3' : knotAt K ((i + 1) + k + 1) ≤ knotAt K (i + 1) :=
          le_trans hle3 ((knotAt_mono hK) (show i ≤ i + 1 by omega))
        exact le_antisymm hle2 hle3'
      rw [hwL, zero_mul, zero_add]
      rw [ih (i + 1) hflat, mul_zero]
/-- Entrywise nonnegativity of the normalized B-splines. -/
theorem splineOn_nonneg {n : Nat} [NeZero n] {K : Fin n → ℝ} (hK : Monotone K)
    (i k : Nat) (y : ℝ) : 0 ≤ splineOn K i k y := by
  induction k generalizing i with
  | zero =>
      rw [splineOn_zero]
      by_cases h : knotAt K i ≤ y ∧ y < knotAt K (i + 1) <;> simp [h]
  | succ k ih =>
      rw [splineOn_succ]
      apply add_nonneg
      · by_cases hN : splineOn K i k y = 0
        · rw [hN, mul_zero]
        · have hs := splineOn_support hK i k y hN
          have hden_pos : 0 < knotAt K (i + k + 1) - knotAt K i := by
            apply sub_pos.mpr
            apply lt_of_le_of_ne ((knotAt_mono hK) (show i ≤ i + k + 1 by omega))
            intro hflat
            have hN' : splineOn K i k y ≠ 0 := hN
            rw [splineOn_eq_zero_of_flat hK i k y hflat] at hN'
            contradiction
          have hwL' : 0 ≤ wLK K i k y := by
            unfold wLK
            by_cases hz : knotAt K (i + k + 1) - knotAt K i = 0
            · simp [hz]
            · simp [hz]
              exact div_nonneg (sub_nonneg.mpr hs.1) hden_pos.le
          exact mul_nonneg hwL' (ih i)
      · by_cases hN : splineOn K (i + 1) k y = 0
        · rw [hN, mul_zero]
        · have hs := splineOn_support hK (i + 1) k y hN
          have hden_pos : 0 < knotAt K (i + k + 2) - knotAt K (i + 1) := by
            apply sub_pos.mpr
            apply lt_of_le_of_ne ((knotAt_mono hK) (show i + 1 ≤ i + k + 2 by omega))
            intro hflat
            have hN' : splineOn K (i + 1) k y ≠ 0 := hN
            rw [splineOn_eq_zero_of_flat hK (i + 1) k y
              (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hflat)] at hN'
            contradiction
          have hwR' : 0 ≤ wRK K i k y := by
            unfold wRK
            by_cases hz : knotAt K (i + k + 2) - knotAt K (i + 1) = 0
            · simp [hz]
            · simp [hz]
              exact div_nonneg
                (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                  sub_nonneg.mpr hs.2.le) hden_pos.le
          exact mul_nonneg hwR' (ih (i + 1))

/-- The value at the left endpoint of a window with a simple first knot is
zero in every positive degree. -/
theorem splineOn_leftEndpoint_zero {n : Nat} [NeZero n] {K : Fin n → ℝ} (hK : Monotone K)
    {i k : Nat} (hk : 0 < k) (hsimple : knotAt K i < knotAt K (i + 1)) :
    splineOn K i k (knotAt K i) = 0 := by
  induction k with
  | zero => omega
  | succ k ih =>
      rw [splineOn_succ]
      have hwL : wLK K i k (knotAt K i) = 0 := by
        unfold wLK
        by_cases hz : knotAt K (i + k + 1) - knotAt K i = 0 <;> simp [hz]
      rw [hwL, zero_mul, zero_add]
      have hN : splineOn K (i + 1) k (knotAt K i) = 0 := by
        by_contra hne
        have hs := splineOn_support hK (i + 1) k (knotAt K i) hne
        exact not_lt_of_ge hs.1 hsimple
      rw [hN, mul_zero]

/-- Splitting one half-open interval at an interior point. -/
theorem indicator_split {a b c y : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    (if a ≤ y ∧ y < b then (1 : ℝ) else 0) +
        (if b ≤ y ∧ y < c then 1 else 0) =
      if a ≤ y ∧ y < c then 1 else 0 := by
  by_cases h1 : a ≤ y ∧ y < b
  · have h1' : a ≤ y ∧ y < c := ⟨h1.1, lt_of_lt_of_le h1.2 hbc⟩
    have h2 : ¬(b ≤ y ∧ y < c) := by
      rintro ⟨hble, _⟩
      exact not_lt_of_ge hble h1.2
    simp [h1, h1', h2]
  · by_cases h2 : b ≤ y ∧ y < c
    · have h2' : a ≤ y ∧ y < c := ⟨le_trans hab h2.1, h2.2⟩
      simp [h1, h2, h2']
    · have h3 : ¬(a ≤ y ∧ y < c) := by
        rintro ⟨hle, hlt⟩
        have hble : b ≤ y := by
          by_contra hnot
          exact h1 ⟨hle, lt_of_not_ge hnot⟩
        exact h2 ⟨hble, hlt⟩
      simp [h1, h2, h3]

/-- Degree-zero partition of unity on the half-open hull. -/
theorem splineOn_zero_sum_eq_indicator (n : Nat) {K : Fin (n + 1) → ℝ}
    (hK : Monotone K) (y : ℝ) :
    (∑ i : Fin n, splineOn K i 0 y) =
      if knotAt K 0 ≤ y ∧ y < knotAt K n then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      let K' : Fin (n + 1) → ℝ := shiftVec K
      have hK' : Monotone K' := by
        intro a b hab
        change (shiftVec K) a ≤ (shiftVec K) b
        unfold shiftVec
        exact hK (show (⟨a + 1, Nat.succ_lt_succ a.isLt⟩ : Fin (n + 2)) ≤
          ⟨b + 1, Nat.succ_lt_succ b.isLt⟩ from
          Fin.le_iff_val_le_val.mpr (Nat.succ_le_succ (Fin.le_iff_val_le_val.mp hab)))
      have hstep : (∑ i : Fin (n + 1), splineOn K i 0 y) =
          splineOn K 0 0 y + ∑ i : Fin n, splineOn K (i + 1) 0 y := by
        rw [Fin.sum_univ_succ]
        simp
      have htail : (∑ i : Fin n, splineOn K (i + 1) 0 y) =
          ∑ i : Fin n, splineOn K' i 0 y := by
        apply Finset.sum_congr rfl
        intro i _
        rw [splineOn_zero, splineOn_zero]
        have h1 : knotAt K ((i : Nat) + 1) = knotAt K' (i : Nat) := by
          simpa [K'] using (knotAt_shiftVec K (i : Nat)).symm
        have h2 : knotAt K ((i : Nat) + 1 + 1) = knotAt K' ((i : Nat) + 1) := by
          simpa [K'] using (knotAt_shiftVec K ((i : Nat) + 1)).symm
        rw [h1, h2]
      rw [hstep, htail]
      have hih : (∑ i : Fin n, splineOn K' i 0 y) =
          if knotAt K' 0 ≤ y ∧ y < knotAt K' n then 1 else 0 := ih hK'
      rw [hih]
      rw [splineOn_zero]
      have hk1 : knotAt K' 0 = knotAt K 1 := by
        simpa [K'] using (knotAt_shiftVec K 0)
      have hkn : knotAt K' n = knotAt K (n + 1) := by
        simpa [K'] using (knotAt_shiftVec K n)
      rw [hk1, hkn]
      exact indicator_split ((knotAt_mono hK) (show (0 : Nat) ≤ 1 by omega))
        ((knotAt_mono hK) (show (1 : Nat) ≤ n + 1 by omega))

/-! ## Marsden factors and the full Marsden identity -/

/-- The degree-`d` Marsden factor attached to window `i`:
`∏ h, (t - K (i + h + 1))`. -/
def marsdenPsi {n : Nat} [NeZero n] (K : Fin n → ℝ) (d i : Nat) (t : ℝ) : ℝ :=
  ∏ h : Fin d, (t - knotAt K (i + h + 1))

/-- Splitting the top Marsden factor off the product. -/
theorem marsdenPsi_succ {n : Nat} [NeZero n] (K : Fin n → ℝ) (d i : Nat) (t : ℝ) :
    marsdenPsi K (d + 1) i t = marsdenPsi K d i t * (t - knotAt K (i + d + 1)) := by
  unfold marsdenPsi
  rw [Fin.prod_univ_castSucc]
  simp [Fin.castSucc]

/-- The shifted window's Marsden factor shares its middle with the unshifted
window: `ψ(i-1, d+1) = (t - K i) * ψ(i, d)`. -/
theorem marsdenPsi_succ_pred {n : Nat} [NeZero n] (K : Fin n → ℝ) {d i : Nat}
    (hi : 0 < i) (t : ℝ) :
    marsdenPsi K (d + 1) (i - 1) t = (t - knotAt K i) * marsdenPsi K d i t := by
  unfold marsdenPsi
  rw [Fin.prod_univ_succ]
  have hfirst : t - knotAt K (i - 1 + ((0 : Fin (d + 1)) : Nat) + 1) = t - knotAt K i := by
    congr 1
    congr 1
    simp
    exact Nat.sub_add_cancel hi
  rw [hfirst]
  congr 1
  apply Finset.prod_congr rfl
  intro h _
  congr 1
  congr 1
  simp only [Fin.val_succ]
  omega

/-- Clamped access is invariant under pointwise equality of vectors. -/
theorem knotAt_congr {n : Nat} [NeZero n] {K K' : Fin n → ℝ} (h : ∀ i : Fin n, K i = K' i) :
    knotAt K = knotAt K' := by
  funext j
  unfold knotAt
  by_cases hj : j < n <;> simp [hj, h]

/-- The B-spline recursion is invariant under pointwise equality of the
clamped knot sequence. -/
theorem splineOn_congr {n : Nat} [NeZero n] {K K' : Fin n → ℝ}
    (h : knotAt K = knotAt K') (i k : Nat) (y : ℝ) :
    splineOn K i k y = splineOn K' i k y := by
  induction k generalizing i with
  | zero => simp [h]
  | succ k ih =>
      simp [wLK, wRK, h, ih i, ih (i + 1)]

/-- Degree-zero partition of unity, stated for a vector of length `n`. -/
theorem splineOn_zero_sum_eq_indicator' {n : Nat} [NeZero n] {K : Fin n → ℝ}
    (hK : Monotone K) (y : ℝ) :
    (∑ i : Fin (n - 1), splineOn K (i : Nat) 0 y) =
      if knotAt K 0 ≤ y ∧ y < knotAt K (n - 1) then 1 else 0 := by
  have hn : n - 1 + 1 = n := by
    have h1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne n))
    omega
  let K' : Fin (n - 1 + 1) → ℝ := fun i ↦ K ⟨(i : Nat), by
    have h1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne n))
    have : (i : Nat) < n := by omega
    exact this⟩
  have hK' : Monotone K' := by
    intro a b hab
    exact hK (Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp hab))
  have hsum : (∑ i : Fin (n - 1), splineOn K' (i : Nat) 0 y) =
      ∑ i : Fin (n - 1), splineOn K (i : Nat) 0 y := by
    apply Finset.sum_congr rfl
    intro i _
    rw [splineOn_zero, splineOn_zero]
    have h1 : knotAt K' (i : Nat) = knotAt K (i : Nat) := by
      unfold knotAt
      have hi : (i : Nat) < n := by
        have hlt := i.isLt
        omega
      have hi' : (i : Nat) < n - 1 + 1 := by omega
      simp [hi, hi', K']
    have h2 : knotAt K' ((i : Nat) + 1) = knotAt K ((i : Nat) + 1) := by
      unfold knotAt
      have hi : (i : Nat) + 1 < n := by
        have hlt := i.isLt
        have h1' : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne n))
        omega
      have hi' : (i : Nat) + 1 < n - 1 + 1 := by omega
      simp [hi, hi', K']
    simp only [h1, h2]
  have hpart := splineOn_zero_sum_eq_indicator (n - 1) (K := K') hK' y
  rw [← hsum]
  rw [hpart]
  have hk0 : knotAt K' 0 = knotAt K 0 := by
    unfold knotAt
    have h0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    have h0' : 0 < n - 1 + 1 := by omega
    simp [h0, h0', K']
  have hkn : knotAt K' (n - 1) = knotAt K (n - 1) := by
    unfold knotAt
    have hnm : n - 1 < n := Nat.sub_one_lt (NeZero.ne n)
    have hnm' : n - 1 < n - 1 + 1 := Nat.lt_succ_self (n - 1)
    simp [hnm, hnm', K']
  simp only [hk0, hkn]

/-- Reindexing a finite sum to a provably equal index type, keeping values. -/
theorem sum_finCast {n m : Nat} (h : n = m) (f : Fin n → ℝ) :
    (∑ i : Fin n, f i) = ∑ i : Fin m, f ⟨(i : Nat), by
      have : (i : Nat) < n := by omega
      exact this⟩ := by
  subst h
  simp

/-- The ring identity behind the interior coefficient matching. -/
lemma marsden_combine_alg (T0 T1 Tm t y M : ℝ) :
    (t - T1) * ((t - Tm) * M) * (y - T0) +
        (t - Tm) * ((t - T0) * M) * (T1 - y) =
      (t - y) * ((t - Tm) * M) * (T1 - T0) := by
  ring

/-- Interior coefficient matching: one degree step of the Marsden induction
for a window with a genuinely non-flat top gap. -/
theorem marsden_interior_coeff {n : Nat} [NeZero n] {K : Fin n → ℝ} (hK : Monotone K)
    (d j : Nat) (t y : ℝ) (hj0 : 0 < j) (hne : knotAt K (j + d + 1) ≠ knotAt K j) :
    ((t - knotAt K (j + d + 1)) * marsdenPsi K d j t * wLK K j d y +
        (t - knotAt K (j + d)) * marsdenPsi K d (j - 1) t * wRK K (j - 1) d y) *
          splineOn K j d y =
      (t - y) * marsdenPsi K d j t * splineOn K j d y := by
  have hwL : wLK K j d y = (y - knotAt K j) / (knotAt K (j + d + 1) - knotAt K j) := by
    unfold wLK
    by_cases hz : knotAt K (j + d + 1) - knotAt K j = 0
    · exfalso
      exact hne (sub_eq_zero.mp hz)
    · simp [hz]
  have hwR : wRK K (j - 1) d y =
      (knotAt K (j + d + 1) - y) / (knotAt K (j + d + 1) - knotAt K j) := by
    unfold wRK
    have hshift : j - 1 + d + 2 = j + d + 1 := by omega
    have hshift' : j - 1 + 1 = j := Nat.sub_add_cancel hj0
    rw [hshift, hshift']
    by_cases hz : knotAt K (j + d + 1) - knotAt K j = 0
    · exfalso
      exact hne (sub_eq_zero.mp hz)
    · simp [hz]
  have hcoeff : (t - knotAt K (j + d + 1)) * marsdenPsi K d j t * wLK K j d y +
        (t - knotAt K (j + d)) * marsdenPsi K d (j - 1) t * wRK K (j - 1) d y =
      (t - y) * marsdenPsi K d j t := by
    rw [hwL, hwR]
    rcases d with _ | d'
    · simp [marsdenPsi]
      field_simp [sub_ne_zero.mpr hne]
      ring
    · have hpsi1 : marsdenPsi K (d' + 1) j t =
          marsdenPsi K d' j t * (t - knotAt K (j + d' + 1)) := marsdenPsi_succ K d' j t
      have hpsi0 : marsdenPsi K (d' + 1) (j - 1) t =
          (t - knotAt K j) * marsdenPsi K d' j t := marsdenPsi_succ_pred K hj0 t
      rw [hpsi1, hpsi0]
      field_simp [sub_ne_zero.mpr hne]
      ring_nf
  rw [hcoeff]

/-- The full Marsden identity: for `y` in the interior region
`[K d, K (n-d-1))`, the monomial `(t - y)^d` expands in the degree-`d`
B-spline basis with the exact Marsden coefficients. -/
theorem marsden_identity {n : Nat} [NeZero n] {K : Fin n → ℝ} (hK : Monotone K)
    (d : Nat) (hd : d + 1 ≤ n) (t y : ℝ)
    (hy : knotAt K d ≤ y ∧ y < knotAt K (n - d - 1)) :
    (t - y) ^ d = ∑ i : Fin (n - d - 1), marsdenPsi K d (i : Nat) t * splineOn K (i : Nat) d y := by
  induction d with
  | zero =>
      have hsum : (∑ i : Fin (n - 1), splineOn K (i : Nat) 0 y) = 1 := by
        rw [splineOn_zero_sum_eq_indicator' hK]
        have hcond : knotAt K 0 ≤ y ∧ y < knotAt K (n - 1) := by
          exact ⟨hy.1, by simpa using hy.2⟩
        simp [hcond]
      simpa only [marsdenPsi, Fin.prod_univ_zero, pow_zero, one_mul] using hsum.symm
  | succ d ih =>
      rw [pow_succ]
      have hih : (t - y) ^ d =
          ∑ i : Fin (n - d - 1), marsdenPsi K d (i : Nat) t * splineOn K (i : Nat) d y := by
        apply ih
        · omega
        · constructor
          · exact le_trans ((knotAt_mono hK) (show d ≤ d + 1 by omega)) hy.1
          · exact lt_of_lt_of_le hy.2
              ((knotAt_mono hK) (show n - d - 2 ≤ n - d - 1 by omega))
      rw [hih]
      rw [sum_finCast (by omega : n - d - 1 = (n - d - 2) + 1)
        (fun i : Fin (n - d - 1) ↦ marsdenPsi K d (i : Nat) t * splineOn K (i : Nat) d y)]
      rw [sum_finCast (by omega : n - (d + 1) - 1 = n - d - 2)
        (fun i : Fin (n - (d + 1) - 1) ↦ marsdenPsi K (d + 1) (i : Nat) t * splineOn K (i : Nat) (d + 1) y)]
      have hexpand : (∑ i : Fin (n - d - 2),
          marsdenPsi K (d + 1) (i : Nat) t * splineOn K (i : Nat) (d + 1) y) =
          (∑ i : Fin (n - d - 2),
            (t - knotAt K ((i : Nat) + d + 1)) * marsdenPsi K d (i : Nat) t * wLK K (i : Nat) d y *
              splineOn K (i : Nat) d y) +
          (∑ i : Fin (n - d - 2),
            (t - knotAt K ((i : Nat) + d + 1)) * marsdenPsi K d (i : Nat) t * wRK K (i : Nat) d y *
              splineOn K ((i : Nat) + 1) d y) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [splineOn_succ]
        rw [marsdenPsi_succ]
        ring
      rw [hexpand]
      have hfirst : (∑ i : Fin (n - d - 2),
          (t - knotAt K ((i : Nat) + d + 1)) * marsdenPsi K d (i : Nat) t * wLK K (i : Nat) d y *
            splineOn K (i : Nat) d y) =
        ∑ j : Fin ((n - d - 2) + 1),
          (if hj : (j : Nat) < n - d - 2 then
            (t - knotAt K ((j : Nat) + d + 1)) * marsdenPsi K d (j : Nat) t * wLK K (j : Nat) d y
          else 0) * splineOn K (j : Nat) d y := by
        symm
        rw [Fin.sum_univ_castSucc]
        have h1 : (∑ i : Fin (n - d - 2),
            (if hj : ((i.castSucc : Fin ((n - d - 2) + 1)) : Nat) < n - d - 2 then
              (t - knotAt K (((i.castSucc : Fin ((n - d - 2) + 1)) : Nat) + d + 1)) *
                marsdenPsi K d ((i.castSucc : Fin ((n - d - 2) + 1)) : Nat) t *
                wLK K ((i.castSucc : Fin ((n - d - 2) + 1)) : Nat) d y
            else 0) * splineOn K ((i.castSucc : Fin ((n - d - 2) + 1)) : Nat) d y) =
          ∑ i : Fin (n - d - 2),
            (t - knotAt K ((i : Nat) + d + 1)) * marsdenPsi K d (i : Nat) t * wLK K (i : Nat) d y *
              splineOn K (i : Nat) d y := by
          apply Finset.sum_congr rfl
          intro i _
          simp
        have h2 : (if hj : ((Fin.last (n - d - 2) : Fin ((n - d - 2) + 1)) : Nat) < n - d - 2 then
            (t - knotAt K (((Fin.last (n - d - 2) : Fin ((n - d - 2) + 1)) : Nat) + d + 1)) *
              marsdenPsi K d ((Fin.last (n - d - 2) : Fin ((n - d - 2) + 1)) : Nat) t *
              wLK K ((Fin.last (n - d - 2) : Fin ((n - d - 2) + 1)) : Nat) d y
          else 0) * splineOn K ((Fin.last (n - d - 2) : Fin ((n - d - 2) + 1)) : Nat) d y = 0 := by
          simp
        rw [h1, h2, add_zero]
      have hsecond : (∑ i : Fin (n - d - 2),
          (t - knotAt K ((i : Nat) + d + 1)) * marsdenPsi K d (i : Nat) t * wRK K (i : Nat) d y *
            splineOn K ((i : Nat) + 1) d y) =
        ∑ j : Fin ((n - d - 2) + 1),
          (if hj : 0 < (j : Nat) then
            (t - knotAt K ((j : Nat) + d)) * marsdenPsi K d ((j : Nat) - 1) t * wRK K ((j : Nat) - 1) d y
          else 0) * splineOn K (j : Nat) d y := by
        symm
        rw [Fin.sum_univ_succ]
        have h1 : (if hj : 0 < ((0 : Fin ((n - d - 2) + 1)) : Nat) then
            (t - knotAt K (((0 : Fin ((n - d - 2) + 1)) : Nat) + d)) *
              marsdenPsi K d (((0 : Fin ((n - d - 2) + 1)) : Nat) - 1) t *
              wRK K (((0 : Fin ((n - d - 2) + 1)) : Nat) - 1) d y
          else 0) * splineOn K ((0 : Fin ((n - d - 2) + 1)) : Nat) d y = 0 := by
          simp
        have h2 : (∑ i : Fin (n - d - 2),
            (if hj : 0 < ((i.succ : Fin ((n - d - 2) + 1)) : Nat) then
              (t - knotAt K (((i.succ : Fin ((n - d - 2) + 1)) : Nat) + d)) *
                marsdenPsi K d (((i.succ : Fin ((n - d - 2) + 1)) : Nat) - 1) t *
                wRK K (((i.succ : Fin ((n - d - 2) + 1)) : Nat) - 1) d y
            else 0) * splineOn K ((i.succ : Fin ((n - d - 2) + 1)) : Nat) d y) =
          ∑ i : Fin (n - d - 2),
            (t - knotAt K ((i : Nat) + d + 1)) * marsdenPsi K d (i : Nat) t * wRK K (i : Nat) d y *
              splineOn K ((i : Nat) + 1) d y := by
          apply Finset.sum_congr rfl
          intro i _
          simp only [Fin.val_succ]
          have h1 : (i : Nat) + 1 + d = (i : Nat) + d + 1 := by omega
          have h2' : (i : Nat) + 1 - 1 = (i : Nat) := by omega
          rw [h1, h2']
          simp
        rw [h1, h2, zero_add]
      rw [hfirst, hsecond]
      rw [← Finset.sum_add_distrib]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj0 : (j : Nat) = 0
      · have hN : splineOn K 0 d y = 0 := by
          by_contra hne
          have hs := splineOn_support hK 0 d y hne
          exact not_lt_of_ge hy.1 (by simpa using hs.2)
        have hj' : j = 0 := Fin.eq_of_val_eq hj0
        rw [hj']
        simp [hN]
      · by_cases hjlast : (j : Nat) = n - d - 2
        · have hN : splineOn K (n - d - 2) d y = 0 := by
            by_contra hne
            have hs := splineOn_support hK (n - d - 2) d y hne
            exact not_lt_of_ge hs.1 hy.2
          have hj' : j = ⟨n - d - 2, by
            have : (n - d - 2) < (n - d - 2) + 1 := by omega
            exact this⟩ := Fin.eq_of_val_eq hjlast
          rw [hj']
          simp [hN]
        · have hjpos : 0 < (j : Nat) := Nat.pos_of_ne_zero hj0
          have hjtop : (j : Nat) < n - d - 2 := by
            have hle : (j : Nat) ≤ n - d - 2 := by omega
            exact lt_of_le_of_ne hle hjlast
          by_cases hflat : knotAt K ((j : Nat) + d + 1) = knotAt K (j : Nat)
          · have hN : splineOn K (j : Nat) d y = 0 :=
              splineOn_eq_zero_of_flat hK (j : Nat) d y hflat.symm
            simp [hjpos, hjtop, hN]
          · have hc := marsden_interior_coeff hK d (j : Nat) t y hjpos hflat
            simp [hjpos, hjtop]
            rw [← add_mul]
            rw [hc]
            ring

/-! ## Paper-level glue: the open two-fan knot vector -/

namespace TwoFanData

/-- The open knot vector is nondecreasing. -/
theorem openKnot_mono {m : Nat} (D : TwoFanData m) : Monotone D.openKnot := by
  intro a b hab
  have hab' : (a : Nat) ≤ (b : Nat) := Fin.le_iff_val_le_val.mp hab
  unfold openKnot
  by_cases ha : (a : Nat) < m - 1
  · simp only [dif_pos ha]
    by_cases hb : (b : Nat) < m - 1
    · simp [hb]
    · simp only [dif_neg hb]
      by_cases hz : (b : Nat) < 3 * m - 1
      · simp [hz]
        exact (D.leftAnchor_lt ⟨(b : Nat) - (m - 1), by
          have hm := D.hm
          have hb' := b.isLt
          omega⟩).le
      · simp [hz]
        exact le_trans
          (D.leftAnchor_lt ⟨0, by have hm := D.hm; omega⟩).le
          (D.lt_rightAnchor ⟨0, by have hm := D.hm; omega⟩).le
  · by_cases haz : (a : Nat) < 3 * m - 1
    · simp only [dif_neg ha, dif_pos haz]
      by_cases hb : (b : Nat) < 3 * m - 1
      · have hbA : ¬(b : Nat) < m - 1 := by omega
        simp only [dif_pos hb, hbA, dif_neg, not_false_eq_true]
        exact D.z_strict.monotone (show (⟨(a : Nat) - (m - 1), by
            have ha' := a.isLt
            have hm := D.hm
            omega⟩ : Fin (2 * m)) ≤ ⟨(b : Nat) - (m - 1), by
            have hb' := b.isLt
            have hm := D.hm
            omega⟩ from Fin.le_iff_val_le_val.mpr (Nat.sub_le_sub_right hab' (m - 1)))
      · have hbA : ¬(b : Nat) < m - 1 := by omega
        simp only [dif_neg hb, hbA, dif_neg, not_false_eq_true]
        exact (D.lt_rightAnchor ⟨(a : Nat) - (m - 1), by
          have ha' := a.isLt
          have hm := D.hm
          omega⟩).le
    · simp only [dif_neg ha, dif_neg haz]
      by_cases hb : (b : Nat) < 3 * m - 1
      · exfalso
        have hba : b < a := by
          have ha3 : 3 * m - 1 ≤ (a : Nat) := le_of_not_gt haz
          omega
        exact (not_le_of_gt hba) hab'
      · have hbA : ¬(b : Nat) < m - 1 := by omega
        simp [hb, hbA]

theorem openKnot_eq_s_iff {m : Nat} (D : TwoFanData m) (hm : 3 ≤ m) (j : Fin m)
    (q : Fin (4 * m - 2)) :
    D.openKnot q = D.s j ↔ q = D.mergeOpenIndex (D.alpha j) := by
  constructor
  · intro h
    apply Fin.ext
    by_contra hne
    by_cases hlt : (q : Nat) < m - 1 + (D.alpha j : Nat)
    · have hq := D.openKnot_lt_z_of_lt_mergeOpenIndex q (D.alpha j) hlt
      rw [h] at hq
      exact (lt_irrefl (D.s j) hq)
    · have hle : m - 1 + (D.alpha j : Nat) ≤ (q : Nat) := le_of_not_gt hlt
      have hgt : m - 1 + (D.alpha j : Nat) < (q : Nat) := lt_of_le_of_ne hle (Ne.symm hne)
      have hq := D.z_lt_openKnot_of_mergeOpenIndex_lt (D.alpha j) q hgt
      rw [h] at hq
      exact (lt_irrefl (D.s j) hq)
  · intro h
    rw [h]
    exact D.openKnot_alpha j

/-- The only open-vector position carrying the right knot `u j`. -/
theorem openKnot_eq_u_iff {m : Nat} (D : TwoFanData m) (hm : 3 ≤ m) (j : Fin m)
    (q : Fin (4 * m - 2)) :
    D.openKnot q = D.u j ↔ q = D.mergeOpenIndex (D.beta j) := by
  constructor
  · intro h
    apply Fin.ext
    by_contra hne
    by_cases hlt : (q : Nat) < m - 1 + (D.beta j : Nat)
    · have hq := D.openKnot_lt_z_of_lt_mergeOpenIndex q (D.beta j) hlt
      rw [h] at hq
      exact (lt_irrefl (D.u j) hq)
    · have hle : m - 1 + (D.beta j : Nat) ≤ (q : Nat) := le_of_not_gt hlt
      have hgt : m - 1 + (D.beta j : Nat) < (q : Nat) := lt_of_le_of_ne hle (Ne.symm hne)
      have hq := D.z_lt_openKnot_of_mergeOpenIndex_lt (D.beta j) q hgt
      rw [h] at hq
      exact (lt_irrefl (D.u j) hq)
  · intro h
    rw [h]
    exact D.openKnot_beta j

theorem openKnot_u_neighbor {m : Nat} (D : TwoFanData m) (hm : 3 ≤ m) (j : Fin m) :
    D.openKnot (D.mergeOpenIndex (D.beta j)) <
      D.openKnot ⟨m - 1 + (D.beta j : Nat) + 1, by
        have hb := (D.beta j).isLt
        have hm' := D.hm
        omega⟩ := by
  unfold TwoFanData.mergeOpenIndex
  simp only [TwoFanData.openKnot]
  have hA : ¬(m - 1 + (D.beta j : Nat) < m - 1) := by
    have hb := (D.beta j).isLt
    omega
  have hA2 : ¬(m - 1 + (D.beta j : Nat) + 1 < m - 1) := by
    have hb := (D.beta j).isLt
    omega
  simp only [hA, hA2, dif_neg, not_false_eq_true]
  by_cases hz : m - 1 + (D.beta j : Nat) < 3 * m - 1
  · by_cases hz' : m - 1 + (D.beta j : Nat) + 1 < 3 * m - 1
    · simp only [hz, hz', dif_pos, not_false_eq_true]
      have h1 : m - 1 + (D.beta j : Nat) - (m - 1) = (D.beta j : Nat) := by omega
      have h2 : m - 1 + (D.beta j : Nat) + 1 - (m - 1) = (D.beta j : Nat) + 1 := by omega
      have hlt : (m - 1 + (D.beta j : Nat) - (m - 1)) <
          (m - 1 + (D.beta j : Nat) + 1 - (m - 1)) := by
        rw [h1, h2]
        omega
      have hltFin : (⟨m - 1 + (D.beta j : Nat) - (m - 1), by
          have hb := (D.beta j).isLt
          have hm' := D.hm
          omega⟩ : Fin (2 * m)) < ⟨m - 1 + (D.beta j : Nat) + 1 - (m - 1), by
          have hb := (D.beta j).isLt
          have hm' := D.hm
          omega⟩ := Fin.lt_iff_val_lt_val.mpr hlt
      exact D.z_strict hltFin
    · simp only [hz, hz', dif_pos, dif_neg, not_false_eq_true]
      have hsub : m - 1 + (D.beta j : Nat) - (m - 1) = (D.beta j : Nat) := by omega
      have hβ : (⟨m - 1 + (D.beta j : Nat) - (m - 1), by
        have hb := (D.beta j).isLt
        have hm' := D.hm
        omega⟩ : Fin (2 * m)) = D.beta j := Fin.ext hsub
      rw [hβ]
      exact D.lt_rightAnchor (D.beta j)
  · exfalso
    have hb := (D.beta j).isLt
    have hm' := D.hm
    omega

end TwoFanData
/-- The interior evaluation region for the paper Marsden identity. -/
theorem paper_marsden_region {m : Nat} (D : TwoFanData m) (hm : 3 ≤ m) {y : ℝ}
    (hy : D.leftAnchor < y ∧ y < D.rightAnchor) :
    D.openKnot ⟨m - 2, by have hm' := D.hm; omega⟩ ≤ y ∧
      y < D.openKnot ⟨4 * m - 2 - (m - 2) - 1, by have hm' := D.hm; omega⟩ := by
  constructor
  · have hA : m - 2 < m - 1 := by omega
    simpa [TwoFanData.openKnot, hA] using hy.1.le
  · have hA' : ¬(4 * m - 2 - (m - 2) - 1 < m - 1) := by
      have hm' := D.hm
      omega
    have hZ' : ¬(4 * m - 2 - (m - 2) - 1 < 3 * m - 1) := by
      have hm' := D.hm
      omega
    simpa [TwoFanData.openKnot, hA', hZ'] using hy.2

/-- The normalized paper B-spline: degree `m-2`, Cox--de Boor normalized. -/
noncomputable def paperBSpline {m : Nat} (D : TwoFanData m)
    (i : Fin (3 * m - 1)) (y : ℝ) : ℝ :=
  letI : NeZero (4 * m - 2) := ⟨by have hm := D.hm; omega⟩
  splineOn D.openKnot (i : Nat) (m - 2) y

/-- Entrywise nonnegativity of the paper B-splines. -/
theorem paperBSpline_nonneg {m : Nat} (D : TwoFanData m) (hm : 3 ≤ m)
    (i : Fin (3 * m - 1)) (y : ℝ) : 0 ≤ paperBSpline D i y := by
  unfold paperBSpline
  letI : NeZero (4 * m - 2) := ⟨by have hm' := D.hm; omega⟩
  exact splineOn_nonneg D.openKnot_mono (i : Nat) (m - 2) y

/-! ## Paper-level Marsden identities -/

/-- Order bridge: open-vector entries up to the `s j` position lie at or
below `s j`. -/
theorem openKnot_le_s_of_le {m : Nat} (D : TwoFanData m) (hm : 3 ≤ m) (j : Fin m)
    {q : Fin (4 * m - 2)} (hq : (q : Nat) ≤ m - 1 + (D.alpha j : Nat)) :
    D.openKnot q ≤ D.s j := by
  have hle := D.openKnot_mono
    (show q ≤ D.mergeOpenIndex (D.alpha j) from Fin.le_iff_val_le_val.mpr hq)
  simpa [D.openKnot_alpha] using hle

/-- Order bridge: open-vector entries from the `s j` position onward lie at
or above `s j`. -/
theorem s_le_openKnot_of_le {m : Nat} (D : TwoFanData m) (hm : 3 ≤ m) (j : Fin m)
    {q : Fin (4 * m - 2)} (hq : m - 1 + (D.alpha j : Nat) ≤ (q : Nat)) :
    D.s j ≤ D.openKnot q := by
  have hle := D.openKnot_mono
    (show D.mergeOpenIndex (D.alpha j) ≤ q from Fin.le_iff_val_le_val.mpr hq)
  simpa [D.openKnot_alpha] using hle

/-- Order bridge: open-vector entries up to the `u j` position lie at or
below `u j`. -/
theorem openKnot_le_u_of_le {m : Nat} (D : TwoFanData m) (hm : 3 ≤ m) (j : Fin m)
    {q : Fin (4 * m - 2)} (hq : (q : Nat) ≤ m - 1 + (D.beta j : Nat)) :
    D.openKnot q ≤ D.u j := by
  have hle := D.openKnot_mono
    (show q ≤ D.mergeOpenIndex (D.beta j) from Fin.le_iff_val_le_val.mpr hq)
  simpa [D.openKnot_beta] using hle

/-- Order bridge: open-vector entries from the `u j` position onward lie at
or above `u j`. -/
theorem u_le_openKnot_of_le {m : Nat} (D : TwoFanData m) (hm : 3 ≤ m) (j : Fin m)
    {q : Fin (4 * m - 2)} (hq : m - 1 + (D.beta j : Nat) ≤ (q : Nat)) :
    D.u j ≤ D.openKnot q := by
  have hle := D.openKnot_mono
    (show D.mergeOpenIndex (D.beta j) ≤ q from Fin.le_iff_val_le_val.mpr hq)
  simpa [D.openKnot_beta] using hle

/-- Left Marsden factors vanish for rows strictly above the left support but
not past the root knot. -/
theorem paper_leftFactor_eq_zero {m : Nat} (D : TwoFanData m) (hm : 3 ≤ m) (j : Fin m)
    {i : Fin (3 * m - 1)} (hi1 : (D.alpha j : Nat) < (i : Nat))
    (hi2 : (i : Nat) ≤ (D.alpha j : Nat) + (m - 2)) :
    (∏ h : Fin (m - 2), (D.s j - D.openKnot (D.slideIndex i h))) = 0 := by
  have hpos : (D.alpha j : Nat) + (m - 2) - (i : Nat) < m - 2 := by
    rw [Nat.sub_lt_iff_lt_add hi2]
    omega
  let h0 : Fin (m - 2) := ⟨(D.alpha j : Nat) + (m - 2) - (i : Nat), hpos⟩
  apply Finset.prod_eq_zero (Finset.mem_univ h0)
  have hindex : (i : Nat) + (h0 : Nat) + 1 = m - 1 + (D.alpha j : Nat) := by
    dsimp [h0]
    rw [Nat.add_sub_of_le hi2]
    have hm' := D.hm
    omega
  have hT : D.openKnot (D.slideIndex i h0) = D.s j := by
    unfold TwoFanData.slideIndex
    have heq : (⟨(i : Nat) + (h0 : Nat) + 1, by
        have hi' := i.isLt
        have hh := h0.isLt
        have hm' := D.hm
        omega⟩ : Fin (4 * m - 2)) = D.mergeOpenIndex (D.alpha j) := by
      apply Fin.ext
      simpa [TwoFanData.mergeOpenIndex] using hindex
    rw [heq]
    exact D.openKnot_alpha j
  rw [hT, sub_self]

/-- Right Marsden factors vanish for rows strictly above the right support
but not past the root knot. -/
theorem paper_rightFactor_eq_zero {m : Nat} (D : TwoFanData m) (hm : 3 ≤ m) (j : Fin m)
    {i : Fin (3 * m - 1)} (hi1 : (D.beta j : Nat) < (i : Nat))
    (hi2 : (i : Nat) ≤ (D.beta j : Nat) + (m - 2)) :
    (∏ h : Fin (m - 2), (D.openKnot (D.slideIndex i h) - D.u j)) = 0 := by
  have hpos : (D.beta j : Nat) + (m - 2) - (i : Nat) < m - 2 := by
    rw [Nat.sub_lt_iff_lt_add hi2]
    omega
  let h0 : Fin (m - 2) := ⟨(D.beta j : Nat) + (m - 2) - (i : Nat), hpos⟩
  apply Finset.prod_eq_zero (Finset.mem_univ h0)
  have hindex : (i : Nat) + (h0 : Nat) + 1 = m - 1 + (D.beta j : Nat) := by
    dsimp [h0]
    rw [Nat.add_sub_of_le hi2]
    have hm' := D.hm
    omega
  have hT : D.openKnot (D.slideIndex i h0) = D.u j := by
    unfold TwoFanData.slideIndex
    have heq : (⟨(i : Nat) + (h0 : Nat) + 1, by
        have hi' := i.isLt
        have hh := h0.isLt
        have hm' := D.hm
        omega⟩ : Fin (4 * m - 2)) = D.mergeOpenIndex (D.beta j) := by
      apply Fin.ext
      simpa [TwoFanData.mergeOpenIndex] using hindex
    rw [heq]
    exact D.openKnot_beta j
  rw [hT, sub_self]

/-- The full Marsden identity in the paper indexing, scalar one. -/
theorem paper_marsden_identity {m : Nat} (D : TwoFanData m) (hm : 3 ≤ m) (t y : ℝ)
    (hy : D.leftAnchor < y ∧ y < D.rightAnchor) :
    (t - y) ^ (m - 2) =
      ∑ i : Fin (3 * m - 1),
        (∏ h : Fin (m - 2), (t - D.openKnot (D.slideIndex i h))) * paperBSpline D i y := by
  letI : NeZero (4 * m - 2) := ⟨by have hm' := D.hm; omega⟩
  have hd : m - 2 + 1 ≤ 4 * m - 2 := by have hm' := D.hm; omega
  have hreg' := paper_marsden_region D hm hy
  have hreg : knotAt D.openKnot (m - 2) ≤ y ∧ y < knotAt D.openKnot (4 * m - 2 - (m - 2) - 1) := by
    constructor
    · have hlt : m - 2 < 4 * m - 2 := by have hm' := D.hm; omega
      simpa [knotAt, hlt, hreg'.1]
    · have hlt : 4 * m - 2 - (m - 2) - 1 < 4 * m - 2 := by
        have hm' := D.hm
        omega
      simpa [knotAt, hlt, hreg'.2]
  have hmid := marsden_identity D.openKnot_mono (m - 2) hd t y hreg
  have hmid' : (t - y) ^ (m - 2) =
      ∑ i : Fin (3 * m - 1),
        (∏ h : Fin (m - 2), (t - knotAt D.openKnot ((i : Nat) + (h : Nat) + 1))) *
          paperBSpline D i y := by
    have hcast := sum_finCast (by omega : 4 * m - 2 - (m - 2) - 1 = 3 * m - 1)
      (fun i : Fin (4 * m - 2 - (m - 2) - 1) ↦ marsdenPsi D.openKnot (m - 2) (i : Nat) t *
        splineOn D.openKnot (i : Nat) (m - 2) y)
    rw [hmid, hcast]
    apply Finset.sum_congr rfl
    intro i _
    simp [paperBSpline, marsdenPsi]
  apply hmid'.trans
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg₂ (fun a b ↦ a * b)
  · apply Finset.prod_congr rfl
    intro h _
    have hlt : (i : Nat) + (h : Nat) + 1 < 4 * m - 2 := by
      have hi := i.isLt
      have hh := h.isLt
      have hm' := D.hm
      omega
    simp [knotAt, hlt, TwoFanData.slideIndex]
  · rfl

/-- One-sided truncated-power reproduction for a left knot, with the exact
left-support truncation of the paper coefficient matrix. -/
theorem paper_marsden_left {m : Nat} (D : TwoFanData m) (hm : 3 ≤ m) (j : Fin m) (y : ℝ)
    (hy : D.leftAnchor < y ∧ y < D.rightAnchor) :
    truncPow (m - 2) (D.s j - y) =
      ∑ i : Fin (3 * m - 1),
        (if (i : Nat) ≤ (D.alpha j : Nat) then
          ∏ h : Fin (m - 2), (D.s j - D.openKnot (D.slideIndex i h))
        else 0) * paperBSpline D i y := by
  letI : NeZero (4 * m - 2) := ⟨by have hm' := D.hm; omega⟩
  have hfull := paper_marsden_identity D hm (D.s j) y hy
  by_cases hy_s : y < D.s j
  · have htrunc : truncPow (m - 2) (D.s j - y) = (D.s j - y) ^ (m - 2) := by
      rw [truncPow_of_pos]
      exact sub_pos.mpr hy_s
    rw [htrunc, hfull]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : (i : Nat) ≤ (D.alpha j : Nat)
    · simp [hi]
    · have hi' : (D.alpha j : Nat) < (i : Nat) := Nat.lt_of_not_ge hi
      by_cases hi2 : (i : Nat) ≤ (D.alpha j : Nat) + (m - 2)
      · have hzero := paper_leftFactor_eq_zero D hm j hi' hi2
        simp [hi, hzero]
      · have hN : paperBSpline D i y = 0 := by
          unfold paperBSpline
          by_contra hne
          have hs := splineOn_support D.openKnot_mono (i : Nat) (m - 2) y hne
          have hTi : D.s j ≤ knotAt D.openKnot (i : Nat) := by
            have hlt : (i : Nat) < 4 * m - 2 := by
              have hi'' := i.isLt
              have hm' := D.hm
              omega
            have hsle := s_le_openKnot_of_le D hm j (q := ⟨(i : Nat), hlt⟩)
              (by omega : m - 1 + (D.alpha j : Nat) ≤ (i : Nat))
            simpa [knotAt, hlt, hsle]
          exact not_lt_of_ge (le_trans hTi hs.1) hy_s
        simp [hi, hN]
  · have htrunc : truncPow (m - 2) (D.s j - y) = 0 := by
      rw [truncPow_of_nonpos]
      exact sub_nonpos.mpr (le_of_not_gt hy_s)
    rw [htrunc]
    symm
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : (i : Nat) ≤ (D.alpha j : Nat)
    · have hN : paperBSpline D i y = 0 := by
        unfold paperBSpline
        by_contra hne
        have hs := splineOn_support D.openKnot_mono (i : Nat) (m - 2) y hne
        have hT : knotAt D.openKnot ((i : Nat) + (m - 2) + 1) ≤ D.s j := by
          have hlt : (i : Nat) + (m - 2) + 1 < 4 * m - 2 := by
            have hi' := i.isLt
            have hm' := D.hm
            omega
          have hle := openKnot_le_s_of_le D hm j (q := ⟨(i : Nat) + (m - 2) + 1, hlt⟩)
            (by omega : (i : Nat) + (m - 2) + 1 ≤ m - 1 + (D.alpha j : Nat))
          simpa [knotAt, hlt, hle]
        exact (not_lt_of_ge (le_of_not_gt hy_s)) (lt_of_lt_of_le hs.2 hT)
      simp [hi, hN]
    · simp [hi]

/-- One-sided truncated-power reproduction for a right knot, with the exact
right-support truncation of the paper coefficient matrix. -/
theorem paper_marsden_right {m : Nat} (D : TwoFanData m) (hm : 3 ≤ m) (j : Fin m) (y : ℝ)
    (hy : D.leftAnchor < y ∧ y < D.rightAnchor) :
    truncPow (m - 2) (y - D.u j) =
      ∑ i : Fin (3 * m - 1),
        (if m - 1 + (D.beta j : Nat) ≤ (i : Nat) then
          ∏ h : Fin (m - 2), (D.openKnot (D.slideIndex i h) - D.u j)
        else 0) * paperBSpline D i y := by
  letI : NeZero (4 * m - 2) := ⟨by have hm' := D.hm; omega⟩
  have hfull := paper_marsden_identity D hm (D.u j) y hy
  have hflipped : (y - D.u j) ^ (m - 2) =
      ∑ i : Fin (3 * m - 1),
        (∏ h : Fin (m - 2), (D.openKnot (D.slideIndex i h) - D.u j)) * paperBSpline D i y := by
    calc
      (y - D.u j) ^ (m - 2)
          = (-1 : ℝ) ^ (m - 2) * (D.u j - y) ^ (m - 2) := by
            rw [show y - D.u j = -(D.u j - y) by ring]
            rw [neg_pow]
      _ = (-1 : ℝ) ^ (m - 2) * (∑ i : Fin (3 * m - 1),
            (∏ h : Fin (m - 2), (D.u j - D.openKnot (D.slideIndex i h))) *
              paperBSpline D i y) := by
            rw [hfull]
      _ = ∑ i : Fin (3 * m - 1),
          (∏ h : Fin (m - 2), (D.openKnot (D.slideIndex i h) - D.u j)) * paperBSpline D i y := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        have hneg : (∏ h : Fin (m - 2), (D.openKnot (D.slideIndex i h) - D.u j)) =
            (-1 : ℝ) ^ (m - 2) * ∏ h : Fin (m - 2), (D.u j - D.openKnot (D.slideIndex i h)) := by
          rw [show (∏ h : Fin (m - 2), (D.openKnot (D.slideIndex i h) - D.u j)) =
              ∏ h : Fin (m - 2), -(D.u j - D.openKnot (D.slideIndex i h)) by
            apply Finset.prod_congr rfl
            intro h _
            ring]
          rw [Finset.prod_neg]
          simp
        rw [hneg]
        ring
  by_cases hu_y : D.u j < y
  · have htrunc : truncPow (m - 2) (y - D.u j) = (y - D.u j) ^ (m - 2) := by
      rw [truncPow_of_pos]
      exact sub_pos.mpr hu_y
    rw [htrunc, hflipped]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : m - 1 + (D.beta j : Nat) ≤ (i : Nat)
    · simp [hi]
    · by_cases hi2 : (D.beta j : Nat) < (i : Nat)
      · have hi2' : (i : Nat) ≤ (D.beta j : Nat) + (m - 2) := by omega
        have hzero := paper_rightFactor_eq_zero D hm j hi2 hi2'
        simp [hi, hzero]
      · have hN : paperBSpline D i y = 0 := by
          unfold paperBSpline
          by_contra hne
          have hs := splineOn_support D.openKnot_mono (i : Nat) (m - 2) y hne
          have hT : knotAt D.openKnot ((i : Nat) + (m - 2) + 1) ≤ D.u j := by
            have hlt : (i : Nat) + (m - 2) + 1 < 4 * m - 2 := by
              have hi' := i.isLt
              have hm' := D.hm
              omega
            have hle := openKnot_le_u_of_le D hm j (q := ⟨(i : Nat) + (m - 2) + 1, hlt⟩)
              (by omega : (i : Nat) + (m - 2) + 1 ≤ m - 1 + (D.beta j : Nat))
            simpa [knotAt, hlt, hle]
          exact (not_lt_of_ge (le_of_lt hu_y)) (lt_of_lt_of_le hs.2 hT)
        simp [hi, hN]
  · have htrunc : truncPow (m - 2) (y - D.u j) = 0 := by
      rw [truncPow_of_nonpos]
      exact sub_nonpos.mpr (le_of_not_gt hu_y)
    rw [htrunc]
    symm
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : m - 1 + (D.beta j : Nat) ≤ (i : Nat)
    · have hN : paperBSpline D i y = 0 := by
        unfold paperBSpline
        by_contra hne
        have hs := splineOn_support D.openKnot_mono (i : Nat) (m - 2) y hne
        by_cases hy_lt : y < D.u j
        · have hTi : D.u j ≤ knotAt D.openKnot (i : Nat) := by
            have hlt : (i : Nat) < 4 * m - 2 := by
              have hi' := i.isLt
              have hm' := D.hm
              omega
            have hle := u_le_openKnot_of_le D hm j (q := ⟨(i : Nat), hlt⟩) hi
            simpa [knotAt, hlt, hle]
          exact not_lt_of_ge (le_trans hTi hs.1) hy_lt
        · have hy_eq : y = D.u j := by
            have hle : y ≤ D.u j := le_of_not_gt hu_y
            exact le_antisymm hle (le_of_not_gt hy_lt)
          have hN' : splineOn D.openKnot (i : Nat) (m - 2) (D.u j) = 0 := by
            by_cases hi_eq : (i : Nat) = m - 1 + (D.beta j : Nat)
            · have hi' : i = ⟨m - 1 + (D.beta j : Nat), by
                have hi'' := i.isLt
                have hb := (D.beta j).isLt
                have hm' := D.hm
                omega⟩ := by
                apply Fin.ext
                exact hi_eq
              rw [hi']
              have hconv : D.u j = knotAt D.openKnot (m - 1 + (D.beta j : Nat)) := by
                have hlt1 : m - 1 + (D.beta j : Nat) < 4 * m - 2 := by
                  have hb := (D.beta j).isLt
                  have hm' := D.hm
                  omega
                have hA : ¬(m - 1 + (D.beta j : Nat) < m - 1) := by
                  have hb := (D.beta j).isLt
                  omega
                have hz : m - 1 + (D.beta j : Nat) < 3 * m - 1 := by
                  have hb := (D.beta j).isLt
                  have hm' := D.hm
                  omega
                have hsub : m - 1 + (D.beta j : Nat) - (m - 1) = (D.beta j : Nat) := by omega
                symm
                rw [knotAt_lt D.openKnot _ hlt1]
                simp [TwoFanData.openKnot, hA, hz, hsub]
                rfl
              rw [hconv]
              apply splineOn_leftEndpoint_zero D.openKnot_mono
              · omega
              · have hlt1 : m - 1 + (D.beta j : Nat) < 4 * m - 2 := by
                  have hb := (D.beta j).isLt
                  have hm' := D.hm
                  omega
                have hlt2 : m - 1 + (D.beta j : Nat) + 1 < 4 * m - 2 := by
                  have hb := (D.beta j).isLt
                  have hm' := D.hm
                  omega
                rw [knotAt_lt D.openKnot _ hlt1, knotAt_lt D.openKnot _ hlt2]
                simpa [TwoFanData.mergeOpenIndex] using (D.openKnot_u_neighbor hm j)
            · by_contra hne'
              have hsupport := splineOn_support D.openKnot_mono (i : Nat) (m - 2) (D.u j) hne'
              have hTi : D.u j < knotAt D.openKnot (i : Nat) := by
                have hlt : (i : Nat) < 4 * m - 2 := by
                  have hi' := i.isLt
                  have hm' := D.hm
                  omega
                have hltm : m - 1 + (D.beta j : Nat) + 1 < 4 * m - 2 := by
                  have hb := (D.beta j).isLt
                  have hm' := D.hm
                  omega
                have hmono : knotAt D.openKnot (m - 1 + (D.beta j : Nat) + 1) ≤
                    knotAt D.openKnot (i : Nat) := by
                  rw [knotAt_lt D.openKnot _ hltm, knotAt_lt D.openKnot _ hlt]
                  exact D.openKnot_mono (Fin.le_iff_val_le_val.mpr
                    (by omega : m - 1 + (D.beta j : Nat) + 1 ≤ (i : Nat)))
                have hTu : D.u j < knotAt D.openKnot (m - 1 + (D.beta j : Nat) + 1) := by
                  rw [knotAt_lt D.openKnot _ hltm]
                  simpa [D.openKnot_beta] using (D.openKnot_u_neighbor hm j)
                exact lt_of_lt_of_le hTu hmono
              exact not_lt_of_ge hsupport.1 hTi
          exact hne (by rw [hy_eq]; exact hN')
      simp [hi, hN]
    · simp [hi]

/-! ## Collocation interface -/

/-- Every sample lies strictly between the exterior anchors. -/
def SamplesInsideAnchors {m : Nat} (D : TwoFanData m)
    (x : Fin (2 * m) → ℝ) : Prop :=
  ∀ i, D.leftAnchor < x i ∧ x i < D.rightAnchor

/-- The paper B-spline collocation matrix `B_T(X)`. -/
def bsplineCollocation {m : Nat} (D : TwoFanData m)
    (x : Fin (2 * m) → ℝ) :
    Matrix (Fin (2 * m)) (Fin (3 * m - 1)) ℝ :=
  fun row i => paperBSpline D i (x row)

end

end ColomboGeneralK2.Odd
