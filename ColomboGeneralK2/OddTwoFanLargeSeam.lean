import ColomboGeneralK2.OddTwoFanCondensationSupport
import ColomboGeneralK2.OddTwoFanSmallSeam
import ColomboGeneralK2.OddOneFanMinors

/-!
# Large two-fan seam condensation

This file supplies the one-sided boundary bookkeeping missing from the
strictly two-sided condensation-support API and then proves positivity of
every supported large mixed seam by strong induction on its order.
-/

open scoped BigOperators
open Finset Matrix

namespace ColomboGeneralK2.Odd

noncomputable section

namespace FanMinorWindow

variable {m : Nat} {D : TwoFanData m}

/-- The left-only window carried by the left part of a fan window. -/
def leftOneFan (W : FanMinorWindow D) : OneFanWindow D where
  side := .left
  c := m - W.ell
  q := W.ell
  rho := W.rho
  cq_le := by
    have := W.ell_le
    omega
  rows_le := by
    have := W.rows_le
    omega

/-- The right-only window carried by the right part of a fan window. -/
def rightOneFan (W : FanMinorWindow D) : OneFanWindow D where
  side := .right
  c := W.c
  q := W.b
  rho := W.rho
  cq_le := W.cb_le
  rows_le := by
    have := W.rows_le
    omega

@[simp] theorem leftOneFan_side (W : FanMinorWindow D) :
    W.leftOneFan.side = .left := rfl

@[simp] theorem rightOneFan_side (W : FanMinorWindow D) :
    W.rightOneFan.side = .right := rfl

@[simp] theorem leftOneFan_q (W : FanMinorWindow D) :
    W.leftOneFan.q = W.ell := rfl

@[simp] theorem rightOneFan_q (W : FanMinorWindow D) :
    W.rightOneFan.q = W.b := rfl

/-- If the right block is empty, the fan minor is literally its left-only
one-fan minor. -/
theorem fanMinor_eq_leftOneFan_minor_of_b_eq_zero (W : FanMinorWindow D)
    (hb0 : W.b = 0) : W.fanMinor = W.leftOneFan.minor := by
  obtain ⟨ell, c, b, rho, hell, hcb, hrows⟩ := W
  dsimp only at hb0
  subst b
  let W0 : FanMinorWindow D :=
    { ell := ell, c := c, b := 0, rho := rho, ell_le := hell,
      cb_le := hcb, rows_le := hrows }
  change W0.fanMinor = W0.leftOneFan.minor
  unfold fanMinor OneFanWindow.minor matrixMinor
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply]
  congr 1
  apply Fin.ext
  change (fanColValue W0 j : Nat) = _
  unfold fanColValue leftOneFan OneFanWindow.cols
  rw [dif_pos (by
    have hj := j.isLt
    change (j : Nat) < ell + 0 at hj
    simpa using hj)]
  rfl

/-- If the left suffix is empty, the fan minor is literally its right-only
one-fan minor. -/
theorem fanMinor_eq_rightOneFan_minor_of_ell_eq_zero (W : FanMinorWindow D)
    (hell0 : W.ell = 0) : W.fanMinor = W.rightOneFan.minor := by
  obtain ⟨ell, c, b, rho, hell, hcb, hrows⟩ := W
  dsimp only at hell0
  subst ell
  let W0 : FanMinorWindow D :=
    { ell := 0, c := c, b := b, rho := rho, ell_le := hell,
      cb_le := hcb, rows_le := hrows }
  change W0.fanMinor = W0.rightOneFan.minor
  unfold fanMinor OneFanWindow.minor matrixMinor
  let e : Fin b ≃ Fin (0 + b) := finCongr (by omega)
  let A := (twoFanCoefficientMatrix D).submatrix
    W0.fanRows W0.fanCols
  change A.det = _
  calc
    A.det = (A.submatrix e e).det :=
      (Matrix.det_submatrix_equiv_self e A).symm
    _ = _ := by
      congr 1

/-- Diagonal support is inherited by the top-left deletion, including the
boundary case `b=1` where the neighbour becomes left-only. -/
theorem tl_diagonalSupported_general (W : FanMinorWindow D)
    (hb : 0 < W.b)
    (hsupp : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      W.fanRows W.fanCols) :
    DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      (W.tl hb).fanRows (W.tl hb).fanCols := by
  intro t
  let u : Fin W.q := ⟨(t : Nat), by
    have ht := t.isLt
    dsimp only [q, tl] at ht ⊢
    omega⟩
  have hrow : (W.tl hb).fanRows t = W.fanRows u := by
    apply Fin.ext
    rfl
  have hcol : (W.tl hb).fanCols t = W.fanCols u := by
    apply Fin.ext
    change (fanColValue (W.tl hb) t : Nat) = (fanColValue W u : Nat)
    unfold fanColValue
    by_cases htell : (t : Nat) < W.ell
    · rw [dif_pos (by simpa [tl] using htell), dif_pos (by simpa [u] using htell)]
      simp [tl, u]
    · rw [dif_neg (by simpa [tl] using htell), dif_neg (by simpa [u] using htell)]
      simp [tl, u]
  rw [hrow, hcol]
  exact hsupp u

/-- Diagonal support is inherited by the bottom-right deletion, including
the boundary case `ell=1` where the neighbour becomes right-only. -/
theorem br_diagonalSupported_general (W : FanMinorWindow D)
    (hell : 0 < W.ell)
    (hsupp : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      W.fanRows W.fanCols) :
    DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      (W.br hell).fanRows (W.br hell).fanCols := by
  intro t
  let u : Fin W.q := ⟨(t : Nat) + 1, by
    have ht := t.isLt
    dsimp only [q, br] at ht ⊢
    omega⟩
  have hrow : (W.br hell).fanRows t = W.fanRows u := by
    apply Fin.ext
    change W.rho + 1 + (t : Nat) = W.rho + ((t : Nat) + 1)
    omega
  have hcol : (W.br hell).fanCols t = W.fanCols u := by
    apply Fin.ext
    change (fanColValue (W.br hell) t : Nat) = (fanColValue W u : Nat)
    unfold fanColValue
    by_cases htell : (t : Nat) < W.ell - 1
    · rw [dif_pos (by simpa [br] using htell), dif_pos (by
          dsimp only [u]
          omega)]
      have := W.ell_le
      simp only [br, u]
      omega
    · rw [dif_neg (by simpa [br] using htell), dif_neg (by
          dsimp only [u]
          omega)]
      dsimp only [u]
      simp only [br]
      omega
  rw [hrow, hcol]
  exact hsupp u

/-- Diagonal support is inherited by the common middle deletion even when
one or both remaining fan blocks are empty. -/
theorem mid_diagonalSupported_general (W : FanMinorWindow D)
    (hell : 0 < W.ell) (hb : 0 < W.b)
    (hsupp : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      W.fanRows W.fanCols) :
    DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      (W.mid hell hb).fanRows (W.mid hell hb).fanCols := by
  intro t
  let u : Fin W.q := ⟨(t : Nat) + 1, by
    have ht := t.isLt
    dsimp only [q, mid] at ht ⊢
    omega⟩
  have hrow : (W.mid hell hb).fanRows t = W.fanRows u := by
    apply Fin.ext
    change W.rho + 1 + (t : Nat) = W.rho + ((t : Nat) + 1)
    omega
  have hcol : (W.mid hell hb).fanCols t = W.fanCols u := by
    apply Fin.ext
    change (fanColValue (W.mid hell hb) t : Nat) = (fanColValue W u : Nat)
    unfold fanColValue
    by_cases htell : (t : Nat) < W.ell - 1
    · rw [dif_pos (by simpa [mid] using htell), dif_pos (by
          dsimp only [u]
          omega)]
      have := W.ell_le
      simp only [mid, u]
      omega
    · rw [dif_neg (by simpa [mid] using htell), dif_neg (by
          dsimp only [u]
          omega)]
      dsimp only [u]
      simp only [mid]
      omega
  rw [hrow, hcol]
  exact hsupp u

/-- The missing `ell=1` lower-endpoint case: the top-right neighbour is a
right-only window whose support starts exactly one row later. -/
theorem tr_fanMinor_eq_zero_of_rho_eq_lower_ell_eq_one
    (W : FanMinorWindow D) (hell : 0 < W.ell) (hb : 0 < W.b)
    (hell1 : W.ell = 1) (hrho : W.rho = W.lower hb) :
    (W.tr hell).fanMinor = 0 := by
  let N := W.tr hell
  have hnell : N.ell = 0 := by simp [N, tr, hell1]
  rw [N.fanMinor_eq_rightOneFan_minor_of_ell_eq_zero hnell]
  apply N.rightOneFan.minor_eq_zero_of_not_diagonalSupported
  intro hs
  have hnq : 0 < N.rightOneFan.q := by simp [N, rightOneFan, tr]; omega
  have hbound := (N.rightOneFan.right_diagonalSupported_iff rfl hnq).mp hs
  have hlast : N.rightOneFan.lastLabel hnq = W.lastRight hb := by
    apply Fin.ext
    simp [N, rightOneFan, OneFanWindow.lastLabel, tr, lastRight]
  rw [hlast] at hbound
  dsimp only [N, rightOneFan, tr] at hbound
  unfold lower q at hrho
  have hfloor := beta_succ_le (D := D) (W.lastRight hb)
  have hlastVal := W.lastRight_val hb
  change m + (D.beta (W.lastRight hb) : Nat) - W.b ≤ W.rho at hbound
  rw [hell1] at hrho
  omega

/-- The missing `b=1` upper-endpoint case: the bottom-left neighbour is a
left-only window whose support ended one row earlier. -/
theorem bl_fanMinor_eq_zero_of_rho_eq_upper_b_eq_one
    (W : FanMinorWindow D) (hell : 0 < W.ell) (hb : 0 < W.b)
    (hb1 : W.b = 1) (hrho : W.rho = W.upper hell) :
    (W.bl hb).fanMinor = 0 := by
  let N := W.bl hb
  have hnb : N.b = 0 := by simp [N, bl, hb1]
  rw [N.fanMinor_eq_leftOneFan_minor_of_b_eq_zero hnb]
  apply N.leftOneFan.minor_eq_zero_of_not_diagonalSupported
  intro hs
  have hnq : 0 < N.leftOneFan.q := by simp [N, leftOneFan, bl]; omega
  have hbound := (N.leftOneFan.left_diagonalSupported_iff rfl hnq).mp hs
  have hfirst : N.leftOneFan.firstLabel hnq = W.firstLeft hell := by
    apply Fin.ext
    simp [N, leftOneFan, OneFanWindow.firstLabel, bl, firstLeft]
  rw [hfirst] at hbound
  dsimp only [N, leftOneFan, bl] at hbound
  unfold upper at hrho
  omega

/-- At the lower endpoint the top-right cross neighbour is zero, with no
restriction on the two block sizes beyond nonemptiness. -/
theorem tr_fanMinor_eq_zero_of_rho_eq_lower_general
    (W : FanMinorWindow D) (hell : 0 < W.ell) (hb : 0 < W.b)
    (hrho : W.rho = W.lower hb) : (W.tr hell).fanMinor = 0 := by
  by_cases hell2 : 1 < W.ell
  · exact W.tr_fanMinor_eq_zero_of_rho_eq_lower hell2 hb hrho
  · apply W.tr_fanMinor_eq_zero_of_rho_eq_lower_ell_eq_one hell hb
      (by omega) hrho

/-- At the upper endpoint the bottom-left cross neighbour is zero, with no
restriction on the two block sizes beyond nonemptiness. -/
theorem bl_fanMinor_eq_zero_of_rho_eq_upper_general
    (W : FanMinorWindow D) (hell : 0 < W.ell) (hb : 0 < W.b)
    (hrho : W.rho = W.upper hell) : (W.bl hb).fanMinor = 0 := by
  by_cases hb2 : 1 < W.b
  · exact W.bl_fanMinor_eq_zero_of_rho_eq_upper hell hb2 hrho
  · apply W.bl_fanMinor_eq_zero_of_rho_eq_upper_b_eq_one hell hb
      (by omega) hrho

end FanMinorWindow

namespace OneFanWindow

variable {m : Nat} {D : TwoFanData m}

/-- The supported full left one-fan minor is positive.  This is the missing
order-`m` endpoint of the sliding-root argument: expansion in the first
column leaves the already-small full cofactor window. -/
theorem leftFull_minor_pos (D : TwoFanData m) :
    0 < (leftFullWindow D).minor := by
  have hm := D.hm
  let W := leftFullWindow D
  let C := leftFullCofactorWindow D
  let n := m - 1
  have hmn : n + 1 = m := by
    dsimp only [n]
    omega
  let e : Fin (n + 1) ≃ Fin m := finCongr hmn
  let A := (twoFanCoefficientMatrix D).submatrix W.rows W.cols
  let B := A.submatrix e e
  have hcofactor : B.submatrix Fin.succ Fin.succ =
      (twoFanCoefficientMatrix D).submatrix C.rows C.cols := by
    ext i j
    change twoFanCoefficientMatrix D (W.rows (e (Fin.succ i)))
        (W.cols (e (Fin.succ j))) =
      twoFanCoefficientMatrix D (C.rows i) (C.cols j)
    have hr : W.rows (e (Fin.succ i)) = C.rows i := by
      apply Fin.ext
      rw [W.rows_val, C.rows_val]
      change W.rho + (e (Fin.succ i) : Nat) = C.rho + (i : Nat)
      simp only [W, C, leftFullWindow, leftFullCofactorWindow]
      simp [e]
      omega
    have hc : W.cols (e (Fin.succ j)) = C.cols j := by
      rw [W.cols_left_eq (by rfl), C.cols_left_eq (by rfl)]
      apply congrArg (twoFanColumnEquiv m)
      apply congrArg Sum.inl
      apply Fin.ext
      change W.c + (e (Fin.succ j) : Nat) = C.c + (j : Nat)
      simp only [W, C, leftFullWindow, leftFullCofactorWindow]
      simp [e]
      omega
    rw [hr, hc]
  have hpivot : 0 < B 0 0 := by
    change 0 < twoFanCoefficientMatrix D
      ((leftFullWindow D).rows (e 0)) ((leftFullWindow D).cols (e 0))
    rw [(leftFullWindow D).cols_left_eq (by rfl)]
    simp only [leftFullWindow, Nat.zero_add]
    apply twoFanCoefficientMatrix_left_pos
    have ha0 : (D.alpha ⟨0, by omega⟩ : Nat) = 0 := by
      simpa using congrArg Fin.val D.alpha_zero
    have he0 : (e 0 : Nat) = 0 := by simp [e]
    simp only [he0, ha0]
    rfl
  have hoff : ∀ i : Fin (n + 1), i ≠ 0 → B i 0 = 0 := by
    intro i hi
    change twoFanCoefficientMatrix D
      ((leftFullWindow D).rows (e i)) ((leftFullWindow D).cols (e 0)) = 0
    rw [(leftFullWindow D).cols_left_eq (by rfl)]
    simp only [leftFullWindow, Nat.zero_add]
    apply twoFanCoefficientMatrix_left_zero
    have hi0 : 0 < (i : Nat) := by
      exact Fin.pos_iff_ne_zero.mpr hi
    have ha0 : (D.alpha ⟨0, by omega⟩ : Nat) = 0 := by
      simpa using congrArg Fin.val D.alpha_zero
    have he0 : (e 0 : Nat) = 0 := by simp [e]
    have hei : (e i : Nat) = (i : Nat) := by simp [e]
    simp only [he0, ha0]
    have hrow := (leftFullWindow D).rows_val (e i)
    change (((leftFullWindow D).rows (e i) : Fin (3 * m - 1)) : Nat) =
      0 + (e i : Nat) at hrow
    change 0 < (((leftFullWindow D).rows (e i) : Fin (3 * m - 1)) : Nat)
    rw [hrow, hei]
    simpa using hi0
  have hcofactor_pos : 0 < C.minor := by
    apply C.left_minor_pos_of_small (by rfl)
    · change 0 < m - 1
      omega
    · rfl
    · exact leftFullCofactor_diagonalSupported D
  have hdet : W.minor = B.det := by
    unfold minor matrixMinor
    change A.det = B.det
    exact (Matrix.det_submatrix_equiv_self e A).symm
  rw [hdet, Matrix.det_succ_column_zero]
  rw [Finset.sum_eq_single 0]
  · simp only [Fin.val_zero, pow_zero, one_mul]
    change 0 < B 0 0 * (B.submatrix Fin.succ Fin.succ).det
    rw [hcofactor]
    exact mul_pos hpivot hcofactor_pos
  · intro i _ hi
    simp [hoff i hi]
  · simp

/-- The supported full right one-fan minor is positive.  Expansion in its
last column has a single nonzero term, at the last row; the corner sign is
even and the remaining leading cofactor is a small right window. -/
theorem rightFull_minor_pos (D : TwoFanData m) :
    0 < (rightFullWindow D).minor := by
  have hm := D.hm
  let W := rightFullWindow D
  let C := rightFullCofactorWindow D
  let n := m - 1
  have hmn : n + 1 = m := by
    dsimp only [n]
    omega
  let e : Fin (n + 1) ≃ Fin m := finCongr hmn
  let A := (twoFanCoefficientMatrix D).submatrix W.rows W.cols
  let B := A.submatrix e e
  have hcofactor : B.submatrix Fin.castSucc Fin.castSucc =
      (twoFanCoefficientMatrix D).submatrix C.rows C.cols := by
    ext i j
    change twoFanCoefficientMatrix D (W.rows (e (Fin.castSucc i)))
        (W.cols (e (Fin.castSucc j))) =
      twoFanCoefficientMatrix D (C.rows i) (C.cols j)
    have hr : W.rows (e (Fin.castSucc i)) = C.rows i := by
      apply Fin.ext
      rw [W.rows_val, C.rows_val]
      change W.rho + (e (Fin.castSucc i) : Nat) = C.rho + (i : Nat)
      simp only [W, C, rightFullWindow, rightFullCofactorWindow]
      simp [e]
    have hc : W.cols (e (Fin.castSucc j)) = C.cols j := by
      rw [W.cols_right_eq (by rfl), C.cols_right_eq (by rfl)]
      apply congrArg (twoFanColumnEquiv m)
      apply congrArg Sum.inr
      apply Fin.ext
      change W.c + (e (Fin.castSucc j) : Nat) = C.c + (j : Nat)
      simp only [W, C, rightFullWindow, rightFullCofactorWindow]
      simp [e]
    rw [hr, hc]
  have hpivot : 0 < B (Fin.last n) (Fin.last n) := by
    change 0 < twoFanCoefficientMatrix D
      ((rightFullWindow D).rows (e (Fin.last n)))
      ((rightFullWindow D).cols (e (Fin.last n)))
    rw [(rightFullWindow D).cols_right_eq (by rfl)]
    simp only [rightFullWindow, Nat.zero_add]
    apply twoFanCoefficientMatrix_right_pos
    have hbetaLast : (D.beta ⟨m - 1, by omega⟩ : Nat) = 2 * m - 1 := by
      simpa using congrArg Fin.val D.beta_last
    have helast : (e (Fin.last n) : Nat) = m - 1 := by
      simp [e, n]
    have hlabel : (⟨(e (Fin.last n) : Nat), by
        exact (e (Fin.last n)).isLt⟩ : Fin m) = ⟨m - 1, by omega⟩ := by
      apply Fin.ext
      exact helast
    have hrow := (rightFullWindow D).rows_val (e (Fin.last n))
    change (((rightFullWindow D).rows (e (Fin.last n)) :
      Fin (3 * m - 1)) : Nat) = 2 * m - 1 + (e (Fin.last n) : Nat) at hrow
    rw [hlabel, hbetaLast]
    change m - 1 + (2 * m - 1) ≤
      (((rightFullWindow D).rows (e (Fin.last n)) : Fin (3 * m - 1)) : Nat)
    rw [hrow, helast]
    omega
  have hoff : ∀ i : Fin (n + 1), i ≠ Fin.last n →
      B i (Fin.last n) = 0 := by
    intro i hi
    change twoFanCoefficientMatrix D
      ((rightFullWindow D).rows (e i))
      ((rightFullWindow D).cols (e (Fin.last n))) = 0
    rw [(rightFullWindow D).cols_right_eq (by rfl)]
    simp only [rightFullWindow, Nat.zero_add]
    apply twoFanCoefficientMatrix_right_zero
    have hbetaLast : (D.beta ⟨m - 1, by omega⟩ : Nat) = 2 * m - 1 := by
      simpa using congrArg Fin.val D.beta_last
    have helast : (e (Fin.last n) : Nat) = m - 1 := by
      simp [e, n]
    have hlabel : (⟨(e (Fin.last n) : Nat), by
        exact (e (Fin.last n)).isLt⟩ : Fin m) = ⟨m - 1, by omega⟩ := by
      apply Fin.ext
      exact helast
    have hiLast : (i : Nat) < n := by
      have hile := Fin.le_last i
      have hine : (i : Nat) ≠ n := by
        intro hieq
        apply hi
        apply Fin.ext
        simpa using hieq
      change (i : Nat) ≤ n at hile
      omega
    have hei : (e i : Nat) = (i : Nat) := by simp [e]
    have hrow := (rightFullWindow D).rows_val (e i)
    change (((rightFullWindow D).rows (e i) : Fin (3 * m - 1)) : Nat) =
      2 * m - 1 + (e i : Nat) at hrow
    rw [hlabel, hbetaLast]
    change (((rightFullWindow D).rows (e i) : Fin (3 * m - 1)) : Nat) <
      m - 1 + (2 * m - 1)
    rw [hrow, hei]
    dsimp only [n] at hiLast
    omega
  have hcofactor_pos : 0 < C.minor := by
    apply C.right_minor_pos_of_small (by rfl)
    · change 0 < m - 1
      omega
    · rfl
    · exact rightFullCofactor_diagonalSupported D
  have hsign : (-1 : ℝ) ^ ((Fin.last n : Nat) + (Fin.last n : Nat)) = 1 := by
    change (-1 : ℝ) ^ (n + n) = 1
    rw [show n + n = 2 * n by omega, pow_mul]
    norm_num
  have hdet : W.minor = B.det := by
    unfold minor matrixMinor
    change A.det = B.det
    exact (Matrix.det_submatrix_equiv_self e A).symm
  rw [hdet, Matrix.det_succ_column B (Fin.last n)]
  rw [Finset.sum_eq_single (Fin.last n)]
  · rw [hsign]
    simp only [one_mul]
    simp only [Fin.succAbove_last]
    change 0 < B (Fin.last n) (Fin.last n) *
      (B.submatrix Fin.castSucc Fin.castSucc).det
    rw [hcofactor]
    exact mul_pos hpivot hcofactor_pos
  · intro i _ hi
    simp [hoff i hi]
  · simp

/-- Every diagonally supported one-fan solid minor is positive, including
the full order endpoint omitted by the small sliding-root theorem. -/
theorem minor_pos_of_diagonalSupported (W : OneFanWindow D)
    (hsupp : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      W.rows W.cols) : 0 < W.minor := by
  by_cases hq0 : W.q = 0
  · exact W.minor_pos_of_q_eq_zero hq0
  have hqpos : 0 < W.q := Nat.pos_of_ne_zero hq0
  have hqle : W.q ≤ m := by
    have := W.cq_le
    omega
  cases hside : W.side with
  | left =>
      by_cases hsmall : W.q ≤ m - 1
      · exact W.left_minor_pos_of_small hside hqpos hsmall hsupp
      · have hqeq : W.q = m := by omega
        obtain ⟨hc, hrho⟩ := W.left_full_endpoint hside hqeq hsupp
        have hW : W = leftFullWindow D := by
          obtain ⟨side, c, q, rho, hcq, hrows⟩ := W
          dsimp only at hside hqeq hc hrho ⊢
          subst side
          subst c
          subst q
          subst rho
          rfl
        rw [hW]
        exact leftFull_minor_pos D
  | right =>
      by_cases hsmall : W.q ≤ m - 1
      · exact W.right_minor_pos_of_small hside hqpos hsmall hsupp
      · have hqeq : W.q = m := by omega
        obtain ⟨hc, hrho⟩ := W.right_full_endpoint hside hqeq hsupp
        have hW : W = rightFullWindow D := by
          obtain ⟨side, c, q, rho, hcq, hrows⟩ := W
          dsimp only at hside hqeq hc hrho ⊢
          subst side
          subst c
          subst q
          subst rho
          rfl
        rw [hW]
        exact rightFull_minor_pos D

end OneFanWindow

namespace FanMinorWindow

variable {m : Nat} {D : TwoFanData m}

/-- Diagonal support of the left block of a fan window transports to its
one-fan presentation (in particular when the right block is empty). -/
theorem leftOneFan_diagonalSupported (W : FanMinorWindow D)
    (hsupp : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      W.fanRows W.fanCols) :
    DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      W.leftOneFan.rows W.leftOneFan.cols := by
  by_cases hell0 : W.ell = 0
  · intro t
    have ht := t.isLt
    simp [leftOneFan, hell0] at ht
  · have hell : 0 < W.ell := Nat.pos_of_ne_zero hell0
    have hq : 0 < W.leftOneFan.q := by simpa using hell
    apply (W.leftOneFan.left_diagonalSupported_iff (by rfl) hq).mpr
    let t : Fin W.ell := ⟨0, hell⟩
    have hdiag := (W.left_diagonal_supported_iff t).mp
      (hsupp (Fin.castAdd W.b t))
    change W.rho ≤
      (D.alpha ⟨m - W.ell, by
        have := W.ell_le
        omega⟩ : Nat)
    simpa [t] using hdiag

/-- Diagonal support of a right-only fan window transports to its one-fan
presentation. -/
theorem rightOneFan_diagonalSupported_of_ell_eq_zero (W : FanMinorWindow D)
    (hell0 : W.ell = 0)
    (hsupp : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      W.fanRows W.fanCols) :
    DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      W.rightOneFan.rows W.rightOneFan.cols := by
  by_cases hb0 : W.b = 0
  · intro t
    have ht := t.isLt
    simp [rightOneFan, hb0] at ht
  · have hb : 0 < W.b := Nat.pos_of_ne_zero hb0
    have hq : 0 < W.rightOneFan.q := by simpa using hb
    apply (W.rightOneFan.right_diagonalSupported_iff (by rfl) hq).mpr
    let t : Fin W.b := ⟨W.b - 1, by omega⟩
    have hdiag := (W.right_diagonal_supported_iff t).mp
      (hsupp (Fin.natAdd W.ell t))
    change m +
      (D.beta ⟨W.c + W.b - 1, by
        have := W.cb_le
        omega⟩ : Nat) - W.b ≤ W.rho
    change m - 1 +
      (D.beta ⟨W.c + (t : Nat), by
        have := W.cb_le
        have := t.isLt
        omega⟩ : Nat) ≤ W.rho + W.ell + (t : Nat) at hdiag
    dsimp only [t] at hdiag
    have hlabel : (⟨W.c + (W.b - 1), by
        have := W.cb_le
        omega⟩ : Fin m) = ⟨W.c + W.b - 1, by
          have := W.cb_le
          omega⟩ := by
      apply Fin.ext
      change W.c + (W.b - 1) = W.c + W.b - 1
      omega
    rw [hlabel] at hdiag
    rw [hell0] at hdiag
    omega

/-- Every diagonally supported genuine two-sided seam of order at least `m`
has positive raw fan minor.  The proof is strong induction on the order.  At
each step width one forces the supported row block onto one of the two seam
endpoints, where one cross minor vanishes and Desnanot--Jacobi reduces to a
positive quotient without introducing any nonvanishing assumption. -/
theorem fanMinor_pos_of_diagonalSupported_large (W : FanMinorWindow D)
    (hell : 0 < W.ell) (hb : 0 < W.b) (hq : m ≤ W.q)
    (hsupp : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      W.fanRows W.fanCols) : 0 < W.fanMinor := by
  let P : Nat → Prop := fun q ↦
    ∀ N : FanMinorWindow D, N.q = q → 0 < N.ell → 0 < N.b →
      m ≤ N.q →
      DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
        N.fanRows N.fanCols →
      0 < N.fanMinor
  have hP : ∀ q, P q := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
        intro N hNq hellN hbN hlargeN hsuppN
        have neighbor_pos : ∀ (K : FanMinorWindow D), K.q < q →
            DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
              K.fanRows K.fanCols →
            0 < K.fanMinor := by
          intro K hKq hsuppK
          by_cases hell0 : K.ell = 0
          · rw [K.fanMinor_eq_rightOneFan_minor_of_ell_eq_zero hell0]
            apply K.rightOneFan.minor_pos_of_diagonalSupported
            exact K.rightOneFan_diagonalSupported_of_ell_eq_zero hell0 hsuppK
          · by_cases hb0 : K.b = 0
            · rw [K.fanMinor_eq_leftOneFan_minor_of_b_eq_zero hb0]
              apply K.leftOneFan.minor_pos_of_diagonalSupported
              exact K.leftOneFan_diagonalSupported hsuppK
            · have hellK : 0 < K.ell := Nat.pos_of_ne_zero hell0
              have hbK : 0 < K.b := Nat.pos_of_ne_zero hb0
              by_cases hsmallK : K.q ≤ m - 1
              · exact K.fanMinor_pos_of_diagonalSupported_small
                  hellK hbK hsmallK hsuppK
              · have hlargeK : m ≤ K.q := by omega
                exact ih K.q hKq K rfl hellK hbK hlargeK hsuppK
        have htlq : (N.tl hbN).q < q := by
          rw [← hNq]
          dsimp only [FanMinorWindow.q, tl]
          omega
        have hbrq : (N.br hellN).q < q := by
          rw [← hNq]
          dsimp only [FanMinorWindow.q, br]
          omega
        have hmidq : (N.mid hellN hbN).q < q := by
          rw [← hNq]
          dsimp only [FanMinorWindow.q, mid]
          omega
        have htl : 0 < (N.tl hbN).fanMinor :=
          neighbor_pos (N.tl hbN) htlq
            (N.tl_diagonalSupported_general hbN hsuppN)
        have hbr : 0 < (N.br hellN).fanMinor :=
          neighbor_pos (N.br hellN) hbrq
            (N.br_diagonalSupported_general hellN hsuppN)
        have hmid : 0 < (N.mid hellN hbN).fanMinor :=
          neighbor_pos (N.mid hellN hbN) hmidq
            (N.mid_diagonalSupported_general hellN hbN hsuppN)
        have hbds := (N.fanMinor_diagonalSupported_iff hellN hbN).mp hsuppN
        have hwidth := N.large_seam_width_one hellN hbN hlargeN
        have hend : N.rho = N.lower hbN ∨ N.rho = N.upper hellN := by
          omega
        have hDJ := N.fanMinor_desnanotJacobi hellN hbN
        rcases hend with hlower | hupper
        · have htr := N.tr_fanMinor_eq_zero_of_rho_eq_lower_general
              hellN hbN hlower
          rw [htr, zero_mul, sub_zero] at hDJ
          have hprod : 0 < N.fanMinor * (N.mid hellN hbN).fanMinor := by
            rw [hDJ]
            exact mul_pos htl hbr
          exact pos_of_mul_pos_left hprod (le_of_lt hmid)
        · have hbl := N.bl_fanMinor_eq_zero_of_rho_eq_upper_general
              hellN hbN hupper
          rw [hbl, mul_zero, sub_zero] at hDJ
          have hprod : 0 < N.fanMinor * (N.mid hellN hbN).fanMinor := by
            rw [hDJ]
            exact mul_pos htl hbr
          exact pos_of_mul_pos_left hprod (le_of_lt hmid)
  exact hP W.q W rfl hell hb hq hsupp

end FanMinorWindow

end

end ColomboGeneralK2.Odd
