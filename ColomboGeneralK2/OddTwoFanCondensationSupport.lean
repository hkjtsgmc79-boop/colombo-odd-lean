import ColomboGeneralK2.OddTwoFanWidthOne
import ColomboGeneralK2.OddTwoFanWindowDJ

/-!
# Support bookkeeping for two-fan condensation

The three positive-side Desnanot--Jacobi neighbours inherit supported
diagonals.  At either endpoint of a large seam's width-one support interval,
one of the two cross neighbours is structurally zero.
-/

namespace ColomboGeneralK2.Odd

noncomputable section

namespace FanMinorWindow

variable {m : Nat} {D : TwoFanData m}

/-- Deleting the last right column can only move the lower support endpoint
weakly downward. -/
theorem tl_lower_le (W : FanMinorWindow D) (hb2 : 1 < W.b) :
    (W.tl (by omega)).lower (by simp [tl]; omega) ≤ W.lower (by omega) := by
  let hp : Fin m := ⟨W.c + W.b - 2, by
    have hcb := W.cb_le
    omega⟩
  let h : Fin m := W.lastRight (by omega)
  have hph : hp < h := by
    change W.c + W.b - 2 < W.c + W.b - 1
    omega
  have hbeta : (D.beta hp : Nat) + 1 ≤ (D.beta h : Nat) :=
    D.beta_strictMono hph
  have hqW : W.q = W.ell + W.b := rfl
  have hqTL : (W.tl (by omega)).q = W.ell + (W.b - 1) := rfl
  unfold lower
  simp only [q, tl, lastRight]
  rw [show (⟨W.c + (W.b - 1) - 1, by
      have hcb := W.cb_le
      omega⟩ : Fin m) = hp by
    apply Fin.ext
    dsimp [hp]
    omega]
  rw [show (⟨W.c + W.b - 1, by
      have hcb := W.cb_le
      omega⟩ : Fin m) = h by rfl]
  change m + (D.beta hp : Nat) - (W.ell + (W.b - 1)) ≤
    m + (D.beta h : Nat) - (W.ell + W.b)
  have hfloor := beta_succ_le (D := D) h
  have hh : (h : Nat) = W.c + W.b - 1 := rfl
  omega

/-- Deleting the first left column moves the upper support endpoint upward
by at least one. -/
theorem upper_add_one_le_br_upper (W : FanMinorWindow D) (hell2 : 1 < W.ell) :
    W.upper (by omega) + 1 ≤ (W.br (by omega)).upper (by simp [br]; omega) := by
  let a : Fin m := W.firstLeft (by omega)
  let an : Fin m := ⟨m - W.ell + 1, by
    have hell := W.ell_le
    omega⟩
  have han : a < an := by
    change m - W.ell < m - W.ell + 1
    omega
  have halpha : (D.alpha a : Nat) + 1 ≤ (D.alpha an : Nat) :=
    D.alpha_strictMono han
  have hellLe := W.ell_le
  unfold upper
  simp only [br, firstLeft]
  rw [show (⟨m - W.ell, by
      have hell := W.ell_le
      omega⟩ : Fin m) = a by rfl]
  rw [show (⟨m - (W.ell - 1), by
      have hell := W.ell_le
      omega⟩ : Fin m) = an by
    apply Fin.ext
    dsimp [an]
    omega]
  change (D.alpha a : Nat) + 1 ≤ (D.alpha an : Nat)
  exact halpha

/-- The top-left neighbour remains diagonally supported. -/
theorem tl_diagonalSupported (W : FanMinorWindow D)
    (hell : 0 < W.ell) (hb2 : 1 < W.b)
    (hsupp : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      W.fanRows W.fanCols) :
    DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      (W.tl (by omega)).fanRows (W.tl (by omega)).fanCols := by
  apply ((W.tl (by omega)).fanMinor_diagonalSupported_iff
    (by simp [tl]; omega) (by simp [tl]; omega)).mpr
  have hw := (W.fanMinor_diagonalSupported_iff hell (by omega)).mp hsupp
  constructor
  · exact le_trans (W.tl_lower_le hb2) hw.1
  · simpa [tl, upper, firstLeft] using hw.2

/-- The bottom-right neighbour remains diagonally supported. -/
theorem br_diagonalSupported (W : FanMinorWindow D)
    (hell2 : 1 < W.ell) (hb : 0 < W.b)
    (hsupp : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      W.fanRows W.fanCols) :
    DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      (W.br (by omega)).fanRows (W.br (by omega)).fanCols := by
  apply ((W.br (by omega)).fanMinor_diagonalSupported_iff
    (by simp [br]; omega) (by simp [br]; omega)).mpr
  have hw := (W.fanMinor_diagonalSupported_iff (by omega) hb).mp hsupp
  constructor
  · unfold lower at hw ⊢
    change m + (D.beta (W.lastRight hb) : Nat) -
        ((W.ell - 1) + W.b) ≤ W.rho + 1
    have hfloor := beta_succ_le (D := D) (W.lastRight hb)
    unfold q at hw
    omega
  · exact le_trans (Nat.add_le_add_right hw.2 1)
      (W.upper_add_one_le_br_upper hell2)

/-- The common middle neighbour remains diagonally supported. -/
theorem mid_diagonalSupported (W : FanMinorWindow D)
    (hell2 : 1 < W.ell) (hb2 : 1 < W.b)
    (hsupp : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      W.fanRows W.fanCols) :
    DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      (W.mid (by omega) (by omega)).fanRows
      (W.mid (by omega) (by omega)).fanCols := by
  apply ((W.mid (by omega) (by omega)).fanMinor_diagonalSupported_iff
    (by simp [mid]; omega) (by simp [mid]; omega)).mpr
  have htl := W.tl_diagonalSupported (by omega) hb2 hsupp
  have htlBounds := ((W.tl (by omega)).fanMinor_diagonalSupported_iff
    (by simp [tl]; omega) (by simp [tl]; omega)).mp htl
  have hlastEq :
      (W.mid (by omega) (by omega)).lastRight (by simp [mid]; omega) =
        (W.tl (by omega)).lastRight (by simp [tl]; omega) := by
    apply Fin.ext
    simp [mid, tl, lastRight]
  constructor
  · have htlLower := htlBounds.1
    unfold lower at htlLower ⊢
    simp only [q, tl, mid, lastRight] at htlLower ⊢
    change m + (D.beta
        ((W.mid (by omega) (by omega)).lastRight (by simp [mid]; omega)) : Nat) -
        ((W.ell - 1) + (W.b - 1)) ≤ W.rho + 1
    change m + (D.beta
        ((W.tl (by omega)).lastRight (by simp [tl]; omega)) : Nat) -
        (W.ell + (W.b - 1)) ≤ W.rho at htlLower
    rw [hlastEq]
    have hfloor := beta_succ_le (D := D)
      ((W.tl (by omega)).lastRight (by simp [tl]; omega))
    have hellLe := W.ell_le
    have hcb := W.cb_le
    omega
  · have hbr := W.br_diagonalSupported hell2 (by omega) hsupp
    have hbrBounds := ((W.br (by omega)).fanMinor_diagonalSupported_iff
      (by simp [br]; omega) (by simp [br]; omega)).mp hbr
    simpa [mid, br, upper, firstLeft] using hbrBounds.2

/-- At the lower endpoint, the top-right cross neighbour is structurally
zero. -/
theorem tr_fanMinor_eq_zero_of_rho_eq_lower (W : FanMinorWindow D)
    (hell2 : 1 < W.ell) (hb : 0 < W.b)
    (hrho : W.rho = W.lower hb) :
    (W.tr (by omega)).fanMinor = 0 := by
  apply (W.tr (by omega)).fanMinor_eq_zero_of_not_window
    (by simp [tr]; omega) (by simp [tr]; omega)
  rw [not_and_or]
  left
  apply not_le_of_gt
  unfold lower at hrho ⊢
  simp only [q, tr, lastRight]
  change W.rho < m + (D.beta (W.lastRight hb) : Nat) -
    ((W.ell - 1) + W.b)
  have hfloor := beta_succ_le (D := D) (W.lastRight hb)
  have hellLe := W.ell_le
  have hlastVal := W.lastRight_val hb
  unfold q at hrho
  omega

/-- At the upper endpoint, the bottom-left cross neighbour is structurally
zero. -/
theorem bl_fanMinor_eq_zero_of_rho_eq_upper (W : FanMinorWindow D)
    (hell : 0 < W.ell) (hb2 : 1 < W.b)
    (hrho : W.rho = W.upper hell) :
    (W.bl (by omega)).fanMinor = 0 := by
  apply (W.bl (by omega)).fanMinor_eq_zero_of_not_window
    (by simp [bl]; omega) (by simp [bl]; omega)
  rw [not_and_or]
  right
  apply not_le_of_gt
  simpa [bl, upper, firstLeft] using
    (show W.upper hell < W.rho + 1 by omega)

end FanMinorWindow

end

end ColomboGeneralK2.Odd
