import ColomboGeneralK2.OddTwoFanData
import ColomboGeneralK2.OddDesnanotJacobi
import ColomboGeneralK2.OddStaircaseSupport

/-!
# Canonical two-fan seam windows

The raw coefficient matrix is indexed from zero.  A `FanMinorWindow` selects
the consecutive row interval beginning at `rho`, a terminal block of `ell`
left columns, and a consecutive block of `b` right columns beginning at `c`.
The definitions below intentionally allow empty left or right blocks; the
nonempty seam theorem records its genuinely two-sided hypotheses separately.
-/

namespace ColomboGeneralK2.Odd

noncomputable section

/-- Data for one naturally ordered two-fan minor. -/
structure FanMinorWindow {m : Nat} (D : TwoFanData m) where
  ell : Nat
  c : Nat
  b : Nat
  rho : Nat
  ell_le : ell ≤ m
  cb_le : c + b ≤ m
  rows_le : rho + (ell + b) ≤ 3 * m - 1

namespace FanMinorWindow

variable {m : Nat} {D : TwoFanData m}

/-- The order of the selected minor. -/
def q (W : FanMinorWindow D) : Nat := W.ell + W.b

/-- The consecutive ambient row selection. -/
def fanRows (W : FanMinorWindow D) : Fin W.q ↪o Fin (3 * m - 1) :=
  intervalOrderEmb W.rho W.rows_le

/-- The natural `[L | R]` column number at a position in the selected
left-suffix/right-block list. -/
def fanColValue (W : FanMinorWindow D) (t : Fin W.q) : Fin (2 * m) :=
  dite ((t : Nat) < W.ell)
  (fun _ ↦ ⟨m - W.ell + (t : Nat), by
      have := W.ell_le
      have ht' := t.isLt
      omega⟩)
  (fun ht ↦ ⟨m + W.c + ((t : Nat) - W.ell), by
      have ht' := t.isLt
      change (t : Nat) < W.ell + W.b at ht'
      have := W.cb_le
      have hle : W.ell ≤ (t : Nat) := Nat.le_of_not_gt ht
      omega⟩
  )

/-- The canonical ordered column selection: the final `ell` left labels,
followed by the `b` right labels starting at `c`. -/
def fanCols (W : FanMinorWindow D) : Fin W.q ↪o Fin (2 * m) :=
  OrderEmbedding.ofStrictMono W.fanColValue (by
    intro x y hxy
    unfold fanColValue
    by_cases hx : (x : Nat) < W.ell
    · by_cases hy : (y : Nat) < W.ell
      · change (fanColValue W x : Nat) < (fanColValue W y : Nat)
        simp only [fanColValue, dif_pos hx, dif_pos hy, Fin.val_mk]
        exact Nat.add_lt_add_left hxy _
      · change (fanColValue W x : Nat) < (fanColValue W y : Nat)
        simp only [fanColValue, dif_pos hx, dif_neg hy, Fin.val_mk]
        have hle := W.ell_le
        have hylt := y.isLt
        omega
    · by_cases hy : (y : Nat) < W.ell
      · change (fanColValue W x : Nat) < (fanColValue W y : Nat)
        simp only [fanColValue, dif_neg hx, dif_pos hy, Fin.val_mk]
        exfalso
        have hxy' : (x : Nat) ≤ (y : Nat) := hxy.le
        exact hx (lt_of_le_of_lt hxy' hy)
      · change (fanColValue W x : Nat) < (fanColValue W y : Nat)
        simp only [fanColValue, dif_neg hx, dif_neg hy, Fin.val_mk]
        have hxle : W.ell ≤ (x : Nat) := Nat.le_of_not_gt hx
        have hyle : W.ell ≤ (y : Nat) := Nat.le_of_not_gt hy
        omega)

/-- The raw two-fan minor on the canonical window. -/
def fanMinor (W : FanMinorWindow D) : ℝ :=
  matrixMinor (twoFanCoefficientMatrix D) W.fanRows W.fanCols

@[simp]
theorem q_eq (W : FanMinorWindow D) : W.q = W.ell + W.b := rfl

@[simp]
theorem fanRows_val (W : FanMinorWindow D) (t : Fin W.q) :
    ((W.fanRows t : Fin (3 * m - 1)) : Nat) = W.rho + (t : Nat) := by
  rfl

/-- Value formula on the left part of the selected columns. -/
  theorem fanCols_left_val (W : FanMinorWindow D) (t : Fin W.ell) :
    ((W.fanCols (Fin.castAdd W.b t) : Fin (2 * m)) : Nat) =
      m - W.ell + (t : Nat) := by
  change (fanColValue W (Fin.castAdd W.b t) : Nat) = _
  simp [fanColValue]

/-- Value formula on the right part of the selected columns. -/
theorem fanCols_right_val (W : FanMinorWindow D) (t : Fin W.b) :
    ((W.fanCols (Fin.natAdd W.ell t) : Fin (2 * m)) : Nat) =
      m + W.c + (t : Nat) := by
  change (fanColValue W (Fin.natAdd W.ell t) : Nat) = _
  simp [fanColValue]

/-- The left portion of `fanCols` is the terminal left-label suffix, not
merely an ambient-number interval. -/
theorem fanCols_left_eq (W : FanMinorWindow D) (t : Fin W.ell) :
    W.fanCols (Fin.castAdd W.b t) =
      twoFanColumnEquiv m (Sum.inl
        ⟨m - W.ell + (t : Nat), by
          have := W.ell_le
          have := t.isLt
          omega⟩) := by
  apply Fin.ext
  rw [W.fanCols_left_val]
  rfl

/-- The right portion of `fanCols` is the consecutive labelled right block. -/
theorem fanCols_right_eq (W : FanMinorWindow D) (t : Fin W.b) :
    W.fanCols (Fin.natAdd W.ell t) =
      twoFanColumnEquiv m (Sum.inr
        ⟨W.c + (t : Nat), by
          have := W.cb_le
          have := t.isLt
          omega⟩) := by
  apply Fin.ext
  rw [W.fanCols_right_val]
  simp [twoFanColumnEquiv, finSumFinEquiv_apply_right]
  omega

/-- A strictly increasing finite-ordinal map gains at least one ambient
rank for each increase of its source index. -/
theorem strictMono_fin_add_le {n p : Nat} (f : Fin n → Fin p)
    (hf : StrictMono f) (i : Fin n) (d : Nat) (h : (i : Nat) + d < n) :
    (f i : Nat) + d ≤ (f ⟨(i : Nat) + d, h⟩ : Nat) := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hd : (i : Nat) + d < n := by omega
      let j : Fin n := ⟨(i : Nat) + d, hd⟩
      let j' : Fin n := ⟨(i : Nat) + (d + 1), h⟩
      have hjlt : j < j' := by
        change (i : Nat) + d < (i : Nat) + (d + 1)
        omega
      have hstep : (f j : Nat) + 1 ≤ (f j' : Nat) := hf hjlt
      have hrec : (f i : Nat) + d ≤ (f j : Nat) := by
        simpa [j] using ih hd
      calc
        (f i : Nat) + (d + 1) = ((f i : Nat) + d) + 1 := by omega
        _ ≤ (f j : Nat) + 1 := Nat.succ_le_succ hrec
        _ ≤ (f j' : Nat) := hstep
        _ = (f ⟨(i : Nat) + (d + 1), h⟩ : Nat) := by rfl

/-- Strict growth of left merge ranks across the terminal suffix. -/
theorem alpha_suffix_growth (W : FanMinorWindow D) (t : Fin W.ell) :
    (D.alpha ⟨m - W.ell, by
      have := W.ell_le
      have ht := t.isLt
      omega⟩ : Nat) + (t : Nat) ≤
      (D.alpha ⟨m - W.ell + (t : Nat), by
        have := W.ell_le
        have := t.isLt
        omega⟩ : Nat) := by
  exact strictMono_fin_add_le D.alpha D.alpha_strictMono
    ⟨m - W.ell, by
      have := W.ell_le
      have hm := D.hm
      have ht := t.isLt
      omega⟩
    (t : Nat) (by
      change m - W.ell + (t : Nat) < m
      have := W.ell_le
      have := t.isLt
      omega)

/-- Strict growth of right merge ranks up to the final selected right label. -/
theorem beta_block_growth (W : FanMinorWindow D) (hb : 0 < W.b)
    (t : Fin W.b) :
    (D.beta ⟨W.c + (t : Nat), by
      have := W.cb_le
      have := t.isLt
      omega⟩ : Nat) + (W.b - 1 - (t : Nat)) ≤
      (D.beta ⟨W.c + W.b - 1, by
        have := W.cb_le
        omega⟩ : Nat) := by
  have htarget : W.c + (t : Nat) + (W.b - 1 - (t : Nat)) =
      W.c + W.b - 1 := by
    have := t.isLt
    omega
  have hlt : W.c + (t : Nat) + (W.b - 1 - (t : Nat)) < m := by
    rw [htarget]
    have := W.cb_le
    omega
  have h := strictMono_fin_add_le D.beta D.beta_strictMono
    ⟨W.c + (t : Nat), by
      have := W.cb_le
      have := t.isLt
      omega⟩
    (W.b - 1 - (t : Nat)) hlt
  simpa [htarget] using h

/-- The first (smallest-labelled) selected left column. -/
def firstLeft (W : FanMinorWindow D) (hell : 0 < W.ell) : Fin m :=
  ⟨m - W.ell, by
    have := W.ell_le
    omega⟩

/-- The last (largest-labelled) selected right column. -/
def lastRight (W : FanMinorWindow D) (hb : 0 < W.b) : Fin m :=
  ⟨W.c + W.b - 1, by
    have := W.cb_le
    omega⟩

/-- The lower row bound forced by the last selected right column. -/
def lower (W : FanMinorWindow D) (hb : 0 < W.b) : Nat :=
  m + (D.beta (W.lastRight hb) : Nat) - W.q

/-- The upper row bound forced by the first selected left column. -/
def upper (W : FanMinorWindow D) (hell : 0 < W.ell) : Nat :=
  D.alpha (W.firstLeft hell)

@[simp]
theorem firstLeft_val (W : FanMinorWindow D) (hell : 0 < W.ell) :
    (W.firstLeft hell : Nat) = m - W.ell := rfl

@[simp]
theorem lastRight_val (W : FanMinorWindow D) (hb : 0 < W.b) :
    (W.lastRight hb : Nat) = W.c + W.b - 1 := rfl

/-- The left diagonal entry at a selected suffix position is in its exact
support interval precisely when it does not exceed its upper endpoint. -/
theorem left_diagonal_supported_iff (W : FanMinorWindow D) (t : Fin W.ell) :
    ((twoFanCoefficientMatrix_intervalSupport D).lo
        (W.fanCols (Fin.castAdd W.b t)) ≤
      W.fanRows (Fin.castAdd W.b t) ∧
      W.fanRows (Fin.castAdd W.b t) ≤
        (twoFanCoefficientMatrix_intervalSupport D).hi
          (W.fanCols (Fin.castAdd W.b t))) ↔
      W.rho + (t : Nat) ≤
        (D.alpha ⟨m - W.ell + (t : Nat), by
          have := W.ell_le
          have := t.isLt
          omega⟩ : Nat) := by
  rw [W.fanCols_left_eq t]
  have hrow : (W.fanRows (Fin.castAdd W.b t) : Nat) = W.rho + (t : Nat) := by
    simpa using W.fanRows_val (Fin.castAdd W.b t)
  simp only [twoFanCoefficientMatrix_intervalSupport, TwoFanData.coefficientLo,
    TwoFanData.coefficientHi, Equiv.symm_apply_apply, Fin.le_iff_val_le_val, hrow]
  omega

/-- The right diagonal entry at a selected block position is in its exact
support interval precisely when it exceeds its lower endpoint. -/
theorem right_diagonal_supported_iff (W : FanMinorWindow D) (t : Fin W.b) :
    ((twoFanCoefficientMatrix_intervalSupport D).lo
        (W.fanCols (Fin.natAdd W.ell t)) ≤
      W.fanRows (Fin.natAdd W.ell t) ∧
      W.fanRows (Fin.natAdd W.ell t) ≤
        (twoFanCoefficientMatrix_intervalSupport D).hi
          (W.fanCols (Fin.natAdd W.ell t))) ↔
      m - 1 + (D.beta ⟨W.c + (t : Nat), by
        have := W.cb_le
        have := t.isLt
        omega⟩ : Nat) ≤ W.rho + W.ell + (t : Nat) := by
  rw [W.fanCols_right_eq t]
  have hrow : (W.fanRows (Fin.natAdd W.ell t) : Nat) =
      W.rho + W.ell + (t : Nat) := by
    simpa [Nat.add_assoc] using W.fanRows_val (Fin.natAdd W.ell t)
  simp only [twoFanCoefficientMatrix_intervalSupport, TwoFanData.coefficientLo,
    TwoFanData.coefficientHi, Equiv.symm_apply_apply, Fin.le_iff_val_le_val, hrow]
  constructor
  · intro h
    omega
  · intro h
    refine ⟨?_, ?_⟩
    · simpa [Nat.add_assoc] using h
    · have hrow := W.rows_le
      have ht := t.isLt
      omega

/-- Every labelled right knot has merge rank at least one beyond its label.
The extra one is the Dyck-order contribution of the corresponding left knot. -/
theorem beta_succ_le (j : Fin m) : (j : Nat) + 1 ≤ (D.beta j : Nat) := by
  let z : Fin m := ⟨0, by have hm := D.hm; omega⟩
  have hbeta0 : 1 ≤ (D.beta z : Nat) := by
    have hpair := D.alpha_lt_beta z
    have halpha : (D.alpha z : Nat) = 0 := by
      simpa [z] using congrArg Fin.val D.alpha_zero
    omega
  have hgrowth := strictMono_fin_add_le D.beta D.beta_strictMono z (j : Nat) (by
    change 0 + (j : Nat) < m
    omega)
  change (j : Nat) + 1 ≤ (D.beta j : Nat)
  have hzval : (z : Nat) = 0 := rfl
  simpa [z, Nat.zero_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    le_trans (Nat.add_le_add_right hbeta0 (j : Nat)) hgrowth

/-- Exact support criterion for a genuine two-sided seam window.  It is the
paper's interval `[m + beta(lastRight) - q, alpha(firstLeft)]`, in zero-based
row indexing.  The proof uses strict rank growth in both labelled fans; it is
not a small-dimensional computation. -/
theorem fanMinor_diagonalSupported_iff (W : FanMinorWindow D)
    (hell : 0 < W.ell) (hb : 0 < W.b) :
    DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
        W.fanRows W.fanCols ↔
      W.lower hb ≤ W.rho ∧ W.rho ≤ W.upper hell := by
  constructor
  · intro hsupp
    constructor
    · let t : Fin W.b := ⟨W.b - 1, by omega⟩
      have hright := (W.right_diagonal_supported_iff t).mp
        (hsupp (Fin.natAdd W.ell t))
      have hindex :
          (⟨W.c + (t : Nat), by
            have := W.cb_le
            have := t.isLt
            omega⟩ : Fin m) = W.lastRight hb := by
        apply Fin.ext
        dsimp [t]
        omega
      rw [hindex] at hright
      have hright' : m - 1 + (D.beta (W.lastRight hb) : Nat) ≤
          W.rho + W.ell + (W.b - 1) := by
        simpa [t] using hright
      unfold lower q
      omega
    · let t : Fin W.ell := ⟨0, hell⟩
      have hleft := (W.left_diagonal_supported_iff t).mp
        (hsupp (Fin.castAdd W.b t))
      simpa [upper, firstLeft, t] using hleft
  · rintro ⟨hlower, hupper⟩ t
    by_cases ht : (t : Nat) < W.ell
    · let u : Fin W.ell := ⟨(t : Nat), ht⟩
      have htu : t = Fin.castAdd W.b u := by
        apply Fin.ext
        rfl
      rw [htu]
      apply (W.left_diagonal_supported_iff u).mpr
      have hupper' : W.rho ≤ (D.alpha (W.firstLeft hell) : Nat) := by
        simpa [upper] using hupper
      have hgrow := W.alpha_suffix_growth u
      simpa [firstLeft] using
        le_trans (Nat.add_le_add_right hupper' (u : Nat)) hgrow
    · let u : Fin W.b := ⟨(t : Nat) - W.ell, by
        have ht' := t.isLt
        change (t : Nat) < W.ell + W.b at ht'
        have hle : W.ell ≤ (t : Nat) := Nat.le_of_not_gt ht
        omega⟩
      have htu : t = Fin.natAdd W.ell u := by
        apply Fin.ext
        dsimp [u]
        have hle : W.ell ≤ (t : Nat) := Nat.le_of_not_gt ht
        omega
      rw [htu]
      apply (W.right_diagonal_supported_iff u).mpr
      have hlast : W.q ≤ m + (D.beta (W.lastRight hb) : Nat) := by
        have hbeta := beta_succ_le (D := D) (W.lastRight hb)
        unfold q
        simp only [lastRight_val] at hbeta
        have hell' := W.ell_le
        omega
      have hlower' : m + (D.beta (W.lastRight hb) : Nat) ≤ W.rho + W.q := by
        exact Nat.sub_le_iff_le_add.mp (by simpa [lower] using hlower)
      have hgrow := W.beta_block_growth hb u
      unfold q at hlower'
      have hlastEq :
          (⟨W.c + W.b - 1, by
            have := W.cb_le
            omega⟩ : Fin m) = W.lastRight hb := by
        rfl
      rw [hlastEq] at hgrow
      omega

/-- Outside the exact two-sided seam interval, the canonical minor is zero.
This is an arbitrary-order application of the staircase Hall obstruction,
not an assumed vanishing of a seam determinant. -/
theorem fanMinor_eq_zero_of_not_window (W : FanMinorWindow D)
    (hell : 0 < W.ell) (hb : 0 < W.b)
    (hout : ¬ (W.lower hb ≤ W.rho ∧ W.rho ≤ W.upper hell)) :
    W.fanMinor = 0 := by
  unfold fanMinor
  apply matrixMinor_eq_zero_of_not_diagonalSupported
    (twoFanCoefficientMatrix_intervalSupport D) W.fanRows W.fanCols
  rwa [W.fanMinor_diagonalSupported_iff hell hb]

end FanMinorWindow

end

end ColomboGeneralK2.Odd
