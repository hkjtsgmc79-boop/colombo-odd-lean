import ColomboGeneralK2.OddTwoFanLargeSeam
import ColomboGeneralK2.OddStaircasePromotion
import ColomboGeneralK2.OddCriticalSplitBridge

/-!
# Total nonnegativity of the raw two-fan coefficient matrix

This module is the assembly layer.  It identifies every consecutive column
interval with one of the canonical one-fan or two-fan windows, dispatches
the corresponding supported solid minor to the established positivity
theorems, and then invokes staircase promotion.
-/

namespace ColomboGeneralK2.Odd

noncomputable section

namespace TwoFanTN

variable {m : Nat} (D : TwoFanData m)

/-- A consecutive solid window wholly in the left fan. -/
def leftSolidWindow (k rowStart colStart : Nat)
    (hrow : rowStart + k ≤ 3 * m - 1) (hleft : colStart + k ≤ m) :
    OneFanWindow D where
  side := .left
  c := colStart
  q := k
  rho := rowStart
  cq_le := hleft
  rows_le := hrow

/-- A consecutive solid window wholly in the right fan. -/
def rightSolidWindow (k rowStart colStart : Nat)
    (hrow : rowStart + k ≤ 3 * m - 1) (hright : m ≤ colStart)
    (hcol : colStart + k ≤ 2 * m) : OneFanWindow D where
  side := .right
  c := colStart - m
  q := k
  rho := rowStart
  cq_le := by omega
  rows_le := hrow

/-- A consecutive solid window crossing the unique fan boundary. -/
def seamSolidWindow (k rowStart colStart : Nat)
    (hrow : rowStart + k ≤ 3 * m - 1) (hleft : colStart < m)
    (hcross : m < colStart + k) (hcol : colStart + k ≤ 2 * m) :
    FanMinorWindow D where
  ell := m - colStart
  c := 0
  b := k - (m - colStart)
  rho := rowStart
  ell_le := by omega
  cb_le := by omega
  rows_le := by omega

@[simp]
theorem leftSolidWindow_rows (k rowStart colStart : Nat)
    (hrow : rowStart + k ≤ 3 * m - 1) (hleft : colStart + k ≤ m) :
    (leftSolidWindow D k rowStart colStart hrow hleft).rows =
      intervalOrderEmb rowStart hrow := by
  rfl

@[simp]
theorem rightSolidWindow_rows (k rowStart colStart : Nat)
    (hrow : rowStart + k ≤ 3 * m - 1) (hright : m ≤ colStart)
    (hcol : colStart + k ≤ 2 * m) :
    (rightSolidWindow D k rowStart colStart hrow hright hcol).rows =
      intervalOrderEmb rowStart hrow := by
  rfl

theorem leftSolidWindow_cols (k rowStart colStart : Nat)
    (hrow : rowStart + k ≤ 3 * m - 1) (hleft : colStart + k ≤ m)
    (hcol : colStart + k ≤ 2 * m) :
    (leftSolidWindow D k rowStart colStart hrow hleft).cols =
      intervalOrderEmb colStart hcol := by
  ext t
  change colStart + (t : Nat) = colStart + (t : Nat)
  rfl

theorem rightSolidWindow_cols (k rowStart colStart : Nat)
    (hrow : rowStart + k ≤ 3 * m - 1) (hright : m ≤ colStart)
    (hcol : colStart + k ≤ 2 * m) :
    (rightSolidWindow D k rowStart colStart hrow hright hcol).cols =
      intervalOrderEmb colStart hcol := by
  ext t
  change m + (colStart - m) + (t : Nat) = colStart + (t : Nat)
  omega

theorem seamSolidWindow_q (k rowStart colStart : Nat)
    (hrow : rowStart + k ≤ 3 * m - 1) (hleft : colStart < m)
    (hcross : m < colStart + k) (hcol : colStart + k ≤ 2 * m) :
    (seamSolidWindow D k rowStart colStart hrow hleft hcross hcol).q = k := by
  simp only [seamSolidWindow, FanMinorWindow.q]
  omega

def seamSolidOrderIso (k rowStart colStart : Nat)
    (hrow : rowStart + k ≤ 3 * m - 1) (hleft : colStart < m)
    (hcross : m < colStart + k) (hcol : colStart + k ≤ 2 * m) :
    Fin (seamSolidWindow D k rowStart colStart hrow hleft hcross hcol).q ≃o Fin k :=
  Fin.castOrderIso (seamSolidWindow_q D k rowStart colStart hrow hleft hcross hcol)

theorem seamSolidWindow_rows_comp (k rowStart colStart : Nat)
    (hrow : rowStart + k ≤ 3 * m - 1) (hleft : colStart < m)
    (hcross : m < colStart + k) (hcol : colStart + k ≤ 2 * m) :
    (seamSolidWindow D k rowStart colStart hrow hleft hcross hcol).fanRows =
      (seamSolidOrderIso D k rowStart colStart hrow hleft hcross hcol).toOrderEmbedding.comp
        (intervalOrderEmb rowStart hrow) := by
  let W := seamSolidWindow D k rowStart colStart hrow hleft hcross hcol
  let e := seamSolidOrderIso D k rowStart colStart hrow hleft hcross hcol
  ext t
  change W.rho + (t : Nat) = rowStart + (e t : Nat)
  have he : (e t : Nat) = (t : Nat) := by
    change ((Fin.castOrderIso
      (seamSolidWindow_q D k rowStart colStart hrow hleft hcross hcol)) t : Nat) =
        (t : Nat)
    rw [Fin.castOrderIso_apply]
    exact Fin.val_cast _ _
  change rowStart + (t : Nat) = rowStart + (e t : Nat)
  omega

theorem seamSolidWindow_cols_comp (k rowStart colStart : Nat)
    (hrow : rowStart + k ≤ 3 * m - 1) (hleft : colStart < m)
    (hcross : m < colStart + k) (hcol : colStart + k ≤ 2 * m) :
    (seamSolidWindow D k rowStart colStart hrow hleft hcross hcol).fanCols =
      (seamSolidOrderIso D k rowStart colStart hrow hleft hcross hcol).toOrderEmbedding.comp
        (intervalOrderEmb colStart hcol) := by
  let W := seamSolidWindow D k rowStart colStart hrow hleft hcross hcol
  let e := seamSolidOrderIso D k rowStart colStart hrow hleft hcross hcol
  -- The two pieces have respectively the ambient values below and above `m`.
  ext t
  have he : (e t : Nat) = (t : Nat) := by
    change ((Fin.castOrderIso
      (seamSolidWindow_q D k rowStart colStart hrow hleft hcross hcol)) t : Nat) =
        (t : Nat)
    rw [Fin.castOrderIso_apply]
    exact Fin.val_cast _ _
  change (W.fanColValue t : Nat) = colStart + (e t : Nat)
  unfold FanMinorWindow.fanColValue
  dsimp only [W, seamSolidWindow]
  by_cases ht : (t : Nat) < m - colStart
  · rw [dif_pos ht]
    change m - (m - colStart) + (t : Nat) = colStart + (e t : Nat)
    omega
  · rw [dif_neg ht]
    change m + 0 + ((t : Nat) - (m - colStart)) = colStart + (e t : Nat)
    have htq := t.isLt
    omega

theorem matrixMinor_comp_orderIso
    {r c a b : Nat} (A : Matrix (Fin r) (Fin c) ℝ)
    (rows : Fin b ↪o Fin r) (cols : Fin b ↪o Fin c)
    (e : Fin a ≃o Fin b) :
    matrixMinor A (e.toOrderEmbedding.comp rows) (e.toOrderEmbedding.comp cols) =
      matrixMinor A rows cols := by
  unfold matrixMinor
  rw [show A.submatrix (e.toOrderEmbedding.comp rows)
      (e.toOrderEmbedding.comp cols) =
      (A.submatrix rows cols).submatrix e.toOrderEmbedding e.toOrderEmbedding by
        simp [Matrix.submatrix_submatrix]]
  exact Matrix.det_submatrix_equiv_self e.toEquiv _

theorem leftSolidWindow_diagonalSupported (k rowStart colStart : Nat)
    (hrow : rowStart + k ≤ 3 * m - 1) (hleft : colStart + k ≤ m)
    (hcol : colStart + k ≤ 2 * m)
    (hsupp : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      (intervalOrderEmb rowStart hrow) (intervalOrderEmb colStart hcol)) :
    DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      (leftSolidWindow D k rowStart colStart hrow hleft).rows
      (leftSolidWindow D k rowStart colStart hrow hleft).cols := by
  rw [leftSolidWindow_rows, leftSolidWindow_cols]
  exact hsupp

theorem rightSolidWindow_diagonalSupported (k rowStart colStart : Nat)
    (hrow : rowStart + k ≤ 3 * m - 1) (hright : m ≤ colStart)
    (hcol : colStart + k ≤ 2 * m)
    (hsupp : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      (intervalOrderEmb rowStart hrow) (intervalOrderEmb colStart hcol)) :
    DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      (rightSolidWindow D k rowStart colStart hrow hright hcol).rows
      (rightSolidWindow D k rowStart colStart hrow hright hcol).cols := by
  rw [rightSolidWindow_rows, rightSolidWindow_cols]
  exact hsupp

theorem seamSolidWindow_diagonalSupported (k rowStart colStart : Nat)
    (hrow : rowStart + k ≤ 3 * m - 1) (hleft : colStart < m)
    (hcross : m < colStart + k) (hcol : colStart + k ≤ 2 * m)
    (hsupp : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      (intervalOrderEmb rowStart hrow) (intervalOrderEmb colStart hcol)) :
    DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      (seamSolidWindow D k rowStart colStart hrow hleft hcross hcol).fanRows
      (seamSolidWindow D k rowStart colStart hrow hleft hcross hcol).fanCols := by
  rw [seamSolidWindow_rows_comp, seamSolidWindow_cols_comp]
  exact hsupp.comp
    (seamSolidOrderIso D k rowStart colStart hrow hleft hcross hcol).toOrderEmbedding

theorem leftSolidWindow_minor_eq (k rowStart colStart : Nat)
    (hrow : rowStart + k ≤ 3 * m - 1) (hleft : colStart + k ≤ m)
    (hcol : colStart + k ≤ 2 * m) :
    (leftSolidWindow D k rowStart colStart hrow hleft).minor =
      matrixMinor (twoFanCoefficientMatrix D)
        (intervalOrderEmb rowStart hrow) (intervalOrderEmb colStart hcol) := by
  unfold OneFanWindow.minor
  rw [leftSolidWindow_rows D k rowStart colStart hrow hleft,
    leftSolidWindow_cols D k rowStart colStart hrow hleft hcol]
  rfl

theorem rightSolidWindow_minor_eq (k rowStart colStart : Nat)
    (hrow : rowStart + k ≤ 3 * m - 1) (hright : m ≤ colStart)
    (hcol : colStart + k ≤ 2 * m) :
    (rightSolidWindow D k rowStart colStart hrow hright hcol).minor =
      matrixMinor (twoFanCoefficientMatrix D)
        (intervalOrderEmb rowStart hrow) (intervalOrderEmb colStart hcol) := by
  unfold OneFanWindow.minor
  rw [rightSolidWindow_rows D k rowStart colStart hrow hright hcol,
    rightSolidWindow_cols D k rowStart colStart hrow hright hcol]
  rfl

theorem seamSolidWindow_minor_eq (k rowStart colStart : Nat)
    (hrow : rowStart + k ≤ 3 * m - 1) (hleft : colStart < m)
    (hcross : m < colStart + k) (hcol : colStart + k ≤ 2 * m) :
    (seamSolidWindow D k rowStart colStart hrow hleft hcross hcol).fanMinor =
      matrixMinor (twoFanCoefficientMatrix D)
        (intervalOrderEmb rowStart hrow) (intervalOrderEmb colStart hcol) := by
  unfold FanMinorWindow.fanMinor
  rw [seamSolidWindow_rows_comp, seamSolidWindow_cols_comp]
  exact matrixMinor_comp_orderIso _ _ _ _

end TwoFanTN

/-- Every supported consecutive solid minor of the raw two-fan coefficient
matrix is strictly positive.  The ambient consecutive column interval is
classified at the unique boundary between the left and right fans. -/
theorem twoFan_supportedSolidMinor_pos {m : Nat} (D : TwoFanData m) :
    SupportedSolidMinorsPositive (twoFanCoefficientMatrix_intervalSupport D) := by
  intro k rowStart colStart hrow hcol hsupp
  by_cases hleft : colStart + k ≤ m
  · let W := TwoFanTN.leftSolidWindow D k rowStart colStart hrow hleft
    have hsuppW : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
        W.rows W.cols := by
      dsimp only [W]
      exact TwoFanTN.leftSolidWindow_diagonalSupported D k rowStart colStart
        hrow hleft hcol hsupp
    have hpos : 0 < W.minor := W.minor_pos_of_diagonalSupported hsuppW
    have hminor : W.minor = matrixMinor (twoFanCoefficientMatrix D)
        (intervalOrderEmb rowStart hrow) (intervalOrderEmb colStart hcol) := by
      dsimp only [W]
      exact TwoFanTN.leftSolidWindow_minor_eq D k rowStart colStart hrow hleft hcol
    rw [hminor] at hpos
    exact hpos
  · by_cases hright : m ≤ colStart
    · let W := TwoFanTN.rightSolidWindow D k rowStart colStart hrow hright hcol
      have hsuppW : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
          W.rows W.cols := by
        dsimp only [W]
        exact TwoFanTN.rightSolidWindow_diagonalSupported D k rowStart colStart
          hrow hright hcol hsupp
      have hpos : 0 < W.minor := W.minor_pos_of_diagonalSupported hsuppW
      have hminor : W.minor = matrixMinor (twoFanCoefficientMatrix D)
          (intervalOrderEmb rowStart hrow) (intervalOrderEmb colStart hcol) := by
        dsimp only [W]
        exact TwoFanTN.rightSolidWindow_minor_eq D k rowStart colStart hrow hright hcol
      rw [hminor] at hpos
      exact hpos
    · have hstart : colStart < m := lt_of_not_ge hright
      have hcross : m < colStart + k := lt_of_not_ge hleft
      let W := TwoFanTN.seamSolidWindow D k rowStart colStart hrow hstart hcross hcol
      have hell : 0 < W.ell := by
        dsimp only [W, TwoFanTN.seamSolidWindow]
        omega
      have hb : 0 < W.b := by
        dsimp only [W, TwoFanTN.seamSolidWindow]
        omega
      have hq : W.q = k := by
        dsimp only [W]
        exact TwoFanTN.seamSolidWindow_q D k rowStart colStart hrow hstart hcross hcol
      have hsuppW : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
          W.fanRows W.fanCols := by
        dsimp only [W]
        exact TwoFanTN.seamSolidWindow_diagonalSupported D k rowStart colStart
          hrow hstart hcross hcol hsupp
      have hpos : 0 < W.fanMinor := by
        by_cases hsmall : k ≤ m - 1
        · have hsmallW : W.q ≤ m - 1 := by rw [hq]; exact hsmall
          exact W.fanMinor_pos_of_diagonalSupported_small hell hb hsmallW hsuppW
        · have hlargeW : m ≤ W.q := by
            rw [hq]
            omega
          exact W.fanMinor_pos_of_diagonalSupported_large hell hb hlargeW hsuppW
      have hminor : W.fanMinor = matrixMinor (twoFanCoefficientMatrix D)
          (intervalOrderEmb rowStart hrow) (intervalOrderEmb colStart hcol) := by
        dsimp only [W]
        exact TwoFanTN.seamSolidWindow_minor_eq D k rowStart colStart
          hrow hstart hcross hcol
      rw [hminor] at hpos
      exact hpos

/-- The raw two-fan coefficient matrix is totally nonnegative. -/
theorem twoFanCoefficientMatrix_tn {m : Nat} (D : TwoFanData m) :
    IsTotallyNonnegative (twoFanCoefficientMatrix D) :=
  isTotallyNonnegative_of_supportedSolidMinorsPositive
    (twoFanCoefficientMatrix_intervalSupport D) (twoFan_supportedSolidMinor_pos D)

/-- Paper-dimensional critical split: a totally nonnegative left factor and
the raw two-fan coefficient matrix yield a totally nonnegative split matrix. -/
theorem twoFan_criticalSplit_isTotallyNonnegative {m : Nat} (D : TwoFanData m)
    (H : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ)
    (B : Matrix (Fin (2 * m)) (Fin (3 * m - 1)) ℝ)
    (hfactor : H = B * twoFanCoefficientMatrix D)
    (hB : IsTotallyNonnegative B) :
    IsTotallyNonnegative H :=
  criticalSplit_isTotallyNonnegative_rectangular H B (twoFanCoefficientMatrix D)
    hfactor hB (twoFanCoefficientMatrix_tn D)

/-- Determinant corollary of the paper-dimensional critical split. -/
theorem twoFan_criticalSplit_determinant_nonnegative {m : Nat} (D : TwoFanData m)
    (H : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ)
    (B : Matrix (Fin (2 * m)) (Fin (3 * m - 1)) ℝ)
    (hfactor : H = B * twoFanCoefficientMatrix D)
    (hB : IsTotallyNonnegative B) :
    0 ≤ H.det :=
  criticalSplit_determinant_nonnegative H B (twoFanCoefficientMatrix D)
    hfactor hB (twoFanCoefficientMatrix_tn D)

end

end ColomboGeneralK2.Odd
