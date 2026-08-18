import ColomboGeneralK2.OddTwoFanKnotOrder
import ColomboGeneralK2.OddTwoFanWindows
import ColomboGeneralK2.OddSlidingRootBasis

/-!
# One-fan solid minors of the raw two-fan matrix

This file treats consecutive row blocks and consecutive column blocks wholly
inside one fan.  The support assertions are exact; supported minors are then
reduced to the sliding-root determinant when their order is at most `m - 1`.
-/

open scoped BigOperators
open Finset Matrix Polynomial

namespace ColomboGeneralK2.Odd

noncomputable section

/-- Which of the two ordered fans supplies a one-sided column block. -/
inductive OneFanSide where
  | left
  | right
deriving DecidableEq, Repr

/-- A square solid window whose columns lie entirely in one fan. -/
structure OneFanWindow {m : Nat} (D : TwoFanData m) where
  side : OneFanSide
  c : Nat
  q : Nat
  rho : Nat
  cq_le : c + q ≤ m
  rows_le : rho + q ≤ 3 * m - 1

namespace OneFanWindow

variable {m : Nat} {D : TwoFanData m}

/-- Consecutive selected rows. -/
def rows (W : OneFanWindow D) : Fin W.q ↪o Fin (3 * m - 1) :=
  intervalOrderEmb W.rho W.rows_le

/-- Consecutive selected columns, within the selected fan. -/
def cols (W : OneFanWindow D) : Fin W.q ↪o Fin (2 * m) :=
  match W.side with
  | .left => OrderEmbedding.ofStrictMono (fun t ↦
      ⟨W.c + (t : Nat), by
        have := W.cq_le
        have := t.isLt
        omega⟩) (by
      intro x y hxy
      change W.c + (x : Nat) < W.c + (y : Nat)
      exact Nat.add_lt_add_left hxy _)
  | .right => OrderEmbedding.ofStrictMono (fun t ↦
      ⟨m + W.c + (t : Nat), by
        have := W.cq_le
        have := t.isLt
        omega⟩) (by
      intro x y hxy
      change m + W.c + (x : Nat) < m + W.c + (y : Nat)
      exact Nat.add_lt_add_left hxy _)

/-- The raw one-fan solid minor. -/
def minor (W : OneFanWindow D) : ℝ :=
  matrixMinor (twoFanCoefficientMatrix D) W.rows W.cols

@[simp] theorem rows_val (W : OneFanWindow D) (t : Fin W.q) :
    ((W.rows t : Fin (3 * m - 1)) : Nat) = W.rho + (t : Nat) := rfl

/-- The selected left column is the corresponding natural left column. -/
theorem cols_left_eq (W : OneFanWindow D) (hside : W.side = .left)
    (t : Fin W.q) :
    W.cols t = twoFanColumnEquiv m (Sum.inl ⟨W.c + (t : Nat), by
      have := W.cq_le
      have := t.isLt
      omega⟩) := by
  cases h : W.side <;> simp_all [cols, twoFanColumnEquiv,
    finSumFinEquiv_apply_left]

/-- The selected right column is the corresponding natural right column. -/
theorem cols_right_eq (W : OneFanWindow D) (hside : W.side = .right)
    (t : Fin W.q) :
    W.cols t = twoFanColumnEquiv m (Sum.inr ⟨W.c + (t : Nat), by
      have := W.cq_le
      have := t.isLt
      omega⟩) := by
  cases h : W.side
  · simp_all
  · simp_all [cols, twoFanColumnEquiv, finSumFinEquiv_apply_right]
    omega

/-- The selected left sample points. -/
def leftPoints (W : OneFanWindow D) : Fin W.q → ℝ := fun t ↦
  D.s ⟨W.c + (t : Nat), by
    have := W.cq_le
    have := t.isLt
    omega⟩

/-- The selected right sample points. -/
def rightPoints (W : OneFanWindow D) : Fin W.q → ℝ := fun t ↦
  D.u ⟨W.c + (t : Nat), by
    have := W.cq_le
    have := t.isLt
    omega⟩

theorem leftPoints_strictMono (W : OneFanWindow D) : StrictMono W.leftPoints := by
  intro x y hxy
  unfold leftPoints
  apply D.s_strictMono
  change W.c + (x : Nat) < W.c + (y : Nat)
  exact Nat.add_lt_add_left hxy _

theorem rightPoints_strictMono (W : OneFanWindow D) : StrictMono W.rightPoints := by
  intro x y hxy
  unfold rightPoints
  apply D.u_strictMono
  change W.c + (x : Nat) < W.c + (y : Nat)
  exact Nat.add_lt_add_left hxy _

/-- The first selected label, available for a nonempty one-fan window. -/
def firstLabel (W : OneFanWindow D) (hq : 0 < W.q) : Fin m :=
  ⟨W.c, by
    have := W.cq_le
    omega⟩

/-- The final selected label, available for a nonempty one-fan window. -/
def lastLabel (W : OneFanWindow D) (hq : 0 < W.q) : Fin m :=
  ⟨W.c + W.q - 1, by
    have := W.cq_le
    omega⟩

@[simp] theorem firstLabel_val (W : OneFanWindow D) (hq : 0 < W.q) :
    (W.firstLabel hq : Nat) = W.c := rfl

@[simp] theorem lastLabel_val (W : OneFanWindow D) (hq : 0 < W.q) :
    (W.lastLabel hq : Nat) = W.c + W.q - 1 := rfl

/-- Strict growth of left merge ranks along the selected column block. -/
theorem alpha_block_growth (W : OneFanWindow D) (hq : 0 < W.q) (t : Fin W.q) :
    (D.alpha (W.firstLabel hq) : Nat) + (t : Nat) ≤
      (D.alpha ⟨W.c + (t : Nat), by
        have := W.cq_le
        have := t.isLt
        omega⟩ : Nat) := by
  exact FanMinorWindow.strictMono_fin_add_le D.alpha D.alpha_strictMono
    (W.firstLabel hq) (t : Nat) (by
      change W.c + (t : Nat) < m
      have := W.cq_le
      have := t.isLt
      omega)

/-- Strict growth of right merge ranks up to the final selected label. -/
theorem beta_block_growth (W : OneFanWindow D) (hq : 0 < W.q) (t : Fin W.q) :
    (D.beta ⟨W.c + (t : Nat), by
      have := W.cq_le
      have := t.isLt
      omega⟩ : Nat) + (W.q - 1 - (t : Nat)) ≤
      (D.beta (W.lastLabel hq) : Nat) := by
  have htarget : W.c + (t : Nat) + (W.q - 1 - (t : Nat)) =
      W.c + W.q - 1 := by
    have := t.isLt
    omega
  have h := FanMinorWindow.strictMono_fin_add_le D.beta D.beta_strictMono
    ⟨W.c + (t : Nat), by
      have := W.cq_le
      have := t.isLt
      omega⟩
    (W.q - 1 - (t : Nat)) (by
      rw [htarget]
      have := W.cq_le
      omega)
  simpa [lastLabel, htarget] using h

/-- Exact support criterion for a nonempty left-only solid window. -/
theorem left_diagonalSupported_iff (W : OneFanWindow D)
    (hside : W.side = .left) (hq : 0 < W.q) :
    DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D) W.rows W.cols ↔
      W.rho ≤ (D.alpha (W.firstLabel hq) : Nat) := by
  constructor
  · intro hsupp
    have h := hsupp ⟨0, hq⟩
    rw [W.cols_left_eq hside] at h
    have hrow : (W.rows ⟨0, hq⟩ : Nat) = W.rho := by simp [rows_val]
    simpa [twoFanCoefficientMatrix_intervalSupport, TwoFanData.coefficientLo,
      TwoFanData.coefficientHi, firstLabel, hrow] using h.2
  · intro hfirst t
    rw [W.cols_left_eq hside]
    have hgrow := W.alpha_block_growth hq t
    have hrow : (W.rows t : Nat) = W.rho + (t : Nat) := W.rows_val t
    simp only [twoFanCoefficientMatrix_intervalSupport, TwoFanData.coefficientLo,
      TwoFanData.coefficientHi, Equiv.symm_apply_apply, Fin.le_iff_val_le_val]
    constructor
    · omega
    · change W.rho + (t : Nat) ≤
        (D.alpha ⟨W.c + (t : Nat), by
          have := W.cq_le
          have := t.isLt
          omega⟩ : Nat)
      simpa [firstLabel] using le_trans (Nat.add_le_add_right hfirst (t : Nat)) hgrow

/-- Exact support criterion for a nonempty right-only solid window. -/
theorem right_diagonalSupported_iff (W : OneFanWindow D)
    (hside : W.side = .right) (hq : 0 < W.q) :
    DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D) W.rows W.cols ↔
      m + (D.beta (W.lastLabel hq) : Nat) - W.q ≤ W.rho := by
  constructor
  · intro hsupp
    let t : Fin W.q := ⟨W.q - 1, by omega⟩
    have h := hsupp t
    rw [W.cols_right_eq hside t] at h
    have hrow : (W.rows t : Nat) = W.rho + W.q - 1 := by
      change W.rho + (W.q - 1) = W.rho + W.q - 1
      omega
    have hlabel :
        (⟨W.c + (t : Nat), by
          have := W.cq_le
          have := t.isLt
          omega⟩ : Fin m) = W.lastLabel hq := by
      apply Fin.ext
      dsimp [t]
      omega
    have h' : m - 1 + (D.beta (W.lastLabel hq) : Nat) ≤
        W.rho + W.q - 1 := by
      rw [hlabel] at h
      have hlow := h.1
      simp only [twoFanCoefficientMatrix_intervalSupport,
        TwoFanData.coefficientLo, Equiv.symm_apply_apply,
        Fin.le_iff_val_le_val] at hlow
      simpa [hrow] using hlow
    omega
  · intro hlast t
    rw [W.cols_right_eq hside]
    have hgrow := W.beta_block_growth hq t
    have hrow : (W.rows t : Nat) = W.rho + (t : Nat) := W.rows_val t
    simp only [twoFanCoefficientMatrix_intervalSupport, TwoFanData.coefficientLo,
      TwoFanData.coefficientHi, Equiv.symm_apply_apply, Fin.le_iff_val_le_val]
    constructor
    · change m - 1 +
          (D.beta ⟨W.c + (t : Nat), by
            have := W.cq_le
            have := t.isLt
            omega⟩ : Nat) ≤ W.rho + (t : Nat)
      have hlast' : m + (D.beta (W.lastLabel hq) : Nat) ≤ W.rho + W.q := by
        exact Nat.sub_le_iff_le_add.mp hlast
      have hqbound : W.q ≤ m + (D.beta (W.lastLabel hq) : Nat) := by
        have hbeta := FanMinorWindow.beta_succ_le (D := D) (W.lastLabel hq)
        have := W.cq_le
        omega
      omega
    · have := W.rows_le
      have := t.isLt
      omega

/-- A one-fan minor outside its exact diagonal-support condition is zero. -/
theorem minor_eq_zero_of_not_diagonalSupported (W : OneFanWindow D)
    (h : ¬ DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D) W.rows W.cols) :
    W.minor = 0 := by
  unfold minor
  exact matrixMinor_eq_zero_of_not_diagonalSupported
    (twoFanCoefficientMatrix_intervalSupport D) W.rows W.cols h

/-- The unmasked degree-`m-2` sliding product at an ambient row. -/
def fullSlidingAt (D : TwoFanData m) (i : Fin (3 * m - 1)) (y : ℝ) : ℝ :=
  Finset.univ.prod (fun h : Fin (m - 2) ↦
    y - D.openKnot (D.slideIndex i h))

/-- If a merged knot lies in a degree-`m-2` sliding interval, its evaluation
of the corresponding full sliding product is zero.  This is the basic
mask-to-root bridge used below. -/
theorem fullSlidingAt_eq_zero_of_mergeRank_in_slide
    (D : TwoFanData m) (i : Fin (3 * m - 1)) (r : Fin (2 * m))
    (hbefore : (r : Nat) < (i : Nat))
    (hafter : (i : Nat) ≤ m - 2 + (r : Nat)) :
    fullSlidingAt D i (D.z r) = 0 := by
  have hm := D.hm
  have hd : 0 < m - 2 := by omega
  let h : Fin (m - 2) := ⟨m - 2 + (r : Nat) - (i : Nat), by
    have := r.isLt
    have := i.isLt
    omega⟩
  rw [fullSlidingAt]
  apply Finset.prod_eq_zero (Finset.mem_univ h)
  rw [sub_eq_zero]
  rw [← D.openKnot_mergeOpenIndex r]
  congr 1
  apply Fin.ext
  dsimp [h, TwoFanData.mergeOpenIndex, TwoFanData.slideIndex]
  omega

/-- In a small supported left-only window, the support mask agrees with the
full sliding evaluation at every selected point. -/
theorem left_entry_eq_fullSlidingAt (W : OneFanWindow D)
    (hside : W.side = .left) (hq : W.q ≤ m - 1)
    (hsupp : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      W.rows W.cols) (v p : Fin W.q) :
    twoFanCoefficientMatrix D (W.rows v) (W.cols p) =
      fullSlidingAt D (W.rows v) (W.leftPoints p) := by
  rw [W.cols_left_eq hside, twoFanCoefficientMatrix_left_apply]
  unfold TwoFanData.leftCoefficient
  let j : Fin m := ⟨W.c + (p : Nat), by
    have := W.cq_le
    have := p.isLt
    omega⟩
  change (if (W.rows v : Nat) ≤ (D.alpha j : Nat) then
      Finset.univ.prod (fun h : Fin (m - 2) ↦
        D.s j - D.openKnot (D.slideIndex (W.rows v) h)) else 0) = _
  change (if (W.rows v : Nat) ≤ (D.alpha j : Nat) then
      Finset.univ.prod (fun h : Fin (m - 2) ↦
        D.s j - D.openKnot (D.slideIndex (W.rows v) h)) else 0) =
    fullSlidingAt D (W.rows v) (D.s j)
  by_cases hmask : (W.rows v : Nat) ≤ (D.alpha j : Nat)
  · rw [if_pos hmask]
    rfl
  · rw [if_neg hmask]
    have hdiag := hsupp p
    rw [W.cols_left_eq hside p] at hdiag
    have hdiag' : W.rho + (p : Nat) ≤ (D.alpha j : Nat) := by
      simpa [twoFanCoefficientMatrix_intervalSupport, TwoFanData.coefficientLo,
        TwoFanData.coefficientHi, rows_val, j] using hdiag.2
    have hbefore : (D.alpha j : Nat) < (W.rows v : Nat) := lt_of_not_ge hmask
    have hrow : (W.rows v : Nat) = W.rho + (v : Nat) := W.rows_val v
    have hafter : (W.rows v : Nat) ≤ m - 2 + (D.alpha j : Nat) := by
      have hpv : (p : Nat) < (v : Nat) := by omega
      have := v.isLt
      have hq' : W.q ≤ m - 1 := hq
      omega
    have hz := fullSlidingAt_eq_zero_of_mergeRank_in_slide D (W.rows v)
      (D.alpha j) hbefore hafter
    simpa [TwoFanData.s] using hz.symm

/-- Reversing every factor of a full sliding product gives the uniform
right-column sign. -/
theorem right_product_eq_negPow_fullSlidingAt (D : TwoFanData m)
    (i : Fin (3 * m - 1)) (y : ℝ) :
    Finset.univ.prod (fun h : Fin (m - 2) ↦
      D.openKnot (D.slideIndex i h) - y) =
      (-1 : ℝ) ^ (m - 2) * fullSlidingAt D i y := by
  simp_rw [show ∀ h : Fin (m - 2),
    D.openKnot (D.slideIndex i h) - y =
      -(y - D.openKnot (D.slideIndex i h)) by intro h; ring]
  rw [Finset.prod_neg]
  simp only [Finset.card_univ, Fintype.card_fin]
  rfl

/-- In a small supported right-only window, the support mask agrees with the
full sliding evaluation, with the fixed factor-reversal sign. -/
theorem right_entry_eq_negPow_fullSlidingAt (W : OneFanWindow D)
    (hside : W.side = .right) (hq : W.q ≤ m - 1)
    (hsupp : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      W.rows W.cols) (v p : Fin W.q) :
    twoFanCoefficientMatrix D (W.rows v) (W.cols p) =
      (-1 : ℝ) ^ (m - 2) * fullSlidingAt D (W.rows v) (W.rightPoints p) := by
  rw [W.cols_right_eq hside, twoFanCoefficientMatrix_right_apply]
  unfold TwoFanData.rightCoefficient
  let j : Fin m := ⟨W.c + (p : Nat), by
    have := W.cq_le
    have := p.isLt
    omega⟩
  change (if m - 1 + (D.beta j : Nat) ≤ (W.rows v : Nat) then
      Finset.univ.prod (fun h : Fin (m - 2) ↦
        D.openKnot (D.slideIndex (W.rows v) h) - D.u j) else 0) = _
  change (if m - 1 + (D.beta j : Nat) ≤ (W.rows v : Nat) then
      Finset.univ.prod (fun h : Fin (m - 2) ↦
        D.openKnot (D.slideIndex (W.rows v) h) - D.u j) else 0) =
    (-1 : ℝ) ^ (m - 2) * fullSlidingAt D (W.rows v) (D.u j)
  by_cases hmask : m - 1 + (D.beta j : Nat) ≤ (W.rows v : Nat)
  · rw [if_pos hmask, right_product_eq_negPow_fullSlidingAt]
  · simp only [if_neg hmask]
    have hdiag := hsupp p
    rw [W.cols_right_eq hside p] at hdiag
    have hdiag' : m - 1 + (D.beta j : Nat) ≤ W.rho + (p : Nat) := by
      simpa [twoFanCoefficientMatrix_intervalSupport, TwoFanData.coefficientLo,
        TwoFanData.coefficientHi, rows_val, j] using hdiag.1
    have hrow : (W.rows v : Nat) = W.rho + (v : Nat) := W.rows_val v
    have hafter : (W.rows v : Nat) ≤ m - 2 + (D.beta j : Nat) := by
      omega
    have hbefore : (D.beta j : Nat) < (W.rows v : Nat) := by
      have hpv : (v : Nat) < (p : Nat) := by omega
      have := p.isLt
      have hq' : W.q ≤ m - 1 := hq
      have hm := D.hm
      omega
    have hz := fullSlidingAt_eq_zero_of_mergeRank_in_slide D (W.rows v)
      (D.beta j) hbefore hafter
    rw [show D.u j = D.z (D.beta j) by rfl, hz]
    simp

/-- The whole selected left block is the full sliding-evaluation matrix in
the small range.  In particular this equality contains no assumed sign or
determinant formula. -/
theorem left_submatrix_eq_fullSlidingMatrix (W : OneFanWindow D)
    (hside : W.side = .left) (hq : W.q ≤ m - 1)
    (hsupp : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      W.rows W.cols) :
    (twoFanCoefficientMatrix D).submatrix W.rows W.cols =
      Matrix.of (fun v p ↦ fullSlidingAt D (W.rows v) (W.leftPoints p)) := by
  ext v p
  exact W.left_entry_eq_fullSlidingAt hside hq hsupp v p

/-- The whole selected right block is the full sliding-evaluation matrix up
to the fixed factor-reversal sign in every entry. -/
theorem right_submatrix_eq_negPow_fullSlidingMatrix (W : OneFanWindow D)
    (hside : W.side = .right) (hq : W.q ≤ m - 1)
    (hsupp : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      W.rows W.cols) :
    (twoFanCoefficientMatrix D).submatrix W.rows W.cols =
      Matrix.of (fun v p ↦
        (-1 : ℝ) ^ (m - 2) * fullSlidingAt D (W.rows v) (W.rightPoints p)) := by
  ext v p
  exact W.right_entry_eq_negPow_fullSlidingAt hside hq hsupp v p

/-- The empty one-fan minor has its canonical positive value. -/
theorem minor_pos_of_q_eq_zero (W : OneFanWindow D) (hq : W.q = 0) :
    0 < W.minor := by
  obtain ⟨side, c, q, rho, hcq, hrows⟩ := W
  change q = 0 at hq
  subst q
  simp [minor]

/-- A supported order-one one-fan minor is its positive diagonal entry. -/
theorem minor_pos_of_q_eq_one (W : OneFanWindow D) (hq : W.q = 1)
    (hsupp : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      W.rows W.cols) : 0 < W.minor := by
  obtain ⟨side, c, q, rho, hcq, hrows⟩ := W
  change q = 1 at hq
  subst q
  rw [minor, matrixMinor_one]
  exact hsupp.entry_pos 0

/-- A supported full left fan can occur only at its forced endpoint window. -/
theorem left_full_endpoint (W : OneFanWindow D) (hside : W.side = .left)
    (hq : W.q = m)
    (hsupp : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      W.rows W.cols) : W.c = 0 ∧ W.rho = 0 := by
  have hm := D.hm
  have hc : W.c = 0 := by
    have := W.cq_le
    omega
  have hqpos : 0 < W.q := by rw [hq]; omega
  have hsupport := (W.left_diagonalSupported_iff hside hqpos).mp hsupp
  have hfirst : W.firstLabel hqpos = ⟨0, by omega⟩ := by
    apply Fin.ext
    change W.c = 0
    exact hc
  have halpha : (D.alpha (W.firstLabel hqpos) : Nat) = 0 := by
    rw [hfirst]
    simpa using congrArg Fin.val D.alpha_zero
  constructor
  · exact hc
  · omega

/-- A supported full right fan can occur only at its forced endpoint window. -/
theorem right_full_endpoint (W : OneFanWindow D) (hside : W.side = .right)
    (hq : W.q = m)
    (hsupp : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      W.rows W.cols) : W.c = 0 ∧ W.rho = 2 * m - 1 := by
  have hm := D.hm
  have hc : W.c = 0 := by
    have := W.cq_le
    omega
  have hqpos : 0 < W.q := by rw [hq]; omega
  have hsupport := (W.right_diagonalSupported_iff hside hqpos).mp hsupp
  have hlast : W.lastLabel hqpos = ⟨m - 1, by omega⟩ := by
    apply Fin.ext
    change W.c + W.q - 1 = m - 1
    omega
  have hbeta : (D.beta (W.lastLabel hqpos) : Nat) = 2 * m - 1 := by
    rw [hlast]
    simpa using congrArg Fin.val D.beta_last
  have hrows := W.rows_le
  constructor
  · exact hc
  · omega

/-- The open knot at offset `n` from the first selected row.  The fallback is
irrelevant in every range used by the small-seam factorization, but keeps the
root lists total functions as required by `OddSlidingRootBasis`. -/
def rootAt (W : OneFanWindow D) (n : Nat) : ℝ :=
  if hn : W.rho + n < 4 * m - 2 then
    D.openKnot ⟨W.rho + n, hn⟩
  else 0

/-- Early roots in the sliding-root basis. -/
def smallA (W : OneFanWindow D) (n : Nat) : ℝ := W.rootAt n

/-- Late roots in the sliding-root basis. -/
def smallB (W : OneFanWindow D) (n : Nat) : ℝ := W.rootAt (m - 1 + n)

/-- The common factor shared by all full sliding polynomials in a small
window. -/
def smallCommon (W : OneFanWindow D) (y : ℝ) : ℝ :=
  (Ico W.q (m - 1)).prod (fun n ↦ y - W.rootAt n)

@[simp] theorem rootAt_eq_openKnot (W : OneFanWindow D) (n : Nat)
    (hn : W.rho + n < 4 * m - 2) :
    W.rootAt n = D.openKnot ⟨W.rho + n, hn⟩ := by
  simp [rootAt, hn]

/-- Reindex a full sliding product by its actual open-vector root offsets. -/
theorem fullSlidingAt_eq_prod_Ico_roots (W : OneFanWindow D)
    (v : Fin W.q) (y : ℝ) :
    fullSlidingAt D (W.rows v) y =
      (Ico ((v : Nat) + 1) ((v : Nat) + m - 1)).prod
        (fun n ↦ y - W.rootAt n) := by
  classical
  rw [fullSlidingAt, Finset.prod_fin_eq_prod_range]
  conv_rhs => rw [Finset.prod_Ico_eq_prod_range]
  have hm := D.hm
  have hdifference : (v : Nat) + m - 1 - ((v : Nat) + 1) = m - 2 := by
    omega
  rw [hdifference]
  apply Finset.prod_congr rfl
  intro h hh
  have hh' : h < m - 2 := Finset.mem_range.mp hh
  simp only [dif_pos hh']
  have hroot : W.rho + ((v : Nat) + 1 + h) < 4 * m - 2 := by
    have hrows := W.rows_le
    have hv := v.isLt
    have hm := D.hm
    omega
  rw [W.rootAt_eq_openKnot _ hroot]
  congr 2
  apply Fin.ext
  dsimp [TwoFanData.slideIndex]
  have hrow : (W.rows v : Nat) = W.rho + (v : Nat) := W.rows_val v
  omega

/-- The exact common-factor decomposition of a full sliding polynomial in a
small one-fan window.  The remaining factor is exactly the basis supplied by
`OddSlidingRootBasis`. -/
theorem fullSlidingAt_eq_smallCommon_mul_evalMatrix_entry
    (W : OneFanWindow D) (hq : W.q ≤ m - 1)
    (v : Fin W.q) (y : ℝ) :
    fullSlidingAt D (W.rows v) y = W.smallCommon y *
      OddSlidingRootBasis.evalMatrix W.q W.smallA W.smallB (fun _ ↦ y) v
        ⟨0, Nat.zero_lt_of_lt v.isLt⟩ := by
  classical
  let f : Nat → ℝ := fun n ↦ y - W.rootAt n
  have hvq : (v : Nat) + 1 ≤ W.q := by omega
  have hvm : (v : Nat) + 1 ≤ m - 1 := le_trans hvq hq
  have hlate :
      (Finset.range (v : Nat)).prod (fun h ↦ y - W.smallB h) =
        (Ico (m - 1) (m - 1 + (v : Nat))).prod f := by
    rw [Finset.prod_Ico_eq_prod_range]
    simp only [Nat.add_sub_cancel_left]
    apply Finset.prod_congr rfl
    intro h hh
    simp [smallB]
  have hearly :
      (Ico ((v : Nat) + 1) W.q).prod (fun h ↦ y - W.smallA h) =
        (Ico ((v : Nat) + 1) W.q).prod f := by
    apply Finset.prod_congr rfl
    intro h hh
    simp [f, smallA]
  rw [fullSlidingAt_eq_prod_Ico_roots]
  change (Ico ((v : Nat) + 1) ((v : Nat) + m - 1)).prod f = _
  rw [← Finset.prod_Ico_consecutive f hvm (by omega)]
  rw [← Finset.prod_Ico_consecutive f hvq hq]
  rw [smallCommon]
  change (_ * _) * _ = _ *
    (OddSlidingRootBasis.slidingRoot W.q W.smallA W.smallB v).eval y
  rw [OddSlidingRootBasis.slidingRoot, Polynomial.eval_mul,
    Polynomial.eval_prod, Polynomial.eval_prod]
  simp_rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [hlate, hearly]
  simp only [f]
  have hupper : (v : Nat) + m - 1 = (v : Nat) + (m - 1) := by omega
  rw [hupper]
  ring_nf

/-- The early and late root lists satisfy the strict cross ordering required
by `OddSlidingRootBasis`.  The proof accounts for the repeated exterior
anchors directly; no global strictness of the open vector is assumed. -/
theorem smallA_lt_smallB (W : OneFanWindow D) (hq : W.q ≤ m - 1)
    (i j : Nat) (hij : i < j) (hj : j < W.q) :
    W.smallA j < W.smallB i := by
  have hm := D.hm
  have hrows := W.rows_le
  have hjm : j < m - 1 := lt_of_lt_of_le hj hq
  have hiq : i < W.q := lt_trans hij hj
  have hx : W.rho + j < 4 * m - 2 := by omega
  have hy : W.rho + (m - 1 + i) < 4 * m - 2 := by omega
  rw [smallA, smallB, W.rootAt_eq_openKnot _ hx,
    W.rootAt_eq_openKnot _ hy]
  unfold TwoFanData.openKnot
  by_cases hxA : W.rho + j < m - 1
  · simp only [dif_pos hxA]
    have hyA : ¬ W.rho + (m - 1 + i) < m - 1 := by omega
    simp only [dif_neg hyA]
    by_cases hyZ : W.rho + (m - 1 + i) < 3 * m - 1
    · simp only [dif_pos hyZ]
      exact D.leftAnchor_lt _
    · simp only [dif_neg hyZ]
      exact lt_trans (D.leftAnchor_lt ⟨0, by omega⟩)
        (D.lt_rightAnchor ⟨0, by omega⟩)
  · simp only [dif_neg hxA]
    have hxZ : W.rho + j < 3 * m - 1 := by omega
    simp only [dif_pos hxZ]
    have hyA : ¬ W.rho + (m - 1 + i) < m - 1 := by omega
    simp only [dif_neg hyA]
    by_cases hyZ : W.rho + (m - 1 + i) < 3 * m - 1
    · simp only [dif_pos hyZ]
      apply D.z_strict
      change (W.rho + j) - (m - 1) <
        (W.rho + (m - 1 + i)) - (m - 1)
      omega
    · simp only [dif_neg hyZ]
      exact D.lt_rightAnchor _

/-- Every common factor is positive at every selected left sample point of a
supported small window. -/
theorem smallCommon_pos_at_leftPoint (W : OneFanWindow D)
    (hside : W.side = .left) (_hq : W.q ≤ m - 1)
    (hsupp : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      W.rows W.cols) (p : Fin W.q) : 0 < W.smallCommon (W.leftPoints p) := by
  have hm := D.hm
  have hqpos : 0 < W.q := Nat.zero_lt_of_lt p.isLt
  have hfirst := (W.left_diagonalSupported_iff hside hqpos).mp hsupp
  rw [smallCommon]
  apply Finset.prod_pos
  intro n hn
  have hn' := Finset.mem_Ico.mp hn
  let j : Fin m := ⟨W.c + (p : Nat), by
    have := W.cq_le
    have := p.isLt
    omega⟩
  have hroot : W.rho + n < 4 * m - 2 := by
    have hrows := W.rows_le
    omega
  rw [W.rootAt_eq_openKnot n hroot]
  change 0 < D.s j - D.openKnot ⟨W.rho + n, hroot⟩
  apply sub_pos.mpr
  change D.openKnot ⟨W.rho + n, hroot⟩ < D.z (D.alpha j)
  apply D.openKnot_lt_z_of_lt_mergeOpenIndex
  have hfirstGrow : (D.alpha (W.firstLabel hqpos) : Nat) ≤
      (D.alpha j : Nat) := by
    apply D.alpha_strictMono.monotone
    change W.c ≤ W.c + (p : Nat)
    omega
  change W.rho + n < m - 1 + (D.alpha j : Nat)
  omega

/-- Matrix form of the common-factor decomposition at the selected left
points. -/
theorem fullSlidingMatrix_eq_smallCommon_mul_evalMatrix_left
    (W : OneFanWindow D) (hq : W.q ≤ m - 1) :
    Matrix.of (fun v p ↦ fullSlidingAt D (W.rows v) (W.leftPoints p)) =
      Matrix.of (fun v p ↦ W.smallCommon (W.leftPoints p) *
        OddSlidingRootBasis.evalMatrix W.q W.smallA W.smallB W.leftPoints v p) := by
  ext v p
  have h := W.fullSlidingAt_eq_smallCommon_mul_evalMatrix_entry hq v
    (W.leftPoints p)
  simpa [OddSlidingRootBasis.evalMatrix] using h

/-- Strict positivity of every supported nonempty left-only solid minor of
order at most `m - 1`. -/
theorem left_minor_pos_of_small (W : OneFanWindow D)
    (hside : W.side = .left) (_hqpos : 0 < W.q) (hq : W.q ≤ m - 1)
    (hsupp : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      W.rows W.cols) : 0 < W.minor := by
  unfold minor matrixMinor
  rw [W.left_submatrix_eq_fullSlidingMatrix hside hq hsupp,
    W.fullSlidingMatrix_eq_smallCommon_mul_evalMatrix_left hq,
    Matrix.det_mul_row]
  apply mul_pos
  · apply Finset.prod_pos
    intro p hp
    exact W.smallCommon_pos_at_leftPoint hside hq hsupp p
  · apply OddSlidingRootBasis.det_evalMatrix_pos
    · intro i j hij hj
      exact W.smallA_lt_smallB hq i j hij hj
    · exact W.leftPoints_strictMono

/-- The positive magnitude of a right common factor, with its sign removed
factor by factor. -/
def smallCommonRightMagnitude (W : OneFanWindow D) (y : ℝ) : ℝ :=
  (Ico W.q (m - 1)).prod (fun n ↦ W.rootAt n - y)

/-- Reversing all common-factor differences records their exact sign. -/
theorem smallCommon_eq_negPow_mul_rightMagnitude (W : OneFanWindow D)
    (_hq : W.q ≤ m - 1) (y : ℝ) :
    W.smallCommon y = (-1 : ℝ) ^ (m - 1 - W.q) *
      W.smallCommonRightMagnitude y := by
  rw [smallCommon, smallCommonRightMagnitude]
  have hcard : (Ico W.q (m - 1)).card = m - 1 - W.q := Nat.card_Ico _ _
  simp_rw [show ∀ n : Nat, y - W.rootAt n = -(W.rootAt n - y) by intro n; ring]
  rw [Finset.prod_neg, hcard]

/-- The sign-free common factor is strictly positive at each selected right
point of a supported small window. -/
theorem smallCommonRightMagnitude_pos_at_rightPoint (W : OneFanWindow D)
    (hside : W.side = .right) (hq : W.q ≤ m - 1)
    (hsupp : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      W.rows W.cols) (p : Fin W.q) :
    0 < W.smallCommonRightMagnitude (W.rightPoints p) := by
  have hm := D.hm
  have hqpos : 0 < W.q := Nat.zero_lt_of_lt p.isLt
  have hlast := (W.right_diagonalSupported_iff hside hqpos).mp hsupp
  rw [smallCommonRightMagnitude]
  apply Finset.prod_pos
  intro n hn
  have hn' := Finset.mem_Ico.mp hn
  let j : Fin m := ⟨W.c + (p : Nat), by
    have := W.cq_le
    have := p.isLt
    omega⟩
  have hroot : W.rho + n < 4 * m - 2 := by
    have hrows := W.rows_le
    omega
  rw [W.rootAt_eq_openKnot n hroot]
  change 0 < D.openKnot ⟨W.rho + n, hroot⟩ - D.u j
  apply sub_pos.mpr
  change D.z (D.beta j) < D.openKnot ⟨W.rho + n, hroot⟩
  apply D.z_lt_openKnot_of_mergeOpenIndex_lt
  have hlastGrow : (D.beta j : Nat) ≤ (D.beta (W.lastLabel hqpos) : Nat) := by
    apply D.beta_strictMono.monotone
    change W.c + (p : Nat) ≤ W.c + W.q - 1
    have := p.isLt
    omega
  have hlast' : m + (D.beta (W.lastLabel hqpos) : Nat) ≤ W.rho + W.q := by
    exact Nat.sub_le_iff_le_add.mp hlast
  change m - 1 + (D.beta j : Nat) < W.rho + n
  omega

/-- Matrix form of the full sliding decomposition at the selected right
points. -/
theorem fullSlidingMatrix_eq_smallCommon_mul_evalMatrix_right
    (W : OneFanWindow D) (hq : W.q ≤ m - 1) :
    Matrix.of (fun v p ↦ fullSlidingAt D (W.rows v) (W.rightPoints p)) =
      Matrix.of (fun v p ↦ W.smallCommon (W.rightPoints p) *
        OddSlidingRootBasis.evalMatrix W.q W.smallA W.smallB W.rightPoints v p) := by
  ext v p
  have h := W.fullSlidingAt_eq_smallCommon_mul_evalMatrix_entry hq v
    (W.rightPoints p)
  simpa [OddSlidingRootBasis.evalMatrix] using h

/-- The scalar multiplying a right evaluation column after both mask removal
and common-factor extraction. -/
def rightScale (W : OneFanWindow D) (p : Fin W.q) : ℝ :=
  (-1 : ℝ) ^ (m - 2) * W.smallCommon (W.rightPoints p)

/-- The product of the right column scalars has no residual sign. -/
theorem rightScale_prod_eq_rightMagnitude_prod (W : OneFanWindow D)
    (hqpos : 0 < W.q) (hq : W.q ≤ m - 1) :
    (Finset.univ.prod W.rightScale) =
      Finset.univ.prod (fun p ↦ W.smallCommonRightMagnitude (W.rightPoints p)) := by
  let r : Nat := m - 1 - W.q
  have hm := D.hm
  have hd : m - 2 = (W.q - 1) + r := by
    dsimp [r]
    omega
  have hexp : (m - 2) * W.q + r * W.q =
      W.q * (W.q - 1) + 2 * (r * W.q) := by
    rw [hd]
    ring
  have heven : Even ((m - 2) * W.q + r * W.q) := by
    rw [hexp]
    exact (Nat.even_mul_pred_self W.q).add (even_two_mul _)
  have hsign : ((-1 : ℝ) ^ (m - 2)) ^ W.q * ((-1 : ℝ) ^ r) ^ W.q = 1 := by
    rw [← pow_mul, ← pow_mul, ← pow_add]
    exact heven.neg_one_pow
  change (Finset.univ.prod (fun p ↦
    ((-1 : ℝ) ^ (m - 2) * W.smallCommon (W.rightPoints p)))) = _
  rw [Finset.prod_mul_distrib]
  simp_rw [W.smallCommon_eq_negPow_mul_rightMagnitude hq]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [show m - 1 - W.q = r by rfl]
  rw [← mul_assoc, hsign, one_mul]

/-- Matrix form of the complete right small-window reduction: the raw block
is a column scaling of the positive sliding-root evaluation matrix. -/
theorem right_submatrix_eq_rightScale_mul_evalMatrix (W : OneFanWindow D)
    (hside : W.side = .right) (hq : W.q ≤ m - 1)
    (hsupp : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      W.rows W.cols) :
    (twoFanCoefficientMatrix D).submatrix W.rows W.cols =
      Matrix.of (fun v p ↦ W.rightScale p *
        OddSlidingRootBasis.evalMatrix W.q W.smallA W.smallB W.rightPoints v p) := by
  rw [W.right_submatrix_eq_negPow_fullSlidingMatrix hside hq hsupp]
  ext v p
  have h := W.fullSlidingAt_eq_smallCommon_mul_evalMatrix_entry hq v
    (W.rightPoints p)
  have h' : fullSlidingAt D (W.rows v) (W.rightPoints p) =
      W.smallCommon (W.rightPoints p) *
        OddSlidingRootBasis.evalMatrix W.q W.smallA W.smallB W.rightPoints v p := by
    simpa [OddSlidingRootBasis.evalMatrix] using h
  unfold rightScale
  simp only [Matrix.of_apply]
  rw [h']
  ring

/-- Strict positivity of every supported nonempty right-only solid minor of
order at most `m - 1`. -/
theorem right_minor_pos_of_small (W : OneFanWindow D)
    (hside : W.side = .right) (hqpos : 0 < W.q) (hq : W.q ≤ m - 1)
    (hsupp : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      W.rows W.cols) : 0 < W.minor := by
  unfold minor matrixMinor
  rw [W.right_submatrix_eq_rightScale_mul_evalMatrix hside hq hsupp,
    Matrix.det_mul_row, W.rightScale_prod_eq_rightMagnitude_prod hqpos hq]
  apply mul_pos
  · apply Finset.prod_pos
    intro p hp
    exact W.smallCommonRightMagnitude_pos_at_rightPoint hside hq hsupp p
  · apply OddSlidingRootBasis.det_evalMatrix_pos
    · intro i j hij hj
      exact W.smallA_lt_smallB hq i j hij hj
    · exact W.rightPoints_strictMono

/-- The unique supported full left-fan window. -/
def leftFullWindow (D : TwoFanData m) : OneFanWindow D where
  side := .left
  c := 0
  q := m
  rho := 0
  cq_le := by omega
  rows_le := by
    have hm := D.hm
    omega

/-- Its order-`m-1` Laplace cofactor window. -/
def leftFullCofactorWindow (D : TwoFanData m) : OneFanWindow D where
  side := .left
  c := 1
  q := m - 1
  rho := 1
  cq_le := by
    have hm := D.hm
    omega
  rows_le := by
    have hm := D.hm
    omega

/-- The unique supported full right-fan window. -/
def rightFullWindow (D : TwoFanData m) : OneFanWindow D where
  side := .right
  c := 0
  q := m
  rho := 2 * m - 1
  cq_le := by omega
  rows_le := by
    have hm := D.hm
    omega

/-- Its order-`m-1` Laplace cofactor window. -/
def rightFullCofactorWindow (D : TwoFanData m) : OneFanWindow D where
  side := .right
  c := 0
  q := m - 1
  rho := 2 * m - 1
  cq_le := by
    have hm := D.hm
    omega
  rows_le := by
    have hm := D.hm
    omega

/-- The left cofactor window is diagonally supported. -/
theorem leftFullCofactor_diagonalSupported (D : TwoFanData m) :
    DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      (leftFullCofactorWindow D).rows (leftFullCofactorWindow D).cols := by
  have hm := D.hm
  have hqpos : 0 < (leftFullCofactorWindow D).q := by
    change 0 < m - 1
    omega
  apply (left_diagonalSupported_iff (leftFullCofactorWindow D) rfl hqpos).mpr
  change 1 ≤ (D.alpha ⟨1, by omega⟩ : Nat)
  have hstrict : D.alpha ⟨0, by omega⟩ < D.alpha ⟨1, by omega⟩ := by
    apply D.alpha_strictMono
    change 0 < 1
    omega
  have hzero : (D.alpha ⟨0, by omega⟩ : Nat) = 0 := by
    simpa using congrArg Fin.val D.alpha_zero
  omega

/-- The right cofactor window is diagonally supported. -/
theorem rightFullCofactor_diagonalSupported (D : TwoFanData m) :
    DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      (rightFullCofactorWindow D).rows (rightFullCofactorWindow D).cols := by
  have hm := D.hm
  have hqpos : 0 < (rightFullCofactorWindow D).q := by
    change 0 < m - 1
    omega
  apply (right_diagonalSupported_iff (rightFullCofactorWindow D) rfl hqpos).mpr
  let j := (rightFullCofactorWindow D).lastLabel hqpos
  have hj : j < ⟨m - 1, by omega⟩ := by
    change 0 + (m - 1) - 1 < m - 1
    omega
  have hbeta : (D.beta j : Nat) < 2 * m - 1 := by
    have hstrict := D.beta_strictMono hj
    have hlast : (D.beta ⟨m - 1, by omega⟩ : Nat) = 2 * m - 1 := by
      simpa using congrArg Fin.val D.beta_last
    omega
  change m + (D.beta j : Nat) - (m - 1) ≤ 2 * m - 1
  omega



end OneFanWindow

end

end ColomboGeneralK2.Odd
