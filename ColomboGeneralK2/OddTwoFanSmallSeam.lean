import ColomboGeneralK2.OddTwoFanKnotOrder
import ColomboGeneralK2.OddTwoFanWindows
import ColomboGeneralK2.OddSlidingRootBasis

/-!
# Small two-fan seam

The small seam is the range in which the masked Marsden entries agree with
the full sliding-root evaluations.  This module will contain the resulting
strict positivity theorem for the raw two-fan coefficient matrix.
-/

open scoped BigOperators
open Finset Matrix Polynomial

namespace ColomboGeneralK2.Odd

noncomputable section

namespace FanMinorWindow

variable {m : Nat} {D : TwoFanData m}

/-- The open-knot entry at offset `k` from the first selected row.  The
fallback branch is irrelevant on every range used below; making the function
total keeps the root families accepted by the arbitrary-order algebraic
lemma. -/
def seamKnot (W : FanMinorWindow D) (k : Nat) : ℝ :=
  if hk : W.rho + k < 4 * m - 2 then
    D.openKnot ⟨W.rho + k, hk⟩
  else 0

/-- The early roots `T_{ρ+j}` in the sliding-root basis. -/
def seamA (W : FanMinorWindow D) (j : Nat) : ℝ := W.seamKnot j

/-- The late roots `T_{ρ+m-1+i}` in the sliding-root basis. -/
def seamB (W : FanMinorWindow D) (i : Nat) : ℝ := W.seamKnot (m - 1 + i)

/-- The full degree-`m - 2` sliding product in seam row `v`. -/
def seamSliding (W : FanMinorWindow D) (v : Fin W.q) (y : ℝ) : ℝ :=
  Finset.univ.prod (fun h : Fin (m - 2) ↦
    y - D.openKnot (D.slideIndex (W.fanRows v) h))

/-- The common factor of the full sliding products in a small seam. -/
def seamCommon (W : FanMinorWindow D) (hq : 0 < W.q) (y : ℝ) : ℝ :=
  Finset.univ.prod (fun h : Fin (m - 2) ↦
    if W.q - 1 ≤ (h : Nat) then
      y - D.openKnot (D.slideIndex
        ⟨W.rho, by
          have hrows := W.rows_le
          have hm := D.hm
          change 0 < W.ell + W.b at hq
          change W.rho + (W.ell + W.b) ≤ 3 * m - 1 at hrows
          omega⟩ h)
    else 1)

private theorem prod_fin_shift_eq_prod_Ico (d a : Nat) (f : Nat → ℝ) :
    (∏ h : Fin d, f (a + (h : Nat))) = ∏ k ∈ Ico a (a + d), f k := by
  rw [Finset.prod_fin_eq_prod_range]
  calc
    (∏ x ∈ range d, if h : x < d then f (a + x) else 1) =
        ∏ x ∈ range d, f (a + x) := by
      apply Finset.prod_congr rfl
      intro x hx
      simp [Finset.mem_range.mp hx]
    _ = _ := by
      rw [Finset.prod_Ico_eq_prod_range]
      simp

private theorem prod_fin_if_ge_eq_prod_Ico (d q : Nat) (f : Nat → ℝ) :
    (∏ h : Fin d, if q ≤ (h : Nat) then f h else 1) =
      ∏ h ∈ Ico q d, f h := by
  rw [Finset.prod_fin_eq_prod_range]
  calc
    (∏ x ∈ range d,
        if hx : x < d then (if q ≤ x then f x else 1) else 1) =
        ∏ x ∈ range d, if q ≤ x then f x else 1 := by
      apply Finset.prod_congr rfl
      intro x hx
      simp [Finset.mem_range.mp hx]
    _ = ∏ x ∈ (range d).filter (q ≤ ·), f x := by
      rw [Finset.prod_filter]
    _ = ∏ h ∈ Ico q d, f h := by
      apply Finset.prod_congr
      · ext x
        simp only [mem_filter, mem_range, mem_Ico]
        constructor <;> omega
      · intro x hx
        rfl

@[simp]
theorem seamKnot_slide (W : FanMinorWindow D) (v : Fin W.q)
    (h : Fin (m - 2)) :
    W.seamKnot ((v : Nat) + (h : Nat) + 1) =
      D.openKnot (D.slideIndex (W.fanRows v) h) := by
  unfold seamKnot
  have hv := v.isLt
  have hh := h.isLt
  have hrows := W.rows_le
  have hm := D.hm
  change (v : Nat) < W.ell + W.b at hv
  change W.rho + (W.ell + W.b) ≤ 3 * m - 1 at hrows
  rw [dif_pos (by
    omega)]
  congr 1
  apply Fin.ext
  change W.rho + ((v : Nat) + (h : Nat) + 1) =
    W.rho + (v : Nat) + (h : Nat) + 1
  omega

theorem seamSliding_eq_prod_Ico (W : FanMinorWindow D) (v : Fin W.q) (y : ℝ) :
    W.seamSliding v y =
      ∏ k ∈ Ico ((v : Nat) + 1) ((v : Nat) + 1 + (m - 2)),
        (y - W.seamKnot k) := by
  unfold seamSliding
  simp_rw [← W.seamKnot_slide v]
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (prod_fin_shift_eq_prod_Ico (m - 2) ((v : Nat) + 1)
      (fun k ↦ y - W.seamKnot k))

theorem seamCommon_eq_prod_Ico (W : FanMinorWindow D) (hq : 0 < W.q) (y : ℝ) :
    W.seamCommon hq y =
      ∏ h ∈ Ico (W.q - 1) (m - 2), (y - W.seamKnot (h + 1)) := by
  calc
    W.seamCommon hq y =
        ∏ h : Fin (m - 2),
          if W.q - 1 ≤ (h : Nat) then y - W.seamKnot ((h : Nat) + 1) else 1 := by
      unfold seamCommon
      apply Finset.prod_congr rfl
      intro h hh
      have heq : (W.q - 1 ≤ (h : Nat)) ↔ W.q ≤ (h : Nat) + 1 := by omega
      by_cases hge : W.q ≤ (h : Nat) + 1
      · rw [if_pos (heq.mpr hge), if_pos (heq.mpr hge)]
        congr 2
        have hrow : (⟨W.rho, by
            have hrows := W.rows_le
            have hm := D.hm
            change W.rho + (W.ell + W.b) ≤ 3 * m - 1 at hrows
            change 0 < W.ell + W.b at hq
            omega⟩ : Fin (3 * m - 1)) = W.fanRows ⟨0, hq⟩ := by
          apply Fin.ext
          rfl
        rw [hrow]
        simpa using (W.seamKnot_slide ⟨0, hq⟩ h).symm
      · have hn : ¬ W.q - 1 ≤ (h : Nat) := by omega
        rw [if_neg hn, if_neg hn]
    _ = _ := prod_fin_if_ge_eq_prod_Ico (m - 2) (W.q - 1)
      (fun h ↦ y - W.seamKnot (h + 1))

theorem seamCommon_eq_rootInterval (W : FanMinorWindow D) (hq : 0 < W.q)
    (y : ℝ) :
    W.seamCommon hq y =
      ∏ k ∈ Ico W.q (m - 1), (y - W.seamKnot k) := by
  rw [W.seamCommon_eq_prod_Ico hq]
  rw [Finset.prod_Ico_eq_prod_range, Finset.prod_Ico_eq_prod_range]
  have hm := D.hm
  have hq' : W.q - 1 + 1 = W.q := by omega
  have hcount : (m - 2) - (W.q - 1) = (m - 1) - W.q := by omega
  rw [hcount]
  apply Finset.prod_congr rfl
  intro k hk
  congr 2
  omega

theorem eval_slidingRoot_eq_rootIntervals (W : FanMinorWindow D)
    (v : Fin W.q) (y : ℝ) :
    (OddSlidingRootBasis.slidingRoot W.q W.seamA W.seamB v).eval y =
      (∏ k ∈ Ico (m - 1) (m - 1 + (v : Nat)), (y - W.seamKnot k)) *
        ∏ k ∈ Ico ((v : Nat) + 1) W.q, (y - W.seamKnot k) := by
  simp only [OddSlidingRootBasis.slidingRoot, eval_mul, eval_prod, eval_sub,
    eval_X, eval_C, seamA, seamB]
  have hcount : (m - 1 + (v : Nat)) - (m - 1) = (v : Nat) := by omega
  have hlate : (∏ x ∈ range (v : Nat),
      (y - W.seamKnot (m - 1 + x))) =
      ∏ k ∈ Ico (m - 1) (m - 1 + (v : Nat)),
        (y - W.seamKnot k) := by
    rw [Finset.prod_Ico_eq_prod_range, hcount]
  rw [hlate]

/-- The full degree-`m-2` product is the common tail times the genuine
order-`q` sliding-root polynomial. -/
theorem seamSliding_eq_common_mul_slidingRoot (W : FanMinorWindow D)
    (hq0 : 0 < W.q) (hq : W.q ≤ m - 1) (v : Fin W.q) (y : ℝ) :
    W.seamSliding v y = W.seamCommon hq0 y *
      (OddSlidingRootBasis.slidingRoot W.q W.seamA W.seamB v).eval y := by
  rw [W.seamSliding_eq_prod_Ico, W.seamCommon_eq_rootInterval hq0,
    W.eval_slidingRoot_eq_rootIntervals]
  have hvq : (v : Nat) + 1 ≤ W.q := by omega
  have hqm : W.q ≤ m - 1 := hq
  have hmmv : m - 1 ≤ m - 1 + (v : Nat) := by omega
  have hfirst := Finset.prod_Ico_consecutive (fun k ↦ y - W.seamKnot k) hvq hqm
  have hsecond := Finset.prod_Ico_consecutive (fun k ↦ y - W.seamKnot k)
    (show (v : Nat) + 1 ≤ m - 1 by omega) hmmv
  calc
    (∏ k ∈ Ico ((v : Nat) + 1) ((v : Nat) + 1 + (m - 2)),
        (y - W.seamKnot k)) =
        ∏ k ∈ Ico ((v : Nat) + 1) (m - 1 + (v : Nat)),
          (y - W.seamKnot k) := by
          congr 2
          have hm := D.hm
          omega
    _ = (∏ k ∈ Ico ((v : Nat) + 1) (m - 1),
          (y - W.seamKnot k)) *
          ∏ k ∈ Ico (m - 1) (m - 1 + (v : Nat)),
            (y - W.seamKnot k) := hsecond.symm
    _ = ((∏ k ∈ Ico ((v : Nat) + 1) W.q, (y - W.seamKnot k)) *
          ∏ k ∈ Ico W.q (m - 1), (y - W.seamKnot k)) *
          ∏ k ∈ Ico (m - 1) (m - 1 + (v : Nat)),
            (y - W.seamKnot k) := by rw [hfirst]
    _ = (∏ k ∈ Ico W.q (m - 1), (y - W.seamKnot k)) *
        ((∏ k ∈ Ico (m - 1) (m - 1 + (v : Nat)),
            (y - W.seamKnot k)) *
          ∏ k ∈ Ico ((v : Nat) + 1) W.q, (y - W.seamKnot k)) := by
          ring

/-- Every selected left entry, including a nominally masked one, is the
full sliding evaluation.  In the masked branch the merge rank itself occurs
among the sliding roots. -/
theorem raw_left_entry_eq_seamSliding (W : FanMinorWindow D)
    (hq : W.q ≤ m - 1)
    (hsupp : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      W.fanRows W.fanCols) (v : Fin W.q) (t : Fin W.ell) :
    twoFanCoefficientMatrix D (W.fanRows v) (W.fanCols (Fin.castAdd W.b t)) =
      W.seamSliding v
        (D.s ⟨m - W.ell + (t : Nat), by
          have := W.ell_le
          have := t.isLt
          omega⟩) := by
  rw [W.fanCols_left_eq t, twoFanCoefficientMatrix_left_apply]
  let j : Fin m := ⟨m - W.ell + (t : Nat), by
    have := W.ell_le
    have := t.isLt
    omega⟩
  change D.leftCoefficient (W.fanRows v) j = W.seamSliding v (D.s j)
  unfold TwoFanData.leftCoefficient
  by_cases hmask : (W.fanRows v : Nat) ≤ (D.alpha j : Nat)
  · rw [if_pos hmask]
    rfl
  · rw [if_neg hmask]
    symm
    unfold seamSliding
    have hdiag := (W.left_diagonal_supported_iff t).mp
      (hsupp (Fin.castAdd W.b t))
    have hv := v.isLt
    have ht := t.isLt
    have hm := D.hm
    have hq' : W.ell + W.b ≤ m - 1 := by simpa [q] using hq
    have hmask' : (D.alpha j : Nat) < W.rho + (v : Nat) := by
      simpa using Nat.lt_of_not_ge hmask
    have hstart : W.rho + (v : Nat) + 1 ≤
        m - 1 + (D.alpha j : Nat) := by
      change (v : Nat) < W.ell + W.b at hv
      change W.rho + (t : Nat) ≤ (D.alpha j : Nat) at hdiag
      omega
    have hend : m - 1 + (D.alpha j : Nat) <
        W.rho + (v : Nat) + 1 + (m - 2) := by omega
    let hroot : Fin (m - 2) :=
      ⟨m - 1 + (D.alpha j : Nat) - (W.rho + (v : Nat) + 1), by omega⟩
    apply Finset.prod_eq_zero (Finset.mem_univ hroot)
    apply sub_eq_zero.mpr
    rw [← D.openKnot_alpha j]
    congr 1
    apply Fin.ext
    dsimp only [TwoFanData.slideIndex, TwoFanData.mergeOpenIndex, hroot]
    change m - 1 + (D.alpha j : Nat) = W.rho + (v : Nat) +
      (m - 1 + (D.alpha j : Nat) - (W.rho + (v : Nat) + 1)) + 1
    omega

/-- Every selected right entry is `(-1)^(m-2)` times the full sliding
evaluation.  The masked branch again vanishes because its merge rank is a
literal sliding root. -/
theorem raw_right_entry_eq_seamSliding (W : FanMinorWindow D)
    (hq : W.q ≤ m - 1)
    (hsupp : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      W.fanRows W.fanCols) (v : Fin W.q) (t : Fin W.b) :
    twoFanCoefficientMatrix D (W.fanRows v) (W.fanCols (Fin.natAdd W.ell t)) =
      (-1 : ℝ) ^ (m - 2) * W.seamSliding v
        (D.u ⟨W.c + (t : Nat), by
          have := W.cb_le
          have := t.isLt
          omega⟩) := by
  rw [W.fanCols_right_eq t, twoFanCoefficientMatrix_right_apply]
  let j : Fin m := ⟨W.c + (t : Nat), by
    have := W.cb_le
    have := t.isLt
    omega⟩
  change D.rightCoefficient (W.fanRows v) j =
    (-1 : ℝ) ^ (m - 2) * W.seamSliding v (D.u j)
  unfold TwoFanData.rightCoefficient
  by_cases hmask : m - 1 + (D.beta j : Nat) ≤ (W.fanRows v : Nat)
  · rw [if_pos hmask]
    unfold seamSliding
    simp_rw [show ∀ h : Fin (m - 2),
      D.openKnot (D.slideIndex (W.fanRows v) h) - D.u j =
        -(D.u j - D.openKnot (D.slideIndex (W.fanRows v) h)) by
          intro h
          ring]
    rw [Finset.prod_neg]
    simp only [Finset.card_univ, Fintype.card_fin]
  · rw [if_neg hmask]
    symm
    rw [mul_eq_zero]
    right
    unfold seamSliding
    have hdiag := (W.right_diagonal_supported_iff t).mp
      (hsupp (Fin.natAdd W.ell t))
    have hv := v.isLt
    have ht := t.isLt
    have hm := D.hm
    have hq' : W.ell + W.b ≤ m - 1 := by simpa [q] using hq
    have hmask' : W.rho + (v : Nat) < m - 1 + (D.beta j : Nat) := by
      simpa using Nat.lt_of_not_ge hmask
    have hstart : W.rho + (v : Nat) + 1 ≤
        m - 1 + (D.beta j : Nat) := by omega
    have hend : m - 1 + (D.beta j : Nat) <
        W.rho + (v : Nat) + 1 + (m - 2) := by
      change m - 1 + (D.beta j : Nat) ≤ W.rho + W.ell + (t : Nat) at hdiag
      change (v : Nat) < W.ell + W.b at hv
      omega
    let hroot : Fin (m - 2) :=
      ⟨m - 1 + (D.beta j : Nat) - (W.rho + (v : Nat) + 1), by omega⟩
    apply Finset.prod_eq_zero (Finset.mem_univ hroot)
    apply sub_eq_zero.mpr
    rw [← D.openKnot_beta j]
    congr 1
    apply Fin.ext
    dsimp only [TwoFanData.slideIndex, TwoFanData.mergeOpenIndex, hroot]
    change m - 1 + (D.beta j : Nat) = W.rho + (v : Nat) +
      (m - 1 + (D.beta j : Nat) - (W.rho + (v : Nat) + 1)) + 1
    omega

/-- The selected points in the raw matrix's natural `[L,R]` column order. -/
def seamRawPoints (W : FanMinorWindow D) : Fin W.q → ℝ := fun t ↦
  if ht : (t : Nat) < W.ell then
    D.s ⟨m - W.ell + (t : Nat), by
      have := W.ell_le
      have := t.isLt
      omega⟩
  else
    D.u ⟨W.c + ((t : Nat) - W.ell), by
      have ht' := t.isLt
      change (t : Nat) < W.ell + W.b at ht'
      have hle : W.ell ≤ (t : Nat) := Nat.le_of_not_gt ht
      have := W.cb_le
      omega⟩

/-- Rotation which reads the raw `[L,R]` columns in right-first order. -/
def seamBlockRotate (W : FanMinorWindow D) : Equiv.Perm (Fin W.q) :=
  (finRotate W.q) ^ W.ell

private theorem finRotate_pow_apply_val {n : Nat} (k : Nat) (t : Fin n) :
    (((finRotate n) ^ k) t : Nat) = ((t : Nat) + k) % n := by
  induction k with
  | zero => simp [Nat.mod_eq_of_lt t.isLt]
  | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, finRotate_apply, Fin.val_add, ih]
      change (((t : Nat) + k) % n + 1 % n) % n =
        ((t : Nat) + (k + 1)) % n
      rw [← Nat.add_mod]
      congr 1

theorem seamBlockRotate_val (W : FanMinorWindow D) (_hq : 0 < W.q)
    (t : Fin W.q) :
    (W.seamBlockRotate t : Nat) = ((t : Nat) + W.ell) % W.q := by
  exact finRotate_pow_apply_val W.ell t

theorem seamBlockRotate_right (W : FanMinorWindow D) (hq : 0 < W.q)
    (t : Fin W.q) (ht : (t : Nat) < W.b) :
    W.seamBlockRotate t =
      Fin.natAdd W.ell ⟨(t : Nat), ht⟩ := by
  apply Fin.ext
  rw [W.seamBlockRotate_val hq]
  change ((t : Nat) + W.ell) % (W.ell + W.b) = W.ell + (t : Nat)
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem seamBlockRotate_left (W : FanMinorWindow D) (hq : 0 < W.q)
    (t : Fin W.q) (ht : W.b ≤ (t : Nat)) :
    W.seamBlockRotate t =
      Fin.castAdd W.b ⟨(t : Nat) - W.b, by
        have ht' := t.isLt
        change (t : Nat) < W.ell + W.b at ht'
        omega⟩ := by
  apply Fin.ext
  rw [W.seamBlockRotate_val hq]
  change ((t : Nat) + W.ell) % (W.ell + W.b) = (t : Nat) - W.b
  have heq : (t : Nat) + W.ell =
      (W.ell + W.b) + ((t : Nat) - W.b) := by omega
  rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt (by
    have ht' := t.isLt
    change (t : Nat) < W.ell + W.b at ht'
    omega)]

/-- The points in the increasing order used by the sliding-root determinant:
the selected right block followed by the selected left suffix. -/
def seamPoints (W : FanMinorWindow D) : Fin W.q → ℝ := fun t ↦
  if ht : (t : Nat) < W.b then
    D.u ⟨W.c + (t : Nat), by
      have := W.cb_le
      have := t.isLt
      omega⟩
  else
    D.s ⟨m - W.ell + ((t : Nat) - W.b), by
      have := W.ell_le
      have ht' := t.isLt
      have htb : W.b ≤ (t : Nat) := Nat.le_of_not_gt ht
      change (t : Nat) < W.ell + W.b at ht'
      omega⟩

/-- The block rotation really sends natural `[L,R]` point order to the
right-first point order. -/
theorem seamRawPoints_blockRotate (W : FanMinorWindow D) (hq : 0 < W.q)
    (t : Fin W.q) : W.seamRawPoints (W.seamBlockRotate t) = W.seamPoints t := by
  by_cases ht : (t : Nat) < W.b
  · rw [W.seamBlockRotate_right hq t ht]
    unfold seamRawPoints seamPoints
    simp only [dif_pos ht, Fin.val_natAdd]
    rw [dif_neg (by omega)]
    congr 2
    omega
  · have htb : W.b ≤ (t : Nat) := Nat.le_of_not_gt ht
    rw [W.seamBlockRotate_left hq t htb]
    unfold seamRawPoints seamPoints
    simp only [dif_neg ht, Fin.val_castAdd]
    rw [dif_pos (by
      have ht' := t.isLt
      change (t : Nat) < W.ell + W.b at ht'
      omega)]

/-- The sign of the block rotation, recorded in the real coefficient ring. -/
theorem seamBlockRotate_sign (W : FanMinorWindow D) :
    ((Equiv.Perm.sign W.seamBlockRotate : ℤˣ) : ℝ) =
      (-1 : ℝ) ^ ((W.q - 1) * W.ell) := by
  unfold seamBlockRotate
  rw [map_pow, sign_finRotate]
  simp
  rw [pow_mul]

/-- On the nonempty small seam the final selected right knot precedes the
first selected left knot in the merged order. -/
theorem lastRight_rank_lt_firstLeft_rank (W : FanMinorWindow D)
    (hell : 0 < W.ell) (hb : 0 < W.b) (hq : W.q ≤ m - 1)
    (hsupp : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      W.fanRows W.fanCols) :
    (D.beta (W.lastRight hb) : Nat) < (D.alpha (W.firstLeft hell) : Nat) := by
  have hwindow := (W.fanMinor_diagonalSupported_iff hell hb).mp hsupp
  have hlower := hwindow.1
  have hupper := hwindow.2
  unfold lower at hlower
  unfold upper at hupper
  have hq' : W.ell + W.b ≤ m - 1 := by simpa [q] using hq
  have hm := D.hm
  omega

/-- The determinant-point order: selected right knots first, then selected
left knots.  This is precisely the order required by the positive
Vandermonde factor in `OddSlidingRootBasis`. -/
theorem seamPoints_strictMono (W : FanMinorWindow D)
    (hell : 0 < W.ell) (hb : 0 < W.b) (hq : W.q ≤ m - 1)
    (hsupp : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      W.fanRows W.fanCols) : StrictMono W.seamPoints := by
  intro x y hxy
  unfold seamPoints
  by_cases hx : (x : Nat) < W.b
  · by_cases hy : (y : Nat) < W.b
    · simp only [dif_pos hx, dif_pos hy]
      apply D.u_strictMono
      change W.c + (x : Nat) < W.c + (y : Nat)
      exact Nat.add_lt_add_left hxy _
    · simp only [dif_pos hx, dif_neg hy]
      change D.z (D.beta ⟨W.c + (x : Nat), _⟩) <
        D.z (D.alpha ⟨m - W.ell + ((y : Nat) - W.b), _⟩)
      apply D.z_strict
      have hlast := W.lastRight_rank_lt_firstLeft_rank hell hb hq hsupp
      have hright :
          (D.beta ⟨W.c + (x : Nat), by
            have := W.cb_le
            have := x.isLt
            omega⟩ : Nat) ≤ (D.beta (W.lastRight hb) : Nat) := by
        apply D.beta_strictMono.monotone
        change W.c + (x : Nat) ≤ W.c + W.b - 1
        have := x.isLt
        omega
      have hleft : (D.alpha (W.firstLeft hell) : Nat) ≤
          (D.alpha ⟨m - W.ell + ((y : Nat) - W.b), by
            have := W.ell_le
            have hy' := y.isLt
            have hyb : W.b ≤ (y : Nat) := Nat.le_of_not_gt hy
            change (y : Nat) < W.ell + W.b at hy'
            omega⟩ : Nat) := by
        apply D.alpha_strictMono.monotone
        change m - W.ell ≤ m - W.ell + ((y : Nat) - W.b)
        omega
      exact lt_of_le_of_lt hright (lt_of_lt_of_le hlast hleft)
  · have hy : ¬ (y : Nat) < W.b := by
      intro hy
      exact hx (lt_trans hxy hy)
    simp only [dif_neg hx, dif_neg hy]
    apply D.s_strictMono
    change m - W.ell + ((x : Nat) - W.b) <
      m - W.ell + ((y : Nat) - W.b)
    have hxb : W.b ≤ (x : Nat) := Nat.le_of_not_gt hx
    exact Nat.add_lt_add_left (Nat.sub_lt_sub_right hxb hxy) _

/-- The open vector is strictly increasing between an entry before the
right anchor and a later entry after the repeated left-anchor block.  These
are exactly the positions occupied by the early and late seam roots. -/
theorem openKnot_lt_openKnot_of_lt (D : TwoFanData m)
    (a b : Fin (4 * m - 2)) (hab : a < b)
    (ha : (a : Nat) < 3 * m - 1) (hb : m - 1 ≤ (b : Nat)) :
    D.openKnot a < D.openKnot b := by
  unfold TwoFanData.openKnot
  by_cases hA : (a : Nat) < m - 1
  · simp only [dif_pos hA]
    have hnotB : ¬ (b : Nat) < m - 1 := by omega
    simp only [dif_neg hnotB]
    by_cases hBZ : (b : Nat) < 3 * m - 1
    · simp only [dif_pos hBZ]
      exact D.leftAnchor_lt _
    · simp only [dif_neg hBZ]
      let z0 : Fin (2 * m) := ⟨0, by have hm := D.hm; omega⟩
      exact lt_trans (D.leftAnchor_lt z0) (D.lt_rightAnchor z0)
  · simp only [dif_neg hA, dif_pos ha]
    have hnotB : ¬ (b : Nat) < m - 1 := by omega
    simp only [dif_neg hnotB]
    by_cases hBZ : (b : Nat) < 3 * m - 1
    · simp only [dif_pos hBZ]
      apply D.z_strict
      change (a : Nat) - (m - 1) < (b : Nat) - (m - 1)
      omega
    · simp only [dif_neg hBZ]
      exact D.lt_rightAnchor _

/-- Strict cross ordering of the early and late roots used by the
arbitrary-order sliding determinant. -/
theorem seamA_lt_seamB (W : FanMinorWindow D) (hq : W.q ≤ m - 1) :
    ∀ i j : Nat, i < j → j < W.q → W.seamA j < W.seamB i := by
  intro i j hij hjq
  unfold seamA seamB seamKnot
  have hrows := W.rows_le
  have hm := D.hm
  change W.rho + (W.ell + W.b) ≤ 3 * m - 1 at hrows
  have hjq' : j < W.ell + W.b := by simpa [q] using hjq
  have hiq : i < W.ell + W.b := lt_trans hij hjq'
  rw [dif_pos (by omega), dif_pos (by omega)]
  apply openKnot_lt_openKnot_of_lt D
  · change W.rho + j < W.rho + (m - 1 + i)
    omega
  · change W.rho + j < 3 * m - 1
    omega
  · change m - 1 ≤ W.rho + (m - 1 + i)
    omega

/-- The genuine order-`q` sliding-root evaluation determinant at the
right-first seam points is strictly positive. -/
theorem seamEvalMatrix_det_pos (W : FanMinorWindow D)
    (hell : 0 < W.ell) (hb : 0 < W.b) (hq : W.q ≤ m - 1)
    (hsupp : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      W.fanRows W.fanCols) :
    0 < (OddSlidingRootBasis.evalMatrix W.q W.seamA W.seamB W.seamPoints).det := by
  exact OddSlidingRootBasis.det_evalMatrix_pos W.q W.seamA W.seamB W.seamPoints
    (W.seamA_lt_seamB hq) (W.seamPoints_strictMono hell hb hq hsupp)

/-- The common right-column factors with their positive orientation. -/
def seamRightCommon (W : FanMinorWindow D) (_hq : 0 < W.q) (y : ℝ) : ℝ :=
  ∏ h : Fin (m - 2),
    if W.q - 1 ≤ (h : Nat) then W.seamKnot ((h : Nat) + 1) - y else 1

theorem seamRightCommon_eq_prod_Ico (W : FanMinorWindow D)
    (hq : 0 < W.q) (y : ℝ) :
    W.seamRightCommon hq y =
      ∏ h ∈ Ico (W.q - 1) (m - 2), (W.seamKnot (h + 1) - y) := by
  unfold seamRightCommon
  simpa using prod_fin_if_ge_eq_prod_Ico (m - 2) (W.q - 1)
    (fun h ↦ W.seamKnot (h + 1) - y)

/-- On a selected left point, every common factor has positive sign. -/
theorem seamCommon_left_pos (W : FanMinorWindow D) (hq0 : 0 < W.q)
    (hsupp : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      W.fanRows W.fanCols) (t : Fin W.ell) :
    0 < W.seamCommon hq0
      (D.s ⟨m - W.ell + (t : Nat), by
        have := W.ell_le
        have := t.isLt
        omega⟩) := by
  let j : Fin m := ⟨m - W.ell + (t : Nat), by
    have := W.ell_le
    have := t.isLt
    omega⟩
  change 0 < W.seamCommon hq0 (D.s j)
  rw [W.seamCommon_eq_prod_Ico hq0]
  apply Finset.prod_pos
  intro h hh
  rw [sub_pos]
  unfold seamKnot
  have hdiag := (W.left_diagonal_supported_iff t).mp
    (hsupp (Fin.castAdd W.b t))
  have hh' := (Finset.mem_Ico.mp hh).2
  have hm := D.hm
  rw [dif_pos (by
    have hrows := W.rows_le
    omega)]
  change D.openKnot _ < D.z (D.alpha j)
  apply D.openKnot_lt_z_of_lt_mergeOpenIndex
  change W.rho + (h + 1) < m - 1 + (D.alpha j : Nat)
  change W.rho + (t : Nat) ≤ (D.alpha j : Nat) at hdiag
  omega

/-- On a selected right point, the reversed common factors are positive. -/
theorem seamRightCommon_pos (W : FanMinorWindow D) (hq0 : 0 < W.q)
    (hsupp : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      W.fanRows W.fanCols) (t : Fin W.b) :
    0 < W.seamRightCommon hq0
      (D.u ⟨W.c + (t : Nat), by
        have := W.cb_le
        have := t.isLt
        omega⟩) := by
  let j : Fin m := ⟨W.c + (t : Nat), by
    have := W.cb_le
    have := t.isLt
    omega⟩
  change 0 < W.seamRightCommon hq0 (D.u j)
  rw [W.seamRightCommon_eq_prod_Ico hq0]
  apply Finset.prod_pos
  intro h hh
  rw [sub_pos]
  unfold seamKnot
  have hdiag := (W.right_diagonal_supported_iff t).mp
    (hsupp (Fin.natAdd W.ell t))
  have hhlo := (Finset.mem_Ico.mp hh).1
  have hhhi := (Finset.mem_Ico.mp hh).2
  have hm := D.hm
  rw [dif_pos (by
    have hrows := W.rows_le
    omega)]
  change D.z (D.beta j) < D.openKnot _
  apply D.z_lt_openKnot_of_mergeOpenIndex_lt
  change m - 1 + (D.beta j : Nat) < W.rho + (h + 1)
  change m - 1 + (D.beta j : Nat) ≤ W.rho + W.ell + (t : Nat) at hdiag
  change W.q - 1 ≤ h at hhlo
  have ht := t.isLt
  have hqeq : W.q = W.ell + W.b := rfl
  omega

/-- Reversing all common right factors contributes exactly their count. -/
theorem seamCommon_eq_negOnePow_mul_rightCommon (W : FanMinorWindow D)
    (hq0 : 0 < W.q) (_hq : W.q ≤ m - 1) (y : ℝ) :
    W.seamCommon hq0 y = (-1 : ℝ) ^ (m - W.q - 1) *
      W.seamRightCommon hq0 y := by
  rw [W.seamCommon_eq_prod_Ico hq0, W.seamRightCommon_eq_prod_Ico hq0]
  simp_rw [show ∀ h : Nat, y - W.seamKnot (h + 1) =
      -(W.seamKnot (h + 1) - y) by intro h; ring]
  rw [Finset.prod_neg]
  simp only [Nat.card_Ico]
  have hm := D.hm
  have hcount : (m - 2) - (W.q - 1) = m - W.q - 1 := by omega
  rw [hcount]

/-- Column scalars after the raw columns are block-rotated right-first. -/
def seamColumnScale (W : FanMinorWindow D) (hq : 0 < W.q) (t : Fin W.q) : ℝ :=
  if (t : Nat) < W.b then
    (-1 : ℝ) ^ (m - 2) * W.seamCommon hq (W.seamPoints t)
  else W.seamCommon hq (W.seamPoints t)

/-- The same scalars with every factor oriented positively. -/
def seamPositiveScale (W : FanMinorWindow D) (hq : 0 < W.q)
    (t : Fin W.q) : ℝ :=
  if (t : Nat) < W.b then W.seamRightCommon hq (W.seamPoints t)
  else W.seamCommon hq (W.seamPoints t)

theorem seamColumnScale_eq_sign_mul_positive (W : FanMinorWindow D)
    (hq0 : 0 < W.q) (hq : W.q ≤ m - 1) (t : Fin W.q) :
    W.seamColumnScale hq0 t =
      (if (t : Nat) < W.b then (-1 : ℝ) ^ (W.q - 1) else 1) *
        W.seamPositiveScale hq0 t := by
  unfold seamColumnScale seamPositiveScale
  by_cases ht : (t : Nat) < W.b
  · simp only [if_pos ht]
    rw [W.seamCommon_eq_negOnePow_mul_rightCommon hq0 hq]
    have hsign : (-1 : ℝ) ^ (m - 2) * (-1 : ℝ) ^ (m - W.q - 1) =
        (-1 : ℝ) ^ (W.q - 1) := by
      rw [← pow_add]
      have hexp : (m - 2) + (m - W.q - 1) =
          (W.q - 1) + 2 * (m - W.q - 1) := by
        have hm := D.hm
        omega
      rw [hexp, pow_add, pow_mul]
      norm_num
    calc
      (-1 : ℝ) ^ (m - 2) *
          ((-1 : ℝ) ^ (m - W.q - 1) * W.seamRightCommon hq0 (W.seamPoints t)) =
          ((-1 : ℝ) ^ (m - 2) * (-1 : ℝ) ^ (m - W.q - 1)) *
            W.seamRightCommon hq0 (W.seamPoints t) := by ring
      _ = _ := by rw [hsign]
  · simp [ht]

theorem seamPositiveScale_pos (W : FanMinorWindow D)
    (hq0 : 0 < W.q)
    (hsupp : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      W.fanRows W.fanCols) (t : Fin W.q) :
    0 < W.seamPositiveScale hq0 t := by
  unfold seamPositiveScale
  by_cases ht : (t : Nat) < W.b
  · simp only [if_pos ht]
    have hpoint : W.seamPoints t =
        D.u ⟨W.c + (t : Nat), by
          have := W.cb_le
          omega⟩ := by
      simp [seamPoints, ht]
    rw [hpoint]
    simpa using W.seamRightCommon_pos hq0 hsupp ⟨(t : Nat), ht⟩
  · simp only [if_neg ht]
    let s : Fin W.ell := ⟨(t : Nat) - W.b, by
        have ht' := t.isLt
        have htb : W.b ≤ (t : Nat) := Nat.le_of_not_gt ht
        change (t : Nat) < W.ell + W.b at ht'
        omega⟩
    have hpoint : W.seamPoints t =
        D.s ⟨m - W.ell + (s : Nat), by
          have := W.ell_le
          have := s.isLt
          omega⟩ := by
      unfold seamPoints
      rw [dif_neg ht]
    rw [hpoint]
    exact W.seamCommon_left_pos hq0 hsupp s

/-- The raw selected coefficient matrix before taking its determinant. -/
def seamRawMatrix (W : FanMinorWindow D) : Matrix (Fin W.q) (Fin W.q) ℝ :=
  (twoFanCoefficientMatrix D).submatrix W.fanRows W.fanCols

/-- After block rotation, every raw column is its common scalar times the
corresponding arbitrary-order sliding-root evaluation column. -/
theorem seamRawMatrix_rotated_eq_scaledEval (W : FanMinorWindow D)
    (hell : 0 < W.ell) (hb : 0 < W.b) (hq : W.q ≤ m - 1)
    (hsupp : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      W.fanRows W.fanCols) :
    W.seamRawMatrix.submatrix id W.seamBlockRotate =
      Matrix.of (fun v t ↦ W.seamColumnScale (by unfold q; omega) t *
        OddSlidingRootBasis.evalMatrix W.q W.seamA W.seamB W.seamPoints v t) := by
  have hq0 : 0 < W.q := by unfold q; omega
  ext v t
  simp only [Matrix.submatrix_apply, id_eq, seamRawMatrix, Matrix.of_apply]
  by_cases ht : (t : Nat) < W.b
  · rw [W.seamBlockRotate_right hq0 t ht]
    let r : Fin W.b := ⟨(t : Nat), ht⟩
    rw [W.raw_right_entry_eq_seamSliding hq hsupp v r]
    have hpoint : D.u ⟨W.c + (r : Nat), by
        have := W.cb_le
        have := r.isLt
        omega⟩ = W.seamPoints t := by
      unfold seamPoints
      rw [dif_pos ht]
    rw [W.seamSliding_eq_common_mul_slidingRoot hq0 hq]
    rw [hpoint]
    unfold seamColumnScale OddSlidingRootBasis.evalMatrix
    simp only [if_pos ht, Matrix.of_apply]
    ring
  · have htb : W.b ≤ (t : Nat) := Nat.le_of_not_gt ht
    rw [W.seamBlockRotate_left hq0 t htb]
    let l : Fin W.ell := ⟨(t : Nat) - W.b, by
      have ht' := t.isLt
      change (t : Nat) < W.ell + W.b at ht'
      omega⟩
    rw [W.raw_left_entry_eq_seamSliding hq hsupp v l]
    rw [W.seamSliding_eq_common_mul_slidingRoot hq0 hq]
    have hpoint : D.s ⟨m - W.ell + (l : Nat), by
        have := W.ell_le
        have := l.isLt
        omega⟩ = W.seamPoints t := by
      unfold seamPoints
      rw [dif_neg ht]
    rw [hpoint]
    unfold seamColumnScale OddSlidingRootBasis.evalMatrix
    simp only [if_neg ht, Matrix.of_apply]

private theorem prod_fin_if_lt_const {q b : Nat} (hbq : b ≤ q) (a : ℝ) :
    (∏ t : Fin q, if (t : Nat) < b then a else 1) = a ^ b := by
  rw [← Finset.prod_filter]
  rw [Finset.prod_const]
  congr 1
  rw [Fin.card_filter_val_lt, Nat.min_eq_right hbq]

/-- Product of the rotated column scalars, with the `b(q-1)` right-column
sign recorded explicitly. -/
theorem prod_seamColumnScale (W : FanMinorWindow D)
    (hq0 : 0 < W.q) (hq : W.q ≤ m - 1) :
    (∏ t : Fin W.q, W.seamColumnScale hq0 t) =
      (-1 : ℝ) ^ (W.b * (W.q - 1)) *
        ∏ t : Fin W.q, W.seamPositiveScale hq0 t := by
  calc
    (∏ t : Fin W.q, W.seamColumnScale hq0 t) =
        ∏ t : Fin W.q,
          ((if (t : Nat) < W.b then (-1 : ℝ) ^ (W.q - 1) else 1) *
            W.seamPositiveScale hq0 t) := by
              apply Finset.prod_congr rfl
              intro t ht
              exact W.seamColumnScale_eq_sign_mul_positive hq0 hq t
    _ = (∏ t : Fin W.q,
          if (t : Nat) < W.b then (-1 : ℝ) ^ (W.q - 1) else 1) *
          ∏ t : Fin W.q, W.seamPositiveScale hq0 t := by
            rw [Finset.prod_mul_distrib]
    _ = ((-1 : ℝ) ^ (W.q - 1)) ^ W.b *
          ∏ t : Fin W.q, W.seamPositiveScale hq0 t := by
            rw [prod_fin_if_lt_const (show W.b ≤ W.q by unfold q; omega)]
    _ = _ := by rw [← pow_mul, Nat.mul_comm]

/-- The block-rotation sign cancels the accumulated right-column sign. -/
theorem signed_prod_seamColumnScale (W : FanMinorWindow D)
    (hq0 : 0 < W.q) (hq : W.q ≤ m - 1) :
    ((Equiv.Perm.sign W.seamBlockRotate : ℤˣ) : ℝ) *
        (∏ t : Fin W.q, W.seamColumnScale hq0 t) =
      ∏ t : Fin W.q, W.seamPositiveScale hq0 t := by
  rw [W.seamBlockRotate_sign, W.prod_seamColumnScale hq0 hq]
  rw [← mul_assoc, ← pow_add]
  have hexp : (W.q - 1) * W.ell + W.b * (W.q - 1) =
      (W.q - 1) * W.q := by
    change 0 < W.ell + W.b at hq0
    change (W.ell + W.b - 1) * W.ell + W.b * (W.ell + W.b - 1) =
      (W.ell + W.b - 1) * (W.ell + W.b)
    ring
  rw [hexp, (by
    have heven : Even ((W.q - 1) * W.q) := by
      rw [Nat.mul_comm]
      exact Nat.even_mul_pred_self W.q
    exact heven.neg_one_pow : (-1 : ℝ) ^ ((W.q - 1) * W.q) = 1), one_mul]

/-- Strict positivity of every supported genuine two-sided small seam. -/
theorem fanMinor_pos_of_diagonalSupported_small (W : FanMinorWindow D)
    (hell : 0 < W.ell) (hb : 0 < W.b) (hq : W.q ≤ m - 1)
    (hsupp : DiagonalSupported (twoFanCoefficientMatrix_intervalSupport D)
      W.fanRows W.fanCols) :
    0 < W.fanMinor := by
  have hq0 : 0 < W.q := by unfold q; omega
  let E := OddSlidingRootBasis.evalMatrix W.q W.seamA W.seamB W.seamPoints
  let M := W.seamRawMatrix
  let s : ℝ := ((Equiv.Perm.sign W.seamBlockRotate : ℤˣ) : ℝ)
  have hmatrix := W.seamRawMatrix_rotated_eq_scaledEval hell hb hq hsupp
  have hrot : (M.submatrix id W.seamBlockRotate).det =
      (∏ t : Fin W.q, W.seamColumnScale hq0 t) * E.det := by
    rw [hmatrix, Matrix.det_mul_row]
  have hperm : (M.submatrix id W.seamBlockRotate).det = s * M.det := by
    exact Matrix.det_permute' W.seamBlockRotate M
  have hsquare : s * s = 1 := by
    dsimp only [s]
    rw [W.seamBlockRotate_sign, ← pow_add]
    exact (Even.add_self ((W.q - 1) * W.ell)).neg_one_pow
  have hdet : M.det =
      (s * ∏ t : Fin W.q, W.seamColumnScale hq0 t) * E.det := by
    calc
      M.det = 1 * M.det := by ring
      _ = (s * s) * M.det := by rw [hsquare]
      _ = s * (s * M.det) := by ring
      _ = s * (M.submatrix id W.seamBlockRotate).det := by rw [hperm]
      _ = s * ((∏ t : Fin W.q, W.seamColumnScale hq0 t) * E.det) := by
        rw [hrot]
      _ = (s * ∏ t : Fin W.q, W.seamColumnScale hq0 t) * E.det := by ring
  have hscale : 0 < s * ∏ t : Fin W.q, W.seamColumnScale hq0 t := by
    rw [W.signed_prod_seamColumnScale hq0 hq]
    apply Finset.prod_pos
    intro t ht
    exact W.seamPositiveScale_pos hq0 hsupp t
  have heval : 0 < E.det := by
    exact W.seamEvalMatrix_det_pos hell hb hq hsupp
  unfold fanMinor
  change 0 < M.det
  rw [hdet]
  exact mul_pos hscale heval

end FanMinorWindow

end

end ColomboGeneralK2.Odd
