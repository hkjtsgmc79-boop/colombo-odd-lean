import ColomboGeneralK2.OddStaircaseSupport

/-!
# Raw two-fan data and coefficient matrix

This is the paper-facing data layer for the critical degree `m - 2`.
`DyckMerge` retains the *labelled* merge ranks of the two strictly ordered
families; the actual knot values live in a strictly increasing merged list.
The coefficient matrix below is the raw (unnormalized) Marsden coefficient
matrix from (C-left)--(C-right) of the odd-branch paper.

The dimension restriction is `2 ≤ m`: it makes the degree `m - 2` and the
open-vector indexing uniform, including the degree-zero case.
-/

open scoped BigOperators

namespace ColomboGeneralK2.Odd

noncomputable section

/-- A labelled Dyck merge: each family is increasing in its own label and
the left occurrence precedes the right occurrence with the same label. -/
structure DyckMerge (m : Nat) where
  rank : Fin m ⊕ Fin m ≃ Fin (2 * m)
  left_strict : StrictMono (fun j : Fin m ↦ rank (Sum.inl j))
  right_strict : StrictMono (fun j : Fin m ↦ rank (Sum.inr j))
  paired : ∀ j : Fin m, rank (Sum.inl j) < rank (Sum.inr j)

/-- A two-fan configuration at the critical degree.  The anchors are outside
the full merged knot list; sampling points are deliberately absent here,
since they belong to the later Marsden collocation layer. -/
structure TwoFanData (m : Nat) where
  hm : 2 ≤ m
  merge : DyckMerge m
  z : Fin (2 * m) → ℝ
  z_strict : StrictMono z
  leftAnchor : ℝ
  rightAnchor : ℝ
  leftAnchor_lt : ∀ q, leftAnchor < z q
  lt_rightAnchor : ∀ q, z q < rightAnchor

/-- The zero-based merge rank of the `j`th left knot. -/
def TwoFanData.alpha {m : Nat} (D : TwoFanData m) (j : Fin m) : Fin (2 * m) :=
  D.merge.rank (Sum.inl j)

/-- The zero-based merge rank of the `j`th right knot. -/
def TwoFanData.beta {m : Nat} (D : TwoFanData m) (j : Fin m) : Fin (2 * m) :=
  D.merge.rank (Sum.inr j)

/-- The labelled left knots, read from the merged list. -/
def TwoFanData.s {m : Nat} (D : TwoFanData m) (j : Fin m) : ℝ :=
  D.z (D.alpha j)

/-- The labelled right knots, read from the merged list. -/
def TwoFanData.u {m : Nat} (D : TwoFanData m) (j : Fin m) : ℝ :=
  D.z (D.beta j)

/-- The natural all-left-then-all-right column enumeration. -/
def twoFanColumnEquiv (m : Nat) : Fin m ⊕ Fin m ≃ Fin (2 * m) :=
  finSumFinEquiv.trans (finCongr (by omega))

/-- The open fine vector
`(A^(m-1), z_0, ..., z_(2m-1), B^(m-1))`. -/
def TwoFanData.openKnot {m : Nat} (D : TwoFanData m) :
    Fin (4 * m - 2) → ℝ := fun i ↦
  if hA : (i : Nat) < m - 1 then D.leftAnchor
  else if hZ : (i : Nat) < 3 * m - 1 then
    D.z ⟨(i : Nat) - (m - 1), by
      have hi := i.isLt
      omega⟩
  else D.rightAnchor

/-- A sliding root index in the open fine knot vector. -/
def TwoFanData.slideIndex {m : Nat} (D : TwoFanData m)
    (i : Fin (3 * m - 1)) (h : Fin (m - 2)) : Fin (4 * m - 2) :=
  ⟨(i : Nat) + (h : Nat) + 1, by
    have hi := i.isLt
    have hh := h.isLt
    have hm := D.hm
    omega⟩

/-- The raw left Marsden coefficient in (C-left). -/
def TwoFanData.leftCoefficient {m : Nat} (D : TwoFanData m)
    (i : Fin (3 * m - 1)) (j : Fin m) : ℝ :=
  if (i : Nat) ≤ (D.alpha j : Nat) then
    Finset.univ.prod (fun h : Fin (m - 2) ↦
      D.s j - D.openKnot (D.slideIndex i h))
  else 0

/-- The raw right Marsden coefficient in (C-right). -/
def TwoFanData.rightCoefficient {m : Nat} (D : TwoFanData m)
    (i : Fin (3 * m - 1)) (j : Fin m) : ℝ :=
  if m - 1 + (D.beta j : Nat) ≤ (i : Nat) then
    Finset.univ.prod (fun h : Fin (m - 2) ↦
      D.openKnot (D.slideIndex i h) - D.u j)
  else 0

/-- The paper's raw two-fan coefficient matrix, in natural `[L | R]` column
order and with `3m-1` rows. -/
def twoFanCoefficientMatrix {m : Nat} (D : TwoFanData m) :
    Matrix (Fin (3 * m - 1)) (Fin (2 * m)) ℝ := fun i col ↦
  match (twoFanColumnEquiv m).symm col with
  | Sum.inl j => D.leftCoefficient i j
  | Sum.inr j => D.rightCoefficient i j

/-- The two occurrences carrying one label occur in the Dyck order. -/
theorem TwoFanData.alpha_lt_beta {m : Nat} (D : TwoFanData m) (j : Fin m) :
    D.alpha j < D.beta j :=
  D.merge.paired j

/-- Merge ranks are strictly increasing within the left family. -/
theorem TwoFanData.alpha_strictMono {m : Nat} (D : TwoFanData m) :
    StrictMono D.alpha :=
  D.merge.left_strict

/-- Merge ranks are strictly increasing within the right family. -/
theorem TwoFanData.beta_strictMono {m : Nat} (D : TwoFanData m) :
    StrictMono D.beta :=
  D.merge.right_strict

/-- The labelled left knots are strictly increasing. -/
theorem TwoFanData.s_strictMono {m : Nat} (D : TwoFanData m) :
    StrictMono D.s := by
  intro a b hab
  exact D.z_strict (D.alpha_strictMono hab)

/-- The labelled right knots are strictly increasing. -/
theorem TwoFanData.u_strictMono {m : Nat} (D : TwoFanData m) :
    StrictMono D.u := by
  intro a b hab
  exact D.z_strict (D.beta_strictMono hab)

/-- A left sliding factor is genuinely below its root knot whenever the row
belongs to the displayed left support. -/
theorem TwoFanData.openKnot_slide_lt_s {m : Nat} (D : TwoFanData m)
    (i : Fin (3 * m - 1)) (j : Fin m) (h : Fin (m - 2))
    (hi : (i : Nat) ≤ (D.alpha j : Nat)) :
    D.openKnot (D.slideIndex i h) < D.s j := by
  unfold TwoFanData.openKnot
  dsimp only [TwoFanData.slideIndex]
  by_cases hA : (i : Nat) + (h : Nat) + 1 < m - 1
  · simp only [dif_pos hA]
    change D.leftAnchor < D.z (D.alpha j)
    exact D.leftAnchor_lt (D.alpha j)
  · simp only [dif_neg hA]
    by_cases hZ : (i : Nat) + (h : Nat) + 1 < 3 * m - 1
    · simp only [dif_pos hZ]
      change D.z ⟨((i : Nat) + (h : Nat) + 1) - (m - 1), _⟩ <
        D.z (D.alpha j)
      apply D.z_strict
      change ((i : Nat) + (h : Nat) + 1) - (m - 1) < (D.alpha j : Nat)
      rw [Nat.sub_lt_iff_lt_add (Nat.le_of_not_gt hA)]
      have hh := h.isLt
      have ha := (D.alpha j).isLt
      have hm := D.hm
      have hm' : m - 2 + 2 = m := Nat.sub_add_cancel hm
      omega
    · simp only [dif_neg hZ]
      exfalso
      have hi' := i.isLt
      have hh := h.isLt
      have ha := (D.alpha j).isLt
      have hm := D.hm
      have hm' : m - 2 + 2 = m := Nat.sub_add_cancel hm
      omega

/-- A right sliding factor is genuinely above its root knot whenever the row
belongs to the displayed right support. -/
theorem TwoFanData.u_lt_openKnot_slide {m : Nat} (D : TwoFanData m)
    (i : Fin (3 * m - 1)) (j : Fin m) (h : Fin (m - 2))
    (hi : m - 1 + (D.beta j : Nat) ≤ (i : Nat)) :
    D.u j < D.openKnot (D.slideIndex i h) := by
  unfold TwoFanData.openKnot
  dsimp only [TwoFanData.slideIndex]
  by_cases hA : (i : Nat) + (h : Nat) + 1 < m - 1
  · exfalso
    have hh := h.isLt
    have hb := (D.beta j).isLt
    have hm := D.hm
    have hm' : m - 2 + 2 = m := Nat.sub_add_cancel hm
    omega
  · simp only [dif_neg hA]
    by_cases hZ : (i : Nat) + (h : Nat) + 1 < 3 * m - 1
    · simp only [dif_pos hZ]
      change D.z (D.beta j) <
        D.z ⟨((i : Nat) + (h : Nat) + 1) - (m - 1), _⟩
      apply D.z_strict
      change (D.beta j : Nat) < ((i : Nat) + (h : Nat) + 1) - (m - 1)
      rw [Nat.lt_sub_iff_add_lt]
      have hh := h.isLt
      have hb := (D.beta j).isLt
      have hm := D.hm
      have hm' : m - 2 + 2 = m := Nat.sub_add_cancel hm
      omega
    · simp only [dif_neg hZ]
      change D.z (D.beta j) < D.rightAnchor
      exact D.lt_rightAnchor (D.beta j)

/-- The formula is identically zero above a left column's stated support. -/
theorem TwoFanData.leftCoefficient_eq_zero_of_lt {m : Nat} (D : TwoFanData m)
    (i : Fin (3 * m - 1)) (j : Fin m)
    (hi : (D.alpha j : Nat) < (i : Nat)) : D.leftCoefficient i j = 0 := by
  simp [TwoFanData.leftCoefficient, Nat.not_le_of_lt hi]

/-- The formula is identically zero below a right column's stated support. -/
theorem TwoFanData.rightCoefficient_eq_zero_of_lt {m : Nat} (D : TwoFanData m)
    (i : Fin (3 * m - 1)) (j : Fin m)
    (hi : (i : Nat) < m - 1 + (D.beta j : Nat)) : D.rightCoefficient i j = 0 := by
  simp [TwoFanData.rightCoefficient, Nat.not_le_of_lt hi]

/-- All factors in a supported left coefficient are positive. -/
theorem TwoFanData.leftCoefficient_pos {m : Nat} (D : TwoFanData m)
    (i : Fin (3 * m - 1)) (j : Fin m)
    (hi : (i : Nat) ≤ (D.alpha j : Nat)) : 0 < D.leftCoefficient i j := by
  rw [TwoFanData.leftCoefficient, if_pos hi]
  apply Finset.prod_pos
  intro h _
  exact sub_pos.mpr (D.openKnot_slide_lt_s i j h hi)

/-- All factors in a supported right coefficient are positive. -/
theorem TwoFanData.rightCoefficient_pos {m : Nat} (D : TwoFanData m)
    (i : Fin (3 * m - 1)) (j : Fin m)
    (hi : m - 1 + (D.beta j : Nat) ≤ (i : Nat)) :
    0 < D.rightCoefficient i j := by
  rw [TwoFanData.rightCoefficient, if_pos hi]
  apply Finset.prod_pos
  intro h _
  exact sub_pos.mpr (D.u_lt_openKnot_slide i j h hi)

/-- The left block of the raw matrix is definitionally the displayed
left-coefficient formula. -/
@[simp] theorem twoFanCoefficientMatrix_left_apply {m : Nat}
    (D : TwoFanData m) (i : Fin (3 * m - 1)) (j : Fin m) :
    twoFanCoefficientMatrix D i (twoFanColumnEquiv m (Sum.inl j)) =
      D.leftCoefficient i j := by
  simp [twoFanCoefficientMatrix]

/-- The right block of the raw matrix is definitionally the displayed
right-coefficient formula. -/
@[simp] theorem twoFanCoefficientMatrix_right_apply {m : Nat}
    (D : TwoFanData m) (i : Fin (3 * m - 1)) (j : Fin m) :
    twoFanCoefficientMatrix D i (twoFanColumnEquiv m (Sum.inr j)) =
      D.rightCoefficient i j := by
  simp [twoFanCoefficientMatrix]

/-- Exact support endpoints, packaged as functions before the monotonicity
certificate is assembled. -/
def TwoFanData.coefficientLo {m : Nat} (D : TwoFanData m) :
    Fin (2 * m) → Fin (3 * m - 1) := fun col ↦
  match (twoFanColumnEquiv m).symm col with
  | Sum.inl _ => ⟨0, by have hm := D.hm; omega⟩
  | Sum.inr j => ⟨m - 1 + (D.beta j : Nat), by
      have hb := (D.beta j).isLt
      have hm := D.hm
      omega⟩

/-- Exact upper support endpoints for the raw coefficient columns. -/
def TwoFanData.coefficientHi {m : Nat} (D : TwoFanData m) :
    Fin (2 * m) → Fin (3 * m - 1) := fun col ↦
  match (twoFanColumnEquiv m).symm col with
  | Sum.inl j => ⟨(D.alpha j : Nat), by
      have ha := (D.alpha j).isLt
      have hm := D.hm
      omega⟩
  | Sum.inr _ => ⟨3 * m - 2, by have hm := D.hm; omega⟩

/-- Every entry inside a stated left support interval is positive. -/
theorem twoFanCoefficientMatrix_left_pos {m : Nat} (D : TwoFanData m)
    (i : Fin (3 * m - 1)) (j : Fin m) (hi : (i : Nat) ≤ (D.alpha j : Nat)) :
    0 < twoFanCoefficientMatrix D i (twoFanColumnEquiv m (Sum.inl j)) := by
  simpa using D.leftCoefficient_pos i j hi

/-- Every entry inside a stated right support interval is positive. -/
theorem twoFanCoefficientMatrix_right_pos {m : Nat} (D : TwoFanData m)
    (i : Fin (3 * m - 1)) (j : Fin m)
    (hi : m - 1 + (D.beta j : Nat) ≤ (i : Nat)) :
    0 < twoFanCoefficientMatrix D i (twoFanColumnEquiv m (Sum.inr j)) := by
  simpa using D.rightCoefficient_pos i j hi

/-- Entries above the left support endpoint vanish exactly. -/
theorem twoFanCoefficientMatrix_left_zero {m : Nat} (D : TwoFanData m)
    (i : Fin (3 * m - 1)) (j : Fin m) (hi : (D.alpha j : Nat) < (i : Nat)) :
    twoFanCoefficientMatrix D i (twoFanColumnEquiv m (Sum.inl j)) = 0 := by
  simpa using D.leftCoefficient_eq_zero_of_lt i j hi

/-- Entries below the right support endpoint vanish exactly. -/
theorem twoFanCoefficientMatrix_right_zero {m : Nat} (D : TwoFanData m)
    (i : Fin (3 * m - 1)) (j : Fin m)
    (hi : (i : Nat) < m - 1 + (D.beta j : Nat)) :
    twoFanCoefficientMatrix D i (twoFanColumnEquiv m (Sum.inr j)) = 0 := by
  simpa using D.rightCoefficient_eq_zero_of_lt i j hi

/-- The first left merge rank is zero.  This is the endpoint part of the
Dyck condition, derived from the labelled order rather than stored twice. -/
theorem TwoFanData.alpha_zero {m : Nat} (D : TwoFanData m) :
    D.alpha ⟨0, by have hm := D.hm; omega⟩ =
      ⟨0, by have hm := D.hm; omega⟩ := by
  apply Fin.ext
  change (D.alpha ⟨0, by have hm := D.hm; omega⟩ : Nat) = 0
  by_contra hzero
  have hpos : 0 < (D.alpha ⟨0, by have hm := D.hm; omega⟩ : Nat) :=
    Nat.pos_of_ne_zero hzero
  let p : Fin (2 * m) := ⟨(D.alpha ⟨0, by have hm := D.hm; omega⟩ : Nat) - 1,
    by have ha := (D.alpha ⟨0, by have hm := D.hm; omega⟩).isLt; omega⟩
  obtain ⟨q, hq⟩ := D.merge.rank.surjective p
  rcases q with q | q
  · have hq0 : (⟨0, by have hm := D.hm; omega⟩ : Fin m) ≤ q := by
      change 0 ≤ (q : Nat)
      omega
    have hle := D.merge.left_strict.monotone hq0
    have hlt : D.merge.rank (Sum.inl q) <
        D.alpha ⟨0, by have hm := D.hm; omega⟩ := by
      rw [hq]
      change (p : Nat) < _
      simp only [p]
      omega
    exact (not_lt_of_ge hle) hlt
  · have hq0 : (⟨0, by have hm := D.hm; omega⟩ : Fin m) ≤ q := by
      change 0 ≤ (q : Nat)
      omega
    have hright := D.merge.right_strict.monotone hq0
    have hpair := D.merge.paired ⟨0, by have hm := D.hm; omega⟩
    have hleftRight : D.alpha ⟨0, by have hm := D.hm; omega⟩ <
        D.merge.rank (Sum.inr q) :=
      lt_of_lt_of_le hpair hright
    have hlt : D.merge.rank (Sum.inr q) <
        D.alpha ⟨0, by have hm := D.hm; omega⟩ := by
      rw [hq]
      change (p : Nat) < _
      simp only [p]
      omega
    exact (not_lt_of_ge hleftRight.le) hlt

/-- The last right merge rank is the last merged position. -/
theorem TwoFanData.beta_last {m : Nat} (D : TwoFanData m) :
    D.beta ⟨m - 1, by have hm := D.hm; omega⟩ =
      ⟨2 * m - 1, by have hm := D.hm; omega⟩ := by
  apply Fin.ext
  change (D.beta ⟨m - 1, by have hm := D.hm; omega⟩ : Nat) = 2 * m - 1
  apply Nat.le_antisymm
  · have hb := (D.beta ⟨m - 1, by have hm := D.hm; omega⟩).isLt
    omega
  · by_contra hnot
    push Not at hnot
    let p : Fin (2 * m) := ⟨(D.beta ⟨m - 1, by have hm := D.hm; omega⟩ : Nat) + 1,
      by have hb := (D.beta ⟨m - 1, by have hm := D.hm; omega⟩).isLt; omega⟩
    obtain ⟨q, hq⟩ := D.merge.rank.surjective p
    rcases q with q | q
    · have hqm : q ≤ ⟨m - 1, by have hm := D.hm; omega⟩ := by
        change (q : Nat) ≤ m - 1
        have hq := q.isLt
        omega
      have hleft := D.merge.left_strict.monotone hqm
      have hpair := D.merge.paired ⟨m - 1, by have hm := D.hm; omega⟩
      have hrightLeft : D.merge.rank (Sum.inl q) <
          D.beta ⟨m - 1, by have hm := D.hm; omega⟩ :=
        lt_of_le_of_lt hleft hpair
      have hlt : D.beta ⟨m - 1, by have hm := D.hm; omega⟩ <
          D.merge.rank (Sum.inl q) := by
        rw [hq]
        change _ < (p : Nat)
        change (D.beta ⟨m - 1, by have hm := D.hm; omega⟩ : Nat) <
          (D.beta ⟨m - 1, by have hm := D.hm; omega⟩ : Nat) + 1
        omega
      exact (not_lt_of_ge hrightLeft.le) hlt
    · have hqm : q ≤ ⟨m - 1, by have hm := D.hm; omega⟩ := by
        change (q : Nat) ≤ m - 1
        have hq := q.isLt
        omega
      have hright := D.merge.right_strict.monotone hqm
      have hlt : D.beta ⟨m - 1, by have hm := D.hm; omega⟩ <
          D.merge.rank (Sum.inr q) := by
        rw [hq]
        change _ < (p : Nat)
        change (D.beta ⟨m - 1, by have hm := D.hm; omega⟩ : Nat) <
          (D.beta ⟨m - 1, by have hm := D.hm; omega⟩ : Nat) + 1
        omega
      exact (not_lt_of_ge hright) hlt

/-- The raw two-fan coefficient matrix has exactly the monotone interval
support prescribed by the two merge-rank fans. -/
def twoFanCoefficientMatrix_intervalSupport {m : Nat} (D : TwoFanData m) :
    MonotoneColumnIntervalSupport (twoFanCoefficientMatrix D) where
  lo := D.coefficientLo
  hi := D.coefficientHi
  lo_mono := by
    intro a b hab
    let qa := (twoFanColumnEquiv m).symm a
    let qb := (twoFanColumnEquiv m).symm b
    have ha : twoFanColumnEquiv m qa = a :=
      (twoFanColumnEquiv m).apply_symm_apply a
    have hb : twoFanColumnEquiv m qb = b :=
      (twoFanColumnEquiv m).apply_symm_apply b
    rw [← ha, ← hb] at hab ⊢
    rcases qa with j | j <;> rcases qb with k | k
    · simp [TwoFanData.coefficientLo]
    · simp [TwoFanData.coefficientLo]
    · exfalso
      have hjk := hab
      change m + (j : Nat) ≤ (k : Nat) at hjk
      have hk := k.isLt
      omega
    · have hjkShift := Fin.le_iff_val_le_val.mp hab
      change m + (j : Nat) ≤ m + (k : Nat) at hjkShift
      have hjk : j ≤ k := by
        apply Fin.le_iff_val_le_val.mpr
        omega
      simp only [TwoFanData.coefficientLo, Equiv.symm_apply_apply]
      change m - 1 + (D.beta j : Nat) ≤ m - 1 + (D.beta k : Nat)
      exact Nat.add_le_add_left (D.beta_strictMono.monotone hjk) _
  hi_mono := by
    intro a b hab
    let qa := (twoFanColumnEquiv m).symm a
    let qb := (twoFanColumnEquiv m).symm b
    have ha : twoFanColumnEquiv m qa = a :=
      (twoFanColumnEquiv m).apply_symm_apply a
    have hb : twoFanColumnEquiv m qb = b :=
      (twoFanColumnEquiv m).apply_symm_apply b
    rw [← ha, ← hb] at hab ⊢
    rcases qa with j | j <;> rcases qb with k | k
    · have hjk := hab
      change (j : Nat) ≤ (k : Nat) at hjk
      simp only [TwoFanData.coefficientHi, Equiv.symm_apply_apply]
      exact D.alpha_strictMono.monotone hjk
    · simp only [TwoFanData.coefficientHi, Equiv.symm_apply_apply]
      change (D.alpha j : Nat) ≤ 3 * m - 2
      have ha := (D.alpha j).isLt
      omega
    · exfalso
      have hjk := hab
      change m + (j : Nat) ≤ (k : Nat) at hjk
      have hk := k.isLt
      omega
    · simp [TwoFanData.coefficientHi]
  entry_pos := by
    intro i col hlo hhi
    let q := (twoFanColumnEquiv m).symm col
    have hcol : twoFanColumnEquiv m q = col :=
      (twoFanColumnEquiv m).apply_symm_apply col
    rw [← hcol] at hlo hhi ⊢
    rcases q with j | j
    · apply twoFanCoefficientMatrix_left_pos
      simpa [TwoFanData.coefficientHi] using hhi
    · apply twoFanCoefficientMatrix_right_pos
      simpa [TwoFanData.coefficientLo] using hlo
  entry_zero := by
    intro i col hout
    let q := (twoFanColumnEquiv m).symm col
    have hcol : twoFanColumnEquiv m q = col :=
      (twoFanColumnEquiv m).apply_symm_apply col
    rw [← hcol] at hout ⊢
    rcases q with j | j
    · apply twoFanCoefficientMatrix_left_zero
      rcases hout with hlo | hhi
      · exfalso
        simp only [TwoFanData.coefficientLo, Equiv.symm_apply_apply] at hlo
        change (i : Nat) < 0 at hlo
        omega
      · simpa [TwoFanData.coefficientHi] using hhi
    · apply twoFanCoefficientMatrix_right_zero
      rcases hout with hlo | hhi
      · simpa [TwoFanData.coefficientLo] using hlo
      · exfalso
        simp only [TwoFanData.coefficientHi, Equiv.symm_apply_apply] at hhi
        change 3 * m - 2 < (i : Nat) at hhi
        have hi := i.isLt
        omega

end

end ColomboGeneralK2.Odd
