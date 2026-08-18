import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Order.Interval.Finset.Fin

/-!
# Monotone interval support for the odd-branch staircase mechanism

This file fixes the generic minor and total-nonnegativity interfaces used by
the two-fan coefficient matrix.  Its main theorem is the structural-zero
half of staircase recognition: for a matrix whose column supports are
monotone intervals, a selected minor vanishes whenever its increasing
diagonal is not supported.

The proof is an arbitrary-size Hall obstruction in the Leibniz expansion.
It assumes neither total nonnegativity nor the sign of any minor.
-/

open scoped BigOperators

namespace ColomboGeneralK2.Odd

/-- A minor selected in the ambient natural row and column orders. -/
def matrixMinor {r c k : Nat} (A : Matrix (Fin r) (Fin c) ℝ)
    (rows : Fin k ↪o Fin r) (cols : Fin k ↪o Fin c) : ℝ :=
  (A.submatrix rows cols).det

@[simp]
theorem matrixMinor_zero {r c : Nat} (A : Matrix (Fin r) (Fin c) ℝ)
    (rows : Fin 0 ↪o Fin r) (cols : Fin 0 ↪o Fin c) :
    matrixMinor A rows cols = 1 := by
  simp [matrixMinor]

@[simp]
theorem matrixMinor_one {r c : Nat} (A : Matrix (Fin r) (Fin c) ℝ)
    (rows : Fin 1 ↪o Fin r) (cols : Fin 1 ↪o Fin c) :
    matrixMinor A rows cols = A (rows 0) (cols 0) := by
  simp [matrixMinor]

/-- Selecting a minor after taking a submatrix composes the two increasing
row and column embeddings. -/
theorem matrixMinor_submatrix {r c k l : Nat}
    (A : Matrix (Fin r) (Fin c) ℝ)
    (rows : Fin k ↪o Fin r) (cols : Fin k ↪o Fin c)
    (subRows subCols : Fin l ↪o Fin k) :
    matrixMinor (A.submatrix rows cols) subRows subCols =
      matrixMinor A (subRows.comp rows) (subCols.comp cols) := by
  simp [matrixMinor, Matrix.submatrix_submatrix]

/-- Total nonnegativity, stated using increasing finite-ordinal embeddings. -/
def IsTotallyNonnegative {r c : Nat} (A : Matrix (Fin r) (Fin c) ℝ) : Prop :=
  ∀ (k : Nat) (rows : Fin k ↪o Fin r) (cols : Fin k ↪o Fin c),
    0 ≤ matrixMinor A rows cols

/-- Transposition exchanges the selected row and column embeddings without
changing the naturally ordered minor. -/
theorem matrixMinor_transpose {r c k : Nat}
    (A : Matrix (Fin r) (Fin c) ℝ)
    (rows : Fin k ↪o Fin r) (cols : Fin k ↪o Fin c) :
    matrixMinor A.transpose cols rows = matrixMinor A rows cols := by
  rw [matrixMinor, matrixMinor, ← Matrix.det_transpose]
  congr 1

/-- Total nonnegativity is invariant under transpose. -/
theorem isTotallyNonnegative_transpose_iff {r c : Nat}
    (A : Matrix (Fin r) (Fin c) ℝ) :
    IsTotallyNonnegative A.transpose ↔ IsTotallyNonnegative A := by
  constructor
  · intro h k rows cols
    rw [← matrixMinor_transpose]
    exact h k cols rows
  · intro h k rows cols
    rw [matrixMinor_transpose]
    exact h k cols rows

/-- Each column is positive on one interval of rows and zero outside it, and
both endpoints move weakly downwards with the column. -/
structure MonotoneColumnIntervalSupport {r c : Nat}
    (A : Matrix (Fin r) (Fin c) ℝ) where
  lo : Fin c → Fin r
  hi : Fin c → Fin r
  lo_mono : Monotone lo
  hi_mono : Monotone hi
  entry_pos : ∀ i j, lo j ≤ i → i ≤ hi j → 0 < A i j
  entry_zero : ∀ i j, (i < lo j ∨ hi j < i) → A i j = 0

/-- Every entry of a monotone interval-supported matrix is nonnegative. -/
theorem MonotoneColumnIntervalSupport.entry_nonneg {r c : Nat}
    {A : Matrix (Fin r) (Fin c) ℝ} (S : MonotoneColumnIntervalSupport A)
    (i : Fin r) (j : Fin c) : 0 ≤ A i j := by
  by_cases hlo : S.lo j ≤ i
  · by_cases hhi : i ≤ S.hi j
    · exact (S.entry_pos i j hlo hhi).le
    · rw [S.entry_zero i j (Or.inr (lt_of_not_ge hhi))]
  · rw [S.entry_zero i j (Or.inl (lt_of_not_ge hlo))]

/-- The increasing diagonal of the selected minor lies in the column support. -/
def DiagonalSupported {r c : Nat} {A : Matrix (Fin r) (Fin c) ℝ}
    (S : MonotoneColumnIntervalSupport A) {k : Nat}
    (rows : Fin k ↪o Fin r) (cols : Fin k ↪o Fin c) : Prop :=
  ∀ t, S.lo (cols t) ≤ rows t ∧ rows t ≤ S.hi (cols t)

/-- Every entry on a supported increasing diagonal is strictly positive. -/
theorem DiagonalSupported.entry_pos {r c k : Nat}
    {A : Matrix (Fin r) (Fin c) ℝ} {S : MonotoneColumnIntervalSupport A}
    {rows : Fin k ↪o Fin r} {cols : Fin k ↪o Fin c}
    (h : DiagonalSupported S rows cols) (t : Fin k) :
    0 < A (rows t) (cols t) :=
  S.entry_pos _ _ (h t).1 (h t).2

/-- Restricting rows and columns by the same increasing embedding preserves
diagonal support. -/
theorem DiagonalSupported.comp {r c k l : Nat}
    {A : Matrix (Fin r) (Fin c) ℝ} {S : MonotoneColumnIntervalSupport A}
    {rows : Fin k ↪o Fin r} {cols : Fin k ↪o Fin c}
    (h : DiagonalSupported S rows cols) (e : Fin l ↪o Fin k) :
    DiagonalSupported S (e.comp rows) (e.comp cols) := by
  intro t
  exact h (e t)

/-- The increasing embedding of `k` consecutive indices starting at
`start`. -/
def intervalOrderEmb {k n : Nat} (start : Nat) (h : start + k ≤ n) :
    Fin k ↪o Fin n :=
  (Fin.natAddOrderEmb start).comp (Fin.castLEOrderEmb h)

@[simp]
theorem intervalOrderEmb_val {k n : Nat} (start : Nat) (h : start + k ≤ n)
    (i : Fin k) :
    ((intervalOrderEmb start h i : Fin n) : Nat) = start + (i : Nat) := by
  rfl

/-! ## Inserting one ambient index into an adjacent gap -/

/-- The new slot immediately after the left endpoint of a selected gap. -/
def gapSlot {k : Nat} (i : Fin k) : Fin (k + 2) :=
  i.castSucc.succ

theorem gapSlot_ne_zero {k : Nat} (i : Fin k) : gapSlot i ≠ 0 := by
  intro h
  have hval := congrArg Fin.val h
  change (i : Nat) + 1 = 0 at hval
  omega

theorem gapSlot_ne_last {k : Nat} (i : Fin k) :
    gapSlot i ≠ Fin.last (k + 1) := by
  intro h
  have hval := congrArg Fin.val h
  change (i : Nat) + 1 = k + 1 at hval
  have hi := i.isLt
  omega

/-- The first missing ambient value in the gap following `i`. -/
def gapValue {k n : Nat} (e : Fin (k + 1) ↪o Fin n) (i : Fin k)
    (hgap : (e i.castSucc : Nat) + 1 < (e i.succ : Nat)) : Fin n :=
  ⟨(e i.castSucc : Nat) + 1, by
    have hlt := (e i.succ).isLt
    omega⟩

/-- Insert `gapValue` into the selected tuple at `gapSlot`. -/
def insertGapFun {k n : Nat} (e : Fin (k + 1) ↪o Fin n) (i : Fin k)
    (hgap : (e i.castSucc : Nat) + 1 < (e i.succ : Nat)) :
    Fin (k + 2) → Fin n :=
  Fin.insertNth (gapSlot i) (gapValue e i hgap) e

theorem insertGapFun_strictMono {k n : Nat} (e : Fin (k + 1) ↪o Fin n)
    (i : Fin k) (hgap : (e i.castSucc : Nat) + 1 < (e i.succ : Nat)) :
    StrictMono (insertGapFun e i hgap) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro x
  have hslotLast : gapSlot i < Fin.last (k + 1) := by
    change (i : Nat) + 1 < k + 1
    exact Nat.add_lt_add_right i.isLt 1
  have hslotPos : (0 : Fin (k + 2)) < gapSlot i := by
    change 0 < (i : Nat) + 1
    omega
  by_cases hxi : (x : Nat) < (i : Nat)
  · have hx0 : x.castSucc < gapSlot i := by
      change (x : Nat) < (i : Nat) + 1
      omega
    have hx1 : x.succ < gapSlot i := by
      change (x : Nat) + 1 < (i : Nat) + 1
      omega
    rw [insertGapFun, Fin.insertNth_apply_below hx0,
      Fin.insertNth_apply_below hx1]
    have hidx : x.castSucc.castPred (Fin.ne_of_lt (lt_trans hx0 hslotLast)) <
        x.succ.castPred (Fin.ne_of_lt (lt_trans hx1 hslotLast)) := by
      change (x : Nat) < (x : Nat) + 1
      omega
    simpa using e.strictMono hidx
  · by_cases hix : (x : Nat) = (i : Nat)
    · have hx0 : x.castSucc < gapSlot i := by
        change (x : Nat) < (i : Nat) + 1
        omega
      have hx1 : x.succ = gapSlot i := by
        apply Fin.ext
        change (x : Nat) + 1 = (i : Nat) + 1
        omega
      rw [insertGapFun, Fin.insertNth_apply_below hx0, hx1,
        Fin.insertNth_apply_same]
      have heq : x.castSucc.castPred
          (Fin.ne_of_lt (lt_trans hx0 hslotLast)) = i.castSucc := by
        apply Fin.ext
        exact hix
      have hv : e i.castSucc < gapValue e i hgap := by
        change (e i.castSucc : Nat) < (e i.castSucc : Nat) + 1
        omega
      simpa [heq] using hv
    · by_cases hxip : (x : Nat) = (i : Nat) + 1
      · have hx0 : x.castSucc = gapSlot i := by
          apply Fin.ext
          exact hxip
        have hx1 : gapSlot i < x.succ := by
          change (i : Nat) + 1 < (x : Nat) + 1
          omega
        rw [insertGapFun, hx0, Fin.insertNth_apply_same,
          Fin.insertNth_apply_above hx1]
        have heq : x.succ.pred (Fin.ne_zero_of_lt (lt_trans hslotPos hx1)) = i.succ := by
          apply Fin.ext
          change (x : Nat) = (i : Nat) + 1
          exact hxip
        simpa [gapValue, heq] using hgap
      · have hx0 : gapSlot i < x.castSucc := by
          change (i : Nat) + 1 < (x : Nat)
          omega
        have hx1 : gapSlot i < x.succ := by
          change (i : Nat) + 1 < (x : Nat) + 1
          omega
        rw [insertGapFun, Fin.insertNth_apply_above hx0,
          Fin.insertNth_apply_above hx1]
        have hidx : x.castSucc.pred (Fin.ne_zero_of_lt (lt_trans hslotPos hx0)) <
            x.succ.pred (Fin.ne_zero_of_lt (lt_trans hslotPos hx1)) := by
          change (x : Nat) - 1 < (x : Nat)
          omega
        simpa using e.strictMono hidx

/-- The original selection with one ambient gap filled. -/
def insertGapOrderEmb {k n : Nat} (e : Fin (k + 1) ↪o Fin n) (i : Fin k)
    (hgap : (e i.castSucc : Nat) + 1 < (e i.succ : Nat)) :
    Fin (k + 2) ↪o Fin n :=
  OrderEmbedding.ofStrictMono (insertGapFun e i hgap)
    (insertGapFun_strictMono e i hgap)

@[simp]
theorem insertGapOrderEmb_apply_gapSlot {k n : Nat}
    (e : Fin (k + 1) ↪o Fin n) (i : Fin k)
    (hgap : (e i.castSucc : Nat) + 1 < (e i.succ : Nat)) :
    insertGapOrderEmb e i hgap (gapSlot i) = gapValue e i hgap := by
  simp [insertGapOrderEmb, insertGapFun]

@[simp]
theorem insertGapOrderEmb_apply_succAbove {k n : Nat}
    (e : Fin (k + 1) ↪o Fin n) (i : Fin k)
    (hgap : (e i.castSucc : Nat) + 1 < (e i.succ : Nat))
    (j : Fin (k + 1)) :
    insertGapOrderEmb e i hgap ((gapSlot i).succAbove j) = e j := by
  simp [insertGapOrderEmb, insertGapFun]

/-- Erasing the inserted slot recovers the original increasing selection. -/
theorem insertGapOrderEmb_erase {k n : Nat} (e : Fin (k + 1) ↪o Fin n)
    (i : Fin k) (hgap : (e i.castSucc : Nat) + 1 < (e i.succ : Nat)) :
    (gapSlot i).succAboveOrderEmb.comp (insertGapOrderEmb e i hgap) = e := by
  ext j
  change (insertGapFun e i hgap ((gapSlot i).succAbove j) : Nat) = (e j : Nat)
  rw [insertGapFun]
  simp

/-- The exact local hypothesis for staircase recognition: only supported
minors with consecutive rows and consecutive columns are assumed positive. -/
def SupportedSolidMinorsPositive {r c : Nat}
    {A : Matrix (Fin r) (Fin c) ℝ}
    (S : MonotoneColumnIntervalSupport A) : Prop :=
  ∀ (k rowStart colStart : Nat)
    (hrow : rowStart + k ≤ r) (hcol : colStart + k ≤ c),
    DiagonalSupported S
        (intervalOrderEmb rowStart hrow) (intervalOrderEmb colStart hcol) →
      0 < matrixMinor A
        (intervalOrderEmb rowStart hrow) (intervalOrderEmb colStart hcol)

/-- A permutation of a finite ordinal sends some element of a prefix across
the prefix's upper boundary. -/
theorem perm_prefix_cross {k : Nat} (σ : Equiv.Perm (Fin k)) (t : Fin k) :
    ∃ i : Fin k, i ≤ t ∧ t ≤ σ i := by
  by_contra h
  have hcross (i : Fin k) (hi : i ≤ t) : σ i < t := by
    exact lt_of_not_ge (fun hti ↦ h ⟨i, hi, hti⟩)
  have hsub : (Finset.Iic t).image σ ⊆ Finset.Iio t := by
    intro j hj
    rw [Finset.mem_image] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    simpa only [Finset.mem_Iio] using
      hcross i (by simpa only [Finset.mem_Iic] using hi)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ σ.injective, Fin.card_Iic, Fin.card_Iio] at hcard
  exact (Nat.not_succ_le_self (t : Nat)) hcard

/-- The suffix form of `perm_prefix_cross`. -/
theorem perm_suffix_cross {k : Nat} (σ : Equiv.Perm (Fin k)) (t : Fin k) :
    ∃ i : Fin k, t ≤ i ∧ σ i ≤ t := by
  obtain ⟨j, hj, hσj⟩ := perm_prefix_cross σ.symm t
  exact ⟨σ.symm j, hσj, by simpa using hj⟩

/-- One unsupported entry on the increasing diagonal forces the selected
minor to vanish. -/
theorem matrixMinor_eq_zero_of_diagonal_outside
    {r c k : Nat} {M : Matrix (Fin r) (Fin c) ℝ}
    (S : MonotoneColumnIntervalSupport M)
    (rows : Fin k ↪o Fin r) (cols : Fin k ↪o Fin c)
    (t : Fin k)
    (hout : rows t < S.lo (cols t) ∨ S.hi (cols t) < rows t) :
    matrixMinor M rows cols = 0 := by
  rw [matrixMinor, Matrix.det_apply']
  apply Finset.sum_eq_zero
  intro σ hσ
  apply mul_eq_zero_of_right
  rcases hout with htooHigh | htooLow
  · obtain ⟨i, hti, hσit⟩ := perm_suffix_cross σ t
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    apply S.entry_zero
    left
    exact lt_of_le_of_lt (rows.monotone hσit)
      (lt_of_lt_of_le htooHigh (S.lo_mono (cols.monotone hti)))
  · obtain ⟨i, hit, htσi⟩ := perm_prefix_cross σ t
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    apply S.entry_zero
    right
    exact lt_of_le_of_lt (S.hi_mono (cols.monotone hit))
      (lt_of_lt_of_le htooLow (rows.monotone htσi))

/-- Hall's obstruction for a monotone interval support: if even one entry of
the sorted diagonal is outside its column interval, the whole minor vanishes. -/
theorem matrixMinor_eq_zero_of_not_diagonalSupported
    {r c k : Nat} {M : Matrix (Fin r) (Fin c) ℝ}
    (S : MonotoneColumnIntervalSupport M)
    (rows : Fin k ↪o Fin r) (cols : Fin k ↪o Fin c)
    (h : ¬ DiagonalSupported S rows cols) :
    matrixMinor M rows cols = 0 := by
  obtain ⟨t, ht⟩ := Classical.not_forall.mp h
  rw [not_and_or] at ht
  apply matrixMinor_eq_zero_of_diagonal_outside S rows cols t
  rcases ht with hhigh | hlow
  · exact Or.inl (lt_of_not_ge hhigh)
  · exact Or.inr (lt_of_not_ge hlow)

end ColomboGeneralK2.Odd
