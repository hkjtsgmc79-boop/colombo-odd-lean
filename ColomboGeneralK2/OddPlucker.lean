import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# The plus-sign Pluecker identity for staircase dispersion

This file isolates the algebraic identity used when a missing column is
inserted into a staircase minor.  The common columns and the common rows are
encoded by the arbitrary `n × n` block `D`.  The three distinguished columns
are displayed in their natural order

* `0` = `j₁`,
* `1` = the inserted column `p`,
* `2` = `jₖ`.

Thus `singletonFrame ... 1` is the positive denominator, while
`pairFrame ... 0 2` is the target minor.  The theorem gives exactly

`den * target = small(j₁) * big(p,jₖ) + small(jₖ) * big(j₁,p)`.

The invertibility of `D` is the nonzero common-frame hypothesis needed by
the Schur-complement proof.  In the staircase application this is supplied
by strict positivity of the denominator's interior minor.  No total
nonnegativity assumption, target-minor assumption, or fixed dimension is
used here.

For the Schur-complement normal form, common columns are displayed after the
distinguished columns.  Returning each of the six determinants to increasing
ambient-column order contributes the same total permutation parity to each
of the three products, so the displayed plus sign is unchanged.
-/

namespace ColomboGeneralK2

namespace OddPlucker

open Matrix

variable {R : Type*} [CommRing R]

/-- Select two of the three distinguished columns in the displayed order. -/
def pairSelection (x y : Fin 3) : Fin 2 → Fin 3 := ![x, y]

/-- The square frame containing the common `n × n` block and two selected
distinguished columns.  The selected columns retain the order `(x,y)`. -/
def pairFrame {n : Nat} (A : Matrix (Fin 2) (Fin 3) R)
    (B : Matrix (Fin 2) (Fin n) R) (C : Matrix (Fin n) (Fin 3) R)
    (D : Matrix (Fin n) (Fin n) R) (x y : Fin 3) :
    Matrix (Fin 2 ⊕ Fin n) (Fin 2 ⊕ Fin n) R :=
  Matrix.fromBlocks (A.submatrix id (pairSelection x y)) B
    (C.submatrix id (pairSelection x y)) D

/-- The smaller frame using the first distinguished row and one selected
distinguished column. -/
def singletonFrame {n : Nat} (A : Matrix (Fin 2) (Fin 3) R)
    (B : Matrix (Fin 2) (Fin n) R) (C : Matrix (Fin n) (Fin 3) R)
    (D : Matrix (Fin n) (Fin n) R) (x : Fin 3) :
    Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) R :=
  Matrix.fromBlocks (fun _ _ ↦ A 0 x) (fun _ j ↦ B 0 j)
    (fun i _ ↦ C i x) D

/-- The arbitrary-size, naturally ordered, plus-sign three-term Pluecker
identity used by the column-dispersion induction.

Column `0` is `j₁`, column `1` is the inserted `p`, and column `2` is `jₖ`.
Consequently the left side is `den * target`; the two right-side products
are the first positive branch and the remaining nonnegative cross branch. -/
theorem plucker_frame {n : Nat}
    (A : Matrix (Fin 2) (Fin 3) R)
    (B : Matrix (Fin 2) (Fin n) R)
    (C : Matrix (Fin n) (Fin 3) R)
    (D : Matrix (Fin n) (Fin n) R) [Invertible D] :
    (singletonFrame A B C D 1).det * (pairFrame A B C D 0 2).det =
      (singletonFrame A B C D 0).det * (pairFrame A B C D 1 2).det +
        (singletonFrame A B C D 2).det * (pairFrame A B C D 0 1).det := by
  let S : Matrix (Fin 2) (Fin 3) R := A - B * ⅟D * C
  have hsingle (x : Fin 3) :
      (singletonFrame A B C D x).det = D.det * S 0 x := by
    rw [singletonFrame, Matrix.det_fromBlocks₂₂]
    apply congrArg (fun z ↦ D.det * z)
    rw [Matrix.det_unique]
    simp only [S, Matrix.sub_apply, Matrix.mul_apply]
  have hpair (x y : Fin 3) :
      (pairFrame A B C D x y).det =
        D.det * (S 0 x * S 1 y - S 0 y * S 1 x) := by
    rw [pairFrame, Matrix.det_fromBlocks₂₂, Matrix.det_fin_two]
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.submatrix_apply, id_eq,
      pairSelection, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [S, Matrix.sub_apply, Matrix.mul_apply]
  rw [hsingle, hsingle, hsingle, hpair, hpair, hpair]
  ring

/-- Field-valued interface for staircase applications: a nonzero determinant
of the common frame supplies the matrix-invertibility instance used above. -/
theorem plucker_frame_field {K : Type*} [Field K] {n : Nat}
    (A : Matrix (Fin 2) (Fin 3) K)
    (B : Matrix (Fin 2) (Fin n) K)
    (C : Matrix (Fin n) (Fin 3) K)
    (D : Matrix (Fin n) (Fin n) K) (hD : D.det ≠ 0) :
    (singletonFrame A B C D 1).det * (pairFrame A B C D 0 2).det =
      (singletonFrame A B C D 0).det * (pairFrame A B C D 1 2).det +
        (singletonFrame A B C D 2).det * (pairFrame A B C D 0 1).det := by
  letI : Invertible D.det := invertibleOfNonzero hD
  letI : Invertible D := Matrix.invertibleOfDetInvertible D
  exact plucker_frame A B C D

section Ordered

variable [LinearOrder R] [IsStrictOrderedRing R]

/-- Subtraction-free positivity propagation in precisely the orientation used
by the staircase proof: the denominator and first branch are positive, and
the cross branch is merely nonnegative. -/
theorem plucker_frame_target_pos {n : Nat}
    (A : Matrix (Fin 2) (Fin 3) R)
    (B : Matrix (Fin 2) (Fin n) R)
    (C : Matrix (Fin n) (Fin 3) R)
    (D : Matrix (Fin n) (Fin n) R) [Invertible D]
    (hden : 0 < (singletonFrame A B C D 1).det)
    (hsmall : 0 < (singletonFrame A B C D 0).det)
    (hbig : 0 < (pairFrame A B C D 1 2).det)
    (hcrossSmall : 0 ≤ (singletonFrame A B C D 2).det)
    (hcrossBig : 0 ≤ (pairFrame A B C D 0 1).det) :
    0 < (pairFrame A B C D 0 2).det := by
  have hprod : 0 < (singletonFrame A B C D 1).det *
      (pairFrame A B C D 0 2).det := by
    rw [plucker_frame]
    exact add_pos_of_pos_of_nonneg (mul_pos hsmall hbig)
      (mul_nonneg hcrossSmall hcrossBig)
  exact pos_of_mul_pos_right hprod hden.le

end Ordered

/-- Ordered-field wrapper for direct use after proving the common-frame
minor nonzero. -/
theorem plucker_frame_target_pos_field {K : Type*} [Field K]
    [LinearOrder K] [IsStrictOrderedRing K] {n : Nat}
    (A : Matrix (Fin 2) (Fin 3) K)
    (B : Matrix (Fin 2) (Fin n) K)
    (C : Matrix (Fin n) (Fin 3) K)
    (D : Matrix (Fin n) (Fin n) K) (hD : D.det ≠ 0)
    (hden : 0 < (singletonFrame A B C D 1).det)
    (hsmall : 0 < (singletonFrame A B C D 0).det)
    (hbig : 0 < (pairFrame A B C D 1 2).det)
    (hcrossSmall : 0 ≤ (singletonFrame A B C D 2).det)
    (hcrossBig : 0 ≤ (pairFrame A B C D 0 1).det) :
    0 < (pairFrame A B C D 0 2).det := by
  letI : Invertible D.det := invertibleOfNonzero hD
  letI : Invertible D := Matrix.invertibleOfDetInvertible D
  exact plucker_frame_target_pos A B C D hden hsmall hbig hcrossSmall hcrossBig


/-! ## Naturally ordered ambient minors

The following bridge turns the block-frame identity above into the literal
ordered-minor identity used by staircase dispersion.  The full row and column
frames have sizes `n+2` and `n+3`.  The inserted column `p` may occupy any
strictly internal position.  Every displayed minor is a `Matrix.submatrix`
selected by an order embedding.

The proof does not assume the desired identity or any sign of the target
minor.  It constructs all six reindexings, computes their permutation signs,
and cancels their common parity inside Lean.
-/

def middleEmb (n : Nat) : Fin n ↪o Fin (n + 2) :=
  (Fin.succOrderEmb n).comp (Fin.castLEOrderEmb (by omega))

def topEmb (n : Nat) : Fin (n + 1) ↪o Fin (n + 2) :=
  Fin.castLEOrderEmb (by omega)

def interiorEmb (n : Nat) : Fin (n + 1) ↪o Fin (n + 3) :=
  (Fin.succOrderEmb (n + 1)).comp (Fin.castLEOrderEmb (by omega))

def prefixEmb (n : Nat) : Fin (n + 2) ↪o Fin (n + 3) :=
  Fin.castLEOrderEmb (by omega)

def commonColEmb {n : Nat} (p : Fin (n + 3)) : Fin n ↪o Fin (n + 3) :=
  (middleEmb n).comp p.succAboveOrderEmb

def smallJOneEmb {n : Nat} (p : Fin (n + 3)) (hpLast : p < Fin.last (n + 2)) :
    Fin (n + 1) ↪o Fin (n + 3) :=
  (p.castLT hpLast).succAboveOrderEmb.comp (prefixEmb n)

def smallJLastEmb {n : Nat} (p : Fin (n + 3)) :
    Fin (n + 1) ↪o Fin (n + 3) :=
  (Fin.succOrderEmb (n + 1)).comp p.succAboveOrderEmb

def rowSpecial (n : Nat) : Fin 2 → Fin (n + 2) :=
  ![0, Fin.last (n + 1)]

def colSpecial {n : Nat} (p : Fin (n + 3)) : Fin 3 → Fin (n + 3) :=
  ![0, p, Fin.last (n + 2)]

def internalPos {n : Nat} (p : Fin (n + 3)) (hp0 : 0 < p)
    (hpLast : p < Fin.last (n + 2)) : Fin (n + 1) :=
  ⟨(p : Nat) - 1, by omega⟩

def afterFirstPos {n : Nat} (p : Fin (n + 3)) (hp0 : 0 < p) : Fin (n + 2) :=
  ⟨(p : Nat) - 1, by omega⟩

def prefixPos {n : Nat} (p : Fin (n + 3))
    (hpLast : p < Fin.last (n + 2)) : Fin (n + 2) :=
  ⟨p, by omega⟩

def qRow (n : Nat) : Equiv.Perm (Fin (n + 2)) :=
  (Fin.cycleIcc 1 (Fin.last (n + 1)))⁻¹

def frontPerm {m : Nat} (p : Fin (m + 1)) : Equiv.Perm (Fin (m + 1)) :=
  (Fin.cycleRange p)⁻¹

@[simp] theorem frontPerm_zero {m : Nat} (p : Fin (m + 1)) : frontPerm p 0 = p := by
  change (Fin.cycleRange p).symm 0 = p
  rw [Equiv.symm_apply_eq]
  exact (Fin.cycleRange_self p).symm

@[simp] theorem frontPerm_succ {m : Nat} (p : Fin (m + 1)) (i : Fin m) :
    frontPerm p i.succ = p.succAbove i := by
  change (Fin.cycleRange p).symm i.succ = p.succAbove i
  rw [Equiv.symm_apply_eq]
  by_cases h : i.castSucc < p
  · rw [Fin.succAbove_of_castSucc_lt _ _ h]
    rw [Fin.cycleRange_of_lt h]
    apply Fin.ext
    rw [Fin.val_add_one_of_lt (Fin.castSucc_lt_last i)]
    rfl
  · have hle : p ≤ i.castSucc := le_of_not_gt h
    rw [Fin.succAbove_of_le_castSucc _ _ hle]
    exact (Fin.cycleRange_of_gt (lt_of_le_of_lt hle i.castSucc_lt_succ)).symm

@[simp] theorem qRow_zero (n : Nat) : qRow n 0 = 0 := by
  change (Fin.cycleIcc 1 (Fin.last (n + 1))).symm 0 = 0
  rw [Equiv.symm_apply_eq]
  exact (Fin.cycleIcc_of_lt (i := (1 : Fin (n + 2)))
    (j := Fin.last (n + 1)) (k := 0) (by simp)
    ).symm

@[simp] theorem qRow_one (n : Nat) : qRow n 1 = Fin.last (n + 1) := by
  change (Fin.cycleIcc 1 (Fin.last (n + 1))).symm 1 = Fin.last (n + 1)
  rw [Equiv.symm_apply_eq]
  exact (Fin.cycleIcc_of_last (i := (1 : Fin (n + 2)))
    (j := Fin.last (n + 1)) (Fin.le_last _)).symm

@[simp] theorem qRow_addTwo (n : Nat) (x : Fin n) :
    qRow n ⟨(x : Nat) + 2, by omega⟩ = ⟨(x : Nat) + 1, by omega⟩ := by
  change (Fin.cycleIcc 1 (Fin.last (n + 1))).symm ⟨(x : Nat) + 2, by omega⟩ = _
  rw [Equiv.symm_apply_eq]
  rw [Fin.cycleIcc_of_ge_of_lt (i := (1 : Fin (n + 2)))
    (j := Fin.last (n + 1)) (k := ⟨(x : Nat) + 1, by omega⟩)
    (by change 1 ≤ (x : Nat) + 1; omega)
    (by change (x : Nat) + 1 < n + 1; omega)]
  apply Fin.ext
  change (x : Nat) + 2 = ((x : Nat) + 1 + 1) % (n + 2)
  rw [Nat.mod_eq_of_lt (by omega)]

def qDen {n : Nat} (p : Fin (n + 3)) (hp0 : 0 < p)
    (hpLast : p < Fin.last (n + 2)) : Equiv.Perm (Fin (n + 1)) :=
  (Fin.cycleRange (internalPos p hp0 hpLast))⁻¹

def qLastSmall (n : Nat) : Equiv.Perm (Fin (n + 1)) :=
  (Fin.cycleRange (Fin.last n))⁻¹

def qBigPJLast {n : Nat} (p : Fin (n + 3)) (hp0 : 0 < p) :
    Equiv.Perm (Fin (n + 2)) :=
  (Fin.cycleRange (afterFirstPos p hp0))⁻¹ * qRow n

def qBigJOneP {n : Nat} (p : Fin (n + 3)) (hpLast : p < Fin.last (n + 2)) :
    Equiv.Perm (Fin (n + 2)) :=
  (Fin.cycleIcc 1 (prefixPos p hpLast))⁻¹

theorem sign_qRow (n : Nat) : (qRow n).sign = (-1 : ℤˣ) ^ n := by
  rw [qRow, Equiv.Perm.sign_inv,
    Fin.sign_cycleIcc_of_le (Fin.le_last (1 : Fin (n + 2)))]
  congr 1

theorem sign_qDen {n : Nat} (p : Fin (n + 3)) (hp0 : 0 < p)
    (hpLast : p < Fin.last (n + 2)) :
    (qDen p hp0 hpLast).sign = (-1 : ℤˣ) ^ ((p : Nat) - 1) := by
  simp [qDen, Equiv.Perm.sign_inv, Fin.sign_cycleRange, internalPos]

theorem sign_qLastSmall (n : Nat) : (qLastSmall n).sign = (-1 : ℤˣ) ^ n := by
  simp [qLastSmall, Equiv.Perm.sign_inv, Fin.sign_cycleRange, Fin.last]

theorem sign_qBigPJLast {n : Nat} (p : Fin (n + 3)) (hp0 : 0 < p) :
    (qBigPJLast p hp0).sign =
      (-1 : ℤˣ) ^ ((p : Nat) - 1) * (-1 : ℤˣ) ^ n := by
  simp [qBigPJLast, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv,
    Fin.sign_cycleRange, afterFirstPos, sign_qRow]

theorem sign_qBigJOneP {n : Nat} (p : Fin (n + 3))
    (hp0 : 0 < p) (hpLast : p < Fin.last (n + 2)) :
    (qBigJOneP p hpLast).sign = (-1 : ℤˣ) ^ ((p : Nat) - 1) := by
  rw [qBigJOneP, Equiv.Perm.sign_inv,
    Fin.sign_cycleIcc_of_le (by change 1 ≤ (prefixPos p hpLast : Nat); simp [prefixPos]; omega)]
  congr 1

@[simp] theorem qBigJOneP_zero {n : Nat} (p : Fin (n + 3))
    (hpLast : p < Fin.last (n + 2)) : qBigJOneP p hpLast 0 = 0 := by
  change (Fin.cycleIcc 1 (prefixPos p hpLast)).symm 0 = 0
  rw [Equiv.symm_apply_eq]
  exact (Fin.cycleIcc_of_lt (i := (1 : Fin (n + 2)))
    (j := prefixPos p hpLast) (k := 0) (by simp)).symm

@[simp] theorem qBigJOneP_one {n : Nat} (p : Fin (n + 3))
    (hp0 : 0 < p) (hpLast : p < Fin.last (n + 2)) :
    qBigJOneP p hpLast 1 = prefixPos p hpLast := by
  change (Fin.cycleIcc 1 (prefixPos p hpLast)).symm 1 = prefixPos p hpLast
  rw [Equiv.symm_apply_eq]
  exact (Fin.cycleIcc_of_last (i := (1 : Fin (n + 2)))
    (j := prefixPos p hpLast) (by change 1 ≤ (prefixPos p hpLast : Nat); simp [prefixPos]; omega)).symm

@[simp] theorem qBigJOneP_addTwo {n : Nat} (p : Fin (n + 3))
    (hpLast : p < Fin.last (n + 2)) (x : Fin n) :
    qBigJOneP p hpLast ⟨(x : Nat) + 2, by omega⟩ =
      (prefixPos p hpLast).succAbove x.succ := by
  change (Fin.cycleIcc 1 (prefixPos p hpLast)).symm ⟨(x : Nat) + 2, by omega⟩ = _
  rw [Equiv.symm_apply_eq]
  by_cases h : x.succ.castSucc < prefixPos p hpLast
  · rw [Fin.succAbove_of_castSucc_lt _ _ h]
    rw [Fin.cycleIcc_of_ge_of_lt (i := (1 : Fin (n + 2)))
      (j := prefixPos p hpLast) (k := x.succ.castSucc)
      (by change 1 ≤ (x : Nat) + 1; omega) h]
    apply Fin.ext
    rw [Fin.val_add_one_of_lt (Fin.castSucc_lt_last x.succ)]
    rfl
  · have hle : prefixPos p hpLast ≤ x.succ.castSucc := le_of_not_gt h
    rw [Fin.succAbove_of_le_castSucc _ _ hle]
    exact (Fin.cycleIcc_of_gt (i := (1 : Fin (n + 2)))
      (j := prefixPos p hpLast) (k := x.succ.succ)
      (lt_of_le_of_lt hle x.succ.castSucc_lt_succ)).symm

def pairSumEquiv (n : Nat) : (Fin 2 ⊕ Fin n) ≃ Fin (n + 2) :=
  finSumFinEquiv.trans (finCongr (by omega))

def singleSumEquiv (n : Nat) : (Fin 1 ⊕ Fin n) ≃ Fin (n + 1) :=
  finSumFinEquiv.trans (finCongr (by omega))

def pairRowFrameIndex (n : Nat) : Fin 2 ⊕ Fin n → Fin (n + 2) :=
  Sum.elim (rowSpecial n) (middleEmb n)

def pairTargetColFrameIndex {n : Nat} (p : Fin (n + 3)) :
    Fin 2 ⊕ Fin n → Fin (n + 3) :=
  Sum.elim (fun x ↦ colSpecial p (pairSelection 0 2 x)) (commonColEmb p)

def pairPJLastColFrameIndex {n : Nat} (p : Fin (n + 3)) :
    Fin 2 ⊕ Fin n → Fin (n + 3) :=
  Sum.elim (fun x ↦ colSpecial p (pairSelection 1 2 x)) (commonColEmb p)

def pairJOnePColFrameIndex {n : Nat} (p : Fin (n + 3)) :
    Fin 2 ⊕ Fin n → Fin (n + 3) :=
  Sum.elim (fun x ↦ colSpecial p (pairSelection 0 1 x)) (commonColEmb p)

theorem pairRowFrameIndex_equiv (n : Nat) (i : Fin (n + 2)) :
    pairRowFrameIndex n ((pairSumEquiv n).symm i) = qRow n i := by
  rcases h : (pairSumEquiv n).symm i with x | x
  · have hi : i = pairSumEquiv n (Sum.inl x) := by
      rw [← h]
      simp
    subst i
    fin_cases x
    · change 0 = qRow n (pairSumEquiv n (Sum.inl ⟨0, by omega⟩))
      convert (qRow_zero n).symm using 1
    · change Fin.last (n + 1) =
        qRow n (pairSumEquiv n (Sum.inl ⟨1, by omega⟩))
      convert (qRow_one n).symm using 1
  · have hi : i = pairSumEquiv n (Sum.inr x) := by
      rw [← h]
      simp
    subst i
    change ⟨(x : Nat) + 1, by omega⟩ = qRow n (pairSumEquiv n (Sum.inr x))
    have harg : pairSumEquiv n (Sum.inr x) = ⟨(x : Nat) + 2, by omega⟩ := by
      apply Fin.ext
      simp [pairSumEquiv]
    rw [harg, qRow_addTwo]

theorem pairTargetColFrameIndex_equiv {n : Nat} (p : Fin (n + 3))
    (hp0 : 0 < p) (hpLast : p < Fin.last (n + 2)) (i : Fin (n + 2)) :
    pairTargetColFrameIndex p ((pairSumEquiv n).symm i) =
      p.succAboveOrderEmb (qRow n i) := by
  have hpoint (u : Fin 2 ⊕ Fin n) :
      pairTargetColFrameIndex p u = p.succAbove (pairRowFrameIndex n u) := by
    rcases u with x | x
    · fin_cases x
      · change (0 : Fin (n + 3)) = p.succAbove 0
        rw [Fin.succAbove_of_castSucc_lt]
        · rfl
        · change (0 : Fin (n + 3)) < p
          exact hp0
      · change Fin.last (n + 2) = p.succAbove (Fin.last (n + 1))
        rw [Fin.succAbove_of_le_castSucc]
        · rfl
        · change (p : Nat) ≤ n + 1
          omega
    · rfl
  rw [hpoint, pairRowFrameIndex_equiv]
  rfl

theorem pairPJLastColFrameIndex_equiv {n : Nat} (p : Fin (n + 3))
    (hp0 : 0 < p) (hpLast : p < Fin.last (n + 2)) (i : Fin (n + 2)) :
    pairPJLastColFrameIndex p ((pairSumEquiv n).symm i) =
      Fin.succOrderEmb (n + 2) (qBigPJLast p hp0 i) := by
  let a := afterFirstPos p hp0
  have hpoint (u : Fin 2 ⊕ Fin n) : pairPJLastColFrameIndex p u =
      Fin.succOrderEmb (n + 2) (frontPerm a (pairRowFrameIndex n u)) := by
    rcases u with x | x
    · fin_cases x
      · change p = Fin.succ (frontPerm a 0)
        rw [frontPerm_zero]
        apply Fin.ext
        simp [a, afterFirstPos]
        omega
      · change Fin.last (n + 2) = Fin.succ (frontPerm a (Fin.last (n + 1)))
        rw [show Fin.last (n + 1) = (Fin.last n).succ by rfl, frontPerm_succ]
        rw [Fin.succAbove_of_le_castSucc]
        · rfl
        · change (p : Nat) - 1 ≤ n
          omega
    · change commonColEmb p x = Fin.succ (frontPerm a ⟨(x : Nat) + 1, by omega⟩)
      let y : Fin (n + 1) := ⟨x, by omega⟩
      have hy : (⟨(x : Nat) + 1, by omega⟩ : Fin (n + 2)) = y.succ := rfl
      rw [hy, frontPerm_succ]
      apply Fin.ext
      change ((p.succAbove ⟨(x : Nat) + 1, by omega⟩ : Fin (n + 3)) : Nat) =
        ((Fin.succ (a.succAbove y) : Fin (n + 3)) : Nat)
      by_cases h : y.castSucc < a
      · rw [Fin.succAbove_of_castSucc_lt _ _ h]
        have hfull : (⟨(x : Nat) + 1, by omega⟩ : Fin (n + 2)).castSucc < p := by
          change (x : Nat) + 1 < (p : Nat)
          change (x : Nat) < (p : Nat) - 1 at h
          omega
        rw [Fin.succAbove_of_castSucc_lt _ _ hfull]
        rfl
      · have hle : a ≤ y.castSucc := le_of_not_gt h
        rw [Fin.succAbove_of_le_castSucc _ _ hle]
        have hfull : p ≤ (⟨(x : Nat) + 1, by omega⟩ : Fin (n + 2)).castSucc := by
          change (p : Nat) ≤ (x : Nat) + 1
          change (p : Nat) - 1 ≤ (x : Nat) at hle
          omega
        rw [Fin.succAbove_of_le_castSucc _ _ hfull]
        rfl
  rw [hpoint, pairRowFrameIndex_equiv]
  rfl

theorem pairJOnePColFrameIndex_equiv {n : Nat} (p : Fin (n + 3))
    (hp0 : 0 < p) (hpLast : p < Fin.last (n + 2)) (i : Fin (n + 2)) :
    pairJOnePColFrameIndex p ((pairSumEquiv n).symm i) =
      prefixEmb n (qBigJOneP p hpLast i) := by
  rcases h : (pairSumEquiv n).symm i with x | x
  · have hi : i = pairSumEquiv n (Sum.inl x) := by rw [← h]; simp
    subst i
    fin_cases x
    · have harg : pairSumEquiv n (Sum.inl ⟨0, by omega⟩) = (0 : Fin (n + 2)) := by
        apply Fin.ext
        simp [pairSumEquiv]
      rw [harg, qBigJOneP_zero]
      rfl
    · have harg : pairSumEquiv n (Sum.inl ⟨1, by omega⟩) = (1 : Fin (n + 2)) := by
        apply Fin.ext
        simp [pairSumEquiv]
      rw [harg, qBigJOneP_one p hp0 hpLast]
      apply Fin.ext
      rfl
  · have hi : i = pairSumEquiv n (Sum.inr x) := by rw [← h]; simp
    subst i
    have harg : pairSumEquiv n (Sum.inr x) = ⟨(x : Nat) + 2, by omega⟩ := by
      apply Fin.ext
      simp [pairSumEquiv]
    rw [harg, qBigJOneP_addTwo p hpLast]
    apply Fin.ext
    change ((p.succAbove ⟨(x : Nat) + 1, by omega⟩ : Fin (n + 3)) : Nat) =
      (((prefixPos p hpLast).succAbove x.succ : Fin (n + 2)) : Nat)
    by_cases hlt : x.succ.castSucc < prefixPos p hpLast
    · rw [Fin.succAbove_of_castSucc_lt _ _ hlt]
      have hfull : (⟨(x : Nat) + 1, by omega⟩ : Fin (n + 2)).castSucc < p := by
        exact hlt
      rw [Fin.succAbove_of_castSucc_lt _ _ hfull]
      rfl
    · have hle : prefixPos p hpLast ≤ x.succ.castSucc := le_of_not_gt hlt
      rw [Fin.succAbove_of_le_castSucc _ _ hle]
      have hfull : p ≤ (⟨(x : Nat) + 1, by omega⟩ : Fin (n + 2)).castSucc := by
        exact hle
      rw [Fin.succAbove_of_le_castSucc _ _ hfull]
      rfl

def singleRowFrameIndex (n : Nat) : Fin 1 ⊕ Fin n → Fin (n + 2) :=
  Sum.elim (fun _ ↦ 0) (middleEmb n)

def singleDenColFrameIndex {n : Nat} (p : Fin (n + 3)) :
    Fin 1 ⊕ Fin n → Fin (n + 3) :=
  Sum.elim (fun _ ↦ p) (commonColEmb p)

def singleJOneColFrameIndex {n : Nat} (p : Fin (n + 3)) :
    Fin 1 ⊕ Fin n → Fin (n + 3) :=
  Sum.elim (fun _ ↦ 0) (commonColEmb p)

def singleJLastColFrameIndex {n : Nat} (p : Fin (n + 3)) :
    Fin 1 ⊕ Fin n → Fin (n + 3) :=
  Sum.elim (fun _ ↦ Fin.last (n + 2)) (commonColEmb p)

theorem singleRowFrameIndex_equiv (n : Nat) (i : Fin (n + 1)) :
    singleRowFrameIndex n ((singleSumEquiv n).symm i) = topEmb n i := by
  rcases h : (singleSumEquiv n).symm i with x | x
  · have hi : i = singleSumEquiv n (Sum.inl x) := by rw [← h]; simp
    subst i
    fin_cases x
    rfl
  · have hi : i = singleSumEquiv n (Sum.inr x) := by rw [← h]; simp
    subst i
    apply Fin.ext
    simp [singleRowFrameIndex, singleSumEquiv, topEmb, middleEmb]

theorem interiorEmb_internalPos {n : Nat} (p : Fin (n + 3)) (hp0 : 0 < p)
    (hpLast : p < Fin.last (n + 2)) :
    interiorEmb n (internalPos p hp0 hpLast) = p := by
  apply Fin.ext
  simp [interiorEmb, internalPos]
  omega

theorem interiorEmb_succAbove_internal {n : Nat} (p : Fin (n + 3)) (hp0 : 0 < p)
    (hpLast : p < Fin.last (n + 2)) (i : Fin n) :
    interiorEmb n ((internalPos p hp0 hpLast).succAbove i) = commonColEmb p i := by
  apply Fin.ext
  change (((internalPos p hp0 hpLast).succAbove i : Fin (n + 1)) : Nat) + 1 =
    ((p.succAbove ⟨(i : Nat) + 1, by omega⟩ : Fin (n + 3)) : Nat)
  by_cases h : i.castSucc < internalPos p hp0 hpLast
  · rw [Fin.succAbove_of_castSucc_lt _ _ h]
    have hfull : (⟨(i : Nat) + 1, by omega⟩ : Fin (n + 2)).castSucc < p := by
      change (i : Nat) + 1 < (p : Nat)
      change (i : Nat) < (p : Nat) - 1 at h
      omega
    rw [Fin.succAbove_of_castSucc_lt _ _ hfull]
    rfl
  · have hle : internalPos p hp0 hpLast ≤ i.castSucc := le_of_not_gt h
    rw [Fin.succAbove_of_le_castSucc _ _ hle]
    have hfull : p ≤ (⟨(i : Nat) + 1, by omega⟩ : Fin (n + 2)).castSucc := by
      change (p : Nat) ≤ (i : Nat) + 1
      change (p : Nat) - 1 ≤ (i : Nat) at hle
      omega
    rw [Fin.succAbove_of_le_castSucc _ _ hfull]
    rfl

theorem singleDenColFrameIndex_equiv {n : Nat} (p : Fin (n + 3))
    (hp0 : 0 < p) (hpLast : p < Fin.last (n + 2)) (i : Fin (n + 1)) :
    singleDenColFrameIndex p ((singleSumEquiv n).symm i) =
      interiorEmb n (qDen p hp0 hpLast i) := by
  rcases h : (singleSumEquiv n).symm i with x | x
  · have hi : i = singleSumEquiv n (Sum.inl x) := by rw [← h]; simp
    subst i
    fin_cases x
    change p = interiorEmb n
      (qDen p hp0 hpLast (singleSumEquiv n (Sum.inl ⟨0, by omega⟩)))
    have harg : singleSumEquiv n (Sum.inl ⟨0, by omega⟩) = (0 : Fin (n + 1)) := by
      apply Fin.ext
      simp [singleSumEquiv]
    rw [harg]
    change p = interiorEmb n (frontPerm (internalPos p hp0 hpLast) 0)
    rw [frontPerm_zero, interiorEmb_internalPos]
  · have hi : i = singleSumEquiv n (Sum.inr x) := by rw [← h]; simp
    subst i
    have harg : singleSumEquiv n (Sum.inr x) = x.succ := by
      apply Fin.ext
      simp [singleSumEquiv]
    rw [harg]
    change commonColEmb p x =
      interiorEmb n (frontPerm (internalPos p hp0 hpLast) x.succ)
    rw [frontPerm_succ, interiorEmb_succAbove_internal]

theorem singleJOneColFrameIndex_equiv {n : Nat} (p : Fin (n + 3))
    (hp0 : 0 < p) (hpLast : p < Fin.last (n + 2)) (i : Fin (n + 1)) :
    singleJOneColFrameIndex p ((singleSumEquiv n).symm i) =
      smallJOneEmb p hpLast i := by
  rcases h : (singleSumEquiv n).symm i with x | x
  · have hi : i = singleSumEquiv n (Sum.inl x) := by rw [← h]; simp
    subst i
    fin_cases x
    have harg : singleSumEquiv n (Sum.inl ⟨0, by omega⟩) = (0 : Fin (n + 1)) := by
      apply Fin.ext
      simp [singleSumEquiv]
    rw [harg]
    change (0 : Fin (n + 3)) = prefixEmb n ((p.castLT hpLast).succAbove 0)
    rw [Fin.succAbove_of_castSucc_lt]
    · rfl
    · change (0 : Fin (n + 2)) < p.castLT hpLast
      exact hp0
  · have hi : i = singleSumEquiv n (Sum.inr x) := by rw [← h]; simp
    subst i
    have harg : singleSumEquiv n (Sum.inr x) = x.succ := by
      apply Fin.ext
      simp [singleSumEquiv]
    rw [harg]
    apply Fin.ext
    change ((p.succAbove ⟨(x : Nat) + 1, by omega⟩ : Fin (n + 3)) : Nat) =
      (((p.castLT hpLast).succAbove x.succ : Fin (n + 2)) : Nat)
    by_cases h : (⟨(x : Nat) + 1, by omega⟩ : Fin (n + 2)).castSucc < p
    · rw [Fin.succAbove_of_castSucc_lt _ _ h]
      have h' : x.succ.castSucc < p.castLT hpLast := by
        change (x : Nat) + 1 < (p : Nat)
        exact h
      rw [Fin.succAbove_of_castSucc_lt _ _ h']
      rfl
    · have hle : p ≤ (⟨(x : Nat) + 1, by omega⟩ : Fin (n + 2)).castSucc := le_of_not_gt h
      rw [Fin.succAbove_of_le_castSucc _ _ hle]
      have hle' : p.castLT hpLast ≤ x.succ.castSucc := by
        change (p : Nat) ≤ (x : Nat) + 1
        exact hle
      rw [Fin.succAbove_of_le_castSucc _ _ hle']
      rfl

theorem singleJLastColFrameIndex_equiv {n : Nat} (p : Fin (n + 3))
    (hpLast : p < Fin.last (n + 2)) (i : Fin (n + 1)) :
    singleJLastColFrameIndex p ((singleSumEquiv n).symm i) =
      smallJLastEmb p (qLastSmall n i) := by
  rcases h : (singleSumEquiv n).symm i with x | x
  · have hi : i = singleSumEquiv n (Sum.inl x) := by rw [← h]; simp
    subst i
    fin_cases x
    have harg : singleSumEquiv n (Sum.inl ⟨0, by omega⟩) = (0 : Fin (n + 1)) := by
      apply Fin.ext
      simp [singleSumEquiv]
    rw [harg]
    change Fin.last (n + 2) = smallJLastEmb p (frontPerm (Fin.last n) 0)
    rw [frontPerm_zero]
    apply Fin.ext
    change n + 2 = ((p.succAbove (Fin.last (n + 1)) : Fin (n + 3)) : Nat)
    rw [Fin.succAbove_of_le_castSucc]
    · rfl
    · change (p : Nat) ≤ n + 1
      omega
  · have hi : i = singleSumEquiv n (Sum.inr x) := by rw [← h]; simp
    subst i
    have harg : singleSumEquiv n (Sum.inr x) = x.succ := by
      apply Fin.ext
      simp [singleSumEquiv]
    rw [harg]
    change commonColEmb p x = smallJLastEmb p (frontPerm (Fin.last n) x.succ)
    rw [frontPerm_succ]
    rw [Fin.succAbove_last_apply]
    apply Fin.ext
    change ((p.succAbove ⟨(x : Nat) + 1, by omega⟩ : Fin (n + 3)) : Nat) =
      ((p.succAbove ⟨(x : Nat) + 1, by omega⟩ : Fin (n + 3)) : Nat)
    rfl

theorem det_perm_perm {m : Nat} (M : Matrix (Fin m) (Fin m) R)
    (r c : Equiv.Perm (Fin m)) :
    (M.submatrix r c).det = (r.sign : R) * (c.sign : R) * M.det := by
  calc
    (M.submatrix r c).det = ((M.submatrix r id).submatrix id c).det := by
      congr 1
    _ = (c.sign : R) * (M.submatrix r id).det := Matrix.det_permute' c _
    _ = (c.sign : R) * ((r.sign : R) * M.det) := by rw [Matrix.det_permute]
    _ = (r.sign : R) * (c.sign : R) * M.det := by ring

def denMinor {n : Nat} (X : Matrix (Fin (n + 2)) (Fin (n + 3)) R) : R :=
  (X.submatrix (topEmb n) (interiorEmb n)).det

def targetMinor {n : Nat} (X : Matrix (Fin (n + 2)) (Fin (n + 3)) R)
    (p : Fin (n + 3)) : R :=
  (X.submatrix (id : Fin (n + 2) → Fin (n + 2)) p.succAboveOrderEmb).det

def smallJOneMinor {n : Nat} (X : Matrix (Fin (n + 2)) (Fin (n + 3)) R)
    (p : Fin (n + 3)) (hpLast : p < Fin.last (n + 2)) : R :=
  (X.submatrix (topEmb n) (smallJOneEmb p hpLast)).det

def bigPJLastMinor {n : Nat} (X : Matrix (Fin (n + 2)) (Fin (n + 3)) R) : R :=
  (X.submatrix (id : Fin (n + 2) → Fin (n + 2)) (Fin.succOrderEmb (n + 2))).det

def smallJLastMinor {n : Nat} (X : Matrix (Fin (n + 2)) (Fin (n + 3)) R)
    (p : Fin (n + 3)) : R :=
  (X.submatrix (topEmb n) (smallJLastEmb p)).det

def bigJOnePMinor {n : Nat} (X : Matrix (Fin (n + 2)) (Fin (n + 3)) R) : R :=
  (X.submatrix (id : Fin (n + 2) → Fin (n + 2)) (prefixEmb n)).det

set_option maxHeartbeats 1000000 in
theorem natural_plucker_frame {n : Nat}
    {K : Type*} [Field K] (X : Matrix (Fin (n + 2)) (Fin (n + 3)) K)
    (p : Fin (n + 3)) (hp0 : 0 < p) (hpLast : p < Fin.last (n + 2))
    (hD : (X.submatrix (middleEmb n) (commonColEmb p)).det ≠ 0) :
    denMinor X * targetMinor X p =
      smallJOneMinor X p hpLast * bigPJLastMinor X +
        smallJLastMinor X p * bigJOnePMinor X := by
  let A : Matrix (Fin 2) (Fin 3) K := X.submatrix (rowSpecial n) (colSpecial p)
  let B : Matrix (Fin 2) (Fin n) K := X.submatrix (rowSpecial n) (commonColEmb p)
  let C : Matrix (Fin n) (Fin 3) K := X.submatrix (middleEmb n) (colSpecial p)
  let D : Matrix (Fin n) (Fin n) K := X.submatrix (middleEmb n) (commonColEmb p)
  have hD' : D.det ≠ 0 := by simpa [D] using hD
  have hmain := plucker_frame_field A B C D hD'
  have hframeTarget : pairFrame A B C D 0 2 =
      X.submatrix (pairRowFrameIndex n) (pairTargetColFrameIndex p) := by
    ext u v
    rcases u with u | u <;> rcases v with v | v
    · fin_cases u <;> fin_cases v <;>
        simp [A, pairFrame, pairSelection, pairRowFrameIndex,
          pairTargetColFrameIndex, rowSpecial, colSpecial]
    · fin_cases u <;>
        simp [B, pairFrame, pairSelection, pairRowFrameIndex,
          pairTargetColFrameIndex, rowSpecial, commonColEmb]
    · fin_cases v <;>
        simp [C, pairFrame, pairSelection, pairRowFrameIndex,
          pairTargetColFrameIndex, colSpecial, middleEmb]
    · simp [D, pairFrame, pairRowFrameIndex, pairTargetColFrameIndex]
  have htargetMatrix :
      (pairFrame A B C D 0 2).submatrix (pairSumEquiv n).symm (pairSumEquiv n).symm =
        (X.submatrix id p.succAboveOrderEmb).submatrix (qRow n) (qRow n) := by
    rw [hframeTarget]
    ext i j
    simp only [Matrix.submatrix_apply, id_eq]
    rw [pairRowFrameIndex_equiv, pairTargetColFrameIndex_equiv p hp0 hpLast]
  have hframeDen : singletonFrame A B C D 1 =
      X.submatrix (singleRowFrameIndex n) (singleDenColFrameIndex p) := by
    ext u v
    rcases u with u | u <;> rcases v with v | v
    · fin_cases u
      fin_cases v
      simp [A, singletonFrame, singleRowFrameIndex, singleDenColFrameIndex,
        rowSpecial, colSpecial]
    · fin_cases u
      simp [B, singletonFrame, singleRowFrameIndex, singleDenColFrameIndex,
        rowSpecial, commonColEmb]
    · fin_cases v
      simp [C, singletonFrame, singleRowFrameIndex, singleDenColFrameIndex,
        colSpecial, middleEmb]
    · simp [D, singletonFrame, singleRowFrameIndex, singleDenColFrameIndex]
  have hdenMatrix :
      (singletonFrame A B C D 1).submatrix
          (singleSumEquiv n).symm (singleSumEquiv n).symm =
        (X.submatrix (topEmb n) (interiorEmb n)).submatrix id
          (qDen p hp0 hpLast) := by
    rw [hframeDen]
    ext i j
    simp only [Matrix.submatrix_apply, id_eq]
    rw [singleRowFrameIndex_equiv, singleDenColFrameIndex_equiv p hp0 hpLast]
  have hdenDet : (singletonFrame A B C D 1).det =
      ((qDen p hp0 hpLast).sign : K) * denMinor X := by
    rw [← Matrix.det_submatrix_equiv_self (singleSumEquiv n).symm,
      hdenMatrix, Matrix.det_permute']
    rfl
  have htargetDet : (pairFrame A B C D 0 2).det = targetMinor X p := by
    rw [← Matrix.det_submatrix_equiv_self (pairSumEquiv n).symm,
      htargetMatrix, det_perm_perm, sign_qRow]
    simp
    change (-1 : K) ^ n * (-1 : K) ^ n *
      (X.submatrix id p.succAboveOrderEmb).det = targetMinor X p
    rw [← mul_pow]
    simp [targetMinor]
  have hframeSmallJOne : singletonFrame A B C D 0 =
      X.submatrix (singleRowFrameIndex n) (singleJOneColFrameIndex p) := by
    ext u v
    rcases u with u | u <;> rcases v with v | v
    · fin_cases u
      fin_cases v
      simp [A, singletonFrame, singleRowFrameIndex, singleJOneColFrameIndex,
        rowSpecial, colSpecial]
    · fin_cases u
      simp [B, singletonFrame, singleRowFrameIndex, singleJOneColFrameIndex,
        rowSpecial, commonColEmb]
    · fin_cases v
      simp [C, singletonFrame, singleRowFrameIndex, singleJOneColFrameIndex,
        colSpecial, middleEmb]
    · simp [D, singletonFrame, singleRowFrameIndex, singleJOneColFrameIndex]
  have hsmallJOneMatrix :
      (singletonFrame A B C D 0).submatrix
          (singleSumEquiv n).symm (singleSumEquiv n).symm =
        X.submatrix (topEmb n) (smallJOneEmb p hpLast) := by
    rw [hframeSmallJOne]
    ext i j
    simp only [Matrix.submatrix_apply]
    rw [singleRowFrameIndex_equiv,
      singleJOneColFrameIndex_equiv p hp0 hpLast]
  have hsmallJOneDet : (singletonFrame A B C D 0).det =
      smallJOneMinor X p hpLast := by
    rw [← Matrix.det_submatrix_equiv_self (singleSumEquiv n).symm,
      hsmallJOneMatrix]
    rfl
  have hframeSmallJLast : singletonFrame A B C D 2 =
      X.submatrix (singleRowFrameIndex n) (singleJLastColFrameIndex p) := by
    ext u v
    rcases u with u | u <;> rcases v with v | v
    · fin_cases u
      fin_cases v
      simp [A, singletonFrame, singleRowFrameIndex, singleJLastColFrameIndex,
        rowSpecial, colSpecial]
    · fin_cases u
      simp [B, singletonFrame, singleRowFrameIndex, singleJLastColFrameIndex,
        rowSpecial, commonColEmb]
    · fin_cases v
      simp [C, singletonFrame, singleRowFrameIndex, singleJLastColFrameIndex,
        colSpecial, middleEmb]
    · simp [D, singletonFrame, singleRowFrameIndex, singleJLastColFrameIndex]
  have hsmallJLastMatrix :
      (singletonFrame A B C D 2).submatrix
          (singleSumEquiv n).symm (singleSumEquiv n).symm =
        (X.submatrix (topEmb n) (smallJLastEmb p)).submatrix id (qLastSmall n) := by
    rw [hframeSmallJLast]
    ext i j
    simp only [Matrix.submatrix_apply, id_eq]
    rw [singleRowFrameIndex_equiv,
      singleJLastColFrameIndex_equiv p hpLast]
  have hsmallJLastDet : (singletonFrame A B C D 2).det =
      ((qLastSmall n).sign : K) * smallJLastMinor X p := by
    rw [← Matrix.det_submatrix_equiv_self (singleSumEquiv n).symm,
      hsmallJLastMatrix, Matrix.det_permute']
    rfl
  have hframeBigPJLast : pairFrame A B C D 1 2 =
      X.submatrix (pairRowFrameIndex n) (pairPJLastColFrameIndex p) := by
    ext u v
    rcases u with u | u <;> rcases v with v | v
    · fin_cases u <;> fin_cases v <;>
        simp [A, pairFrame, pairSelection, pairRowFrameIndex,
          pairPJLastColFrameIndex, rowSpecial, colSpecial]
    · fin_cases u <;>
        simp [B, pairFrame, pairSelection, pairRowFrameIndex,
          pairPJLastColFrameIndex, rowSpecial, commonColEmb]
    · fin_cases v <;>
        simp [C, pairFrame, pairSelection, pairRowFrameIndex,
          pairPJLastColFrameIndex, colSpecial, middleEmb]
    · simp [D, pairFrame, pairRowFrameIndex, pairPJLastColFrameIndex]
  have hbigPJLastMatrix :
      (pairFrame A B C D 1 2).submatrix (pairSumEquiv n).symm (pairSumEquiv n).symm =
        (X.submatrix id (Fin.succOrderEmb (n + 2))).submatrix
          (qRow n) (qBigPJLast p hp0) := by
    rw [hframeBigPJLast]
    ext i j
    simp only [Matrix.submatrix_apply, id_eq]
    rw [pairRowFrameIndex_equiv, pairPJLastColFrameIndex_equiv p hp0 hpLast]
  have hbigPJLastDet : (pairFrame A B C D 1 2).det =
      ((qRow n).sign : K) * ((qBigPJLast p hp0).sign : K) * bigPJLastMinor X := by
    rw [← Matrix.det_submatrix_equiv_self (pairSumEquiv n).symm,
      hbigPJLastMatrix, det_perm_perm]
    rfl
  have hframeBigJOneP : pairFrame A B C D 0 1 =
      X.submatrix (pairRowFrameIndex n) (pairJOnePColFrameIndex p) := by
    ext u v
    rcases u with u | u <;> rcases v with v | v
    · fin_cases u <;> fin_cases v <;>
        simp [A, pairFrame, pairSelection, pairRowFrameIndex,
          pairJOnePColFrameIndex, rowSpecial, colSpecial]
    · fin_cases u <;>
        simp [B, pairFrame, pairSelection, pairRowFrameIndex,
          pairJOnePColFrameIndex, rowSpecial, commonColEmb]
    · fin_cases v <;>
        simp [C, pairFrame, pairSelection, pairRowFrameIndex,
          pairJOnePColFrameIndex, colSpecial, middleEmb]
    · simp [D, pairFrame, pairRowFrameIndex, pairJOnePColFrameIndex]
  have hbigJOnePMatrix :
      (pairFrame A B C D 0 1).submatrix (pairSumEquiv n).symm (pairSumEquiv n).symm =
        (X.submatrix id (prefixEmb n)).submatrix (qRow n) (qBigJOneP p hpLast) := by
    rw [hframeBigJOneP]
    ext i j
    simp only [Matrix.submatrix_apply, id_eq]
    rw [pairRowFrameIndex_equiv,
      pairJOnePColFrameIndex_equiv p hp0 hpLast]
  have hbigJOnePDet : (pairFrame A B C D 0 1).det =
      ((qRow n).sign : K) * ((qBigJOneP p hpLast).sign : K) * bigJOnePMinor X := by
    rw [← Matrix.det_submatrix_equiv_self (pairSumEquiv n).symm,
      hbigJOnePMatrix, det_perm_perm]
    rfl
  let s : K := (-1 : K) ^ ((p : Nat) - 1)
  let t : K := (-1 : K) ^ n
  have hs : s ≠ 0 := pow_ne_zero _ (by norm_num)
  have ht : t * t = 1 := by
    dsimp [t]
    rw [← mul_pow]
    norm_num
  have hdenDet' : (singletonFrame A B C D 1).det = s * denMinor X := by
    simpa [s, sign_qDen p hp0 hpLast] using hdenDet
  have hsmallJLastDet' : (singletonFrame A B C D 2).det =
      t * smallJLastMinor X p := by
    simpa [t, sign_qLastSmall n] using hsmallJLastDet
  have hbigPJLastDet' : (pairFrame A B C D 1 2).det = s * bigPJLastMinor X := by
    calc
      (pairFrame A B C D 1 2).det = t * (s * t) * bigPJLastMinor X := by
        simpa [s, t, sign_qRow n, sign_qBigPJLast p hp0] using hbigPJLastDet
      _ = s * (t * t) * bigPJLastMinor X := by ring
      _ = s * bigPJLastMinor X := by rw [ht]; ring
  have hbigJOnePDet' : (pairFrame A B C D 0 1).det =
      t * s * bigJOnePMinor X := by
    simpa [s, t, sign_qRow n, sign_qBigJOneP p hp0 hpLast] using hbigJOnePDet
  rw [hdenDet', htargetDet, hsmallJOneDet, hbigPJLastDet',
    hsmallJLastDet', hbigJOnePDet'] at hmain
  apply mul_left_cancel₀ hs
  calc
    s * (denMinor X * targetMinor X p) =
        (s * denMinor X) * targetMinor X p := by ring
    _ = smallJOneMinor X p hpLast * (s * bigPJLastMinor X) +
        (t * smallJLastMinor X p) * (t * s * bigJOnePMinor X) := hmain
    _ = s * (smallJOneMinor X p hpLast * bigPJLastMinor X) +
        (t * t) * s * (smallJLastMinor X p * bigJOnePMinor X) := by ring
    _ = s * (smallJOneMinor X p hpLast * bigPJLastMinor X +
        smallJLastMinor X p * bigJOnePMinor X) := by
      rw [ht]
      ring

/-- Subtraction-free positivity propagation for the literal naturally
ordered minors.  This is the interface consumed by the staircase column-gap
step: the denominator and the first branch are positive, while the remaining
cross branch need only be nonnegative. -/
theorem natural_plucker_target_pos {n : Nat} {K : Type*} [Field K]
    [LinearOrder K] [IsStrictOrderedRing K]
    (X : Matrix (Fin (n + 2)) (Fin (n + 3)) K)
    (p : Fin (n + 3)) (hp0 : 0 < p) (hpLast : p < Fin.last (n + 2))
    (hD : (X.submatrix (middleEmb n) (commonColEmb p)).det ≠ 0)
    (hden : 0 < denMinor X)
    (hsmall : 0 < smallJOneMinor X p hpLast)
    (hbig : 0 < bigPJLastMinor X)
    (hcrossSmall : 0 ≤ smallJLastMinor X p)
    (hcrossBig : 0 ≤ bigJOnePMinor X) :
    0 < targetMinor X p := by
  have hprod : 0 < denMinor X * targetMinor X p := by
    rw [natural_plucker_frame X p hp0 hpLast hD]
    exact add_pos_of_pos_of_nonneg (mul_pos hsmall hbig)
      (mul_nonneg hcrossSmall hcrossBig)
  exact pos_of_mul_pos_right hprod hden.le

end OddPlucker

end ColomboGeneralK2
