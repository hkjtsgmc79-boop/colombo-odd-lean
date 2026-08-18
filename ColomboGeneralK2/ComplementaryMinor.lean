import ColomboGeneralK2.MatrixAdapter
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Sign

/-!
# Complementary minors in natural power coordinates

The ambient columns occur in adjacent two-column blocks.  This file isolates
the useful sign fact: every permutation of whole blocks induces an even
permutation of the individual columns.  Consequently no shuffle sign occurs
when a paired set of columns is moved in front of its paired complement.

The final interface uses the natural low/high power split required by the
concrete Vandermonde/kernel factorization.  Every sign is proved from the
explicit column equivalences; no complementary-minor axiom is introduced.
-/

namespace ColomboGeneralK2

/-- Act by `σ` on the pair label and leave the side of the pair fixed. -/
def pairBlockPerm {n : Nat} (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin n × Fin 2) :=
  Equiv.prodCongrLeft (fun _ : Fin 2 ↦ σ)

@[simp]
theorem pairBlockPerm_apply {n : Nat} (σ : Equiv.Perm (Fin n))
    (q : Fin n) (side : Fin 2) :
    pairBlockPerm σ (q, side) = (σ q, side) := by
  rfl

/-- Every permutation of adjacent two-column blocks is even. -/
@[simp]
theorem pairBlockPerm_sign {n : Nat} (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign (pairBlockPerm σ) = 1 := by
  rw [pairBlockPerm, Equiv.Perm.sign_prodCongrLeft]
  simp

/-- Reordering the columns of a square matrix by whole pairs preserves its determinant. -/
theorem det_submatrix_pairBlockPerm {R : Type*} [CommRing R] {n : Nat}
    (σ : Equiv.Perm (Fin n)) (M : Matrix (Fin n × Fin 2) (Fin n × Fin 2) R) :
    (M.submatrix id (pairBlockPerm σ)).det = M.det := by
  rw [Matrix.det_permute', pairBlockPerm_sign]
  simp

/-- The same determinant invariance after using any row equivalence. -/
theorem det_submatrix_rowEquiv_pairBlockPerm {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : Nat}
    (row : (Fin n × Fin 2) ≃ ι) (σ : Equiv.Perm (Fin n))
    (M : Matrix ι (Fin n × Fin 2) R) :
    (M.submatrix row (pairBlockPerm σ)).det =
      (M.submatrix row id).det := by
  simpa [Matrix.submatrix_submatrix, Function.comp_def] using
    det_submatrix_pairBlockPerm σ (M.submatrix row id)

/-! ## Normalized complementary minors

Let `C` be a `κ × ι` matrix and put

`H = [I, -Cᵀ]`, `Y = [C, I]`.

The rows of `Y` span the kernel of `H`.  For a column shuffle `e` putting a
set of `ι` columns first and its `κ`-column complement last, the corresponding
maximal minors of `H` and `Y` agree up to `sign e`.  The proof below uses only
two unitriangular determinant calculations, so it works over a commutative
ring and does not need an inverse-minor theorem.
-/

/-- The normalized full-rank matrix `[I, -Cᵀ]`. -/
def normalizedTop {R ι κ : Type*} [Zero R] [One R] [Neg R]
    [DecidableEq ι] [DecidableEq κ] (C : Matrix κ ι R) :
    Matrix ι (ι ⊕ κ) R :=
  Matrix.fromCols 1 (-C.transpose)

/-- The normalized kernel matrix `[C, I]`. -/
def normalizedKernel {R ι κ : Type*} [Zero R] [One R]
    [DecidableEq κ] (C : Matrix κ ι R) : Matrix κ (ι ⊕ κ) R :=
  Matrix.fromCols C 1

/-- Standard coordinate rows supported on the columns placed last by `e`. -/
def complementSelector {R ι κ : Type*} [Zero R] [One R]
    [DecidableEq ι] [DecidableEq κ]
    (e : Equiv.Perm (ι ⊕ κ)) : Matrix κ (ι ⊕ κ) R :=
  (1 : Matrix (ι ⊕ κ) (ι ⊕ κ) R).submatrix (e ∘ Sum.inr) id

/-- Complete `normalizedTop` by coordinate rows on the complementary columns. -/
def completionMatrix {R ι κ : Type*} [Zero R] [One R] [Neg R]
    [DecidableEq ι] [DecidableEq κ]
    (C : Matrix κ ι R) (e : Equiv.Perm (ι ⊕ κ)) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) R :=
  Matrix.fromRows (normalizedTop C) (complementSelector e)

/-- The unitriangular shear cancelling the `-Cᵀ` block in `normalizedTop`. -/
def normalizedShear {R ι κ : Type*} [Zero R] [One R]
    [DecidableEq ι] [DecidableEq κ]
    (C : Matrix κ ι R) : Matrix (ι ⊕ κ) (ι ⊕ κ) R :=
  Matrix.fromBlocks 1 C.transpose 0 1

theorem completionMatrix_submatrix_shuffle
    {R ι κ : Type*} [CommRing R]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (C : Matrix κ ι R) (e : Equiv.Perm (ι ⊕ κ)) :
    (completionMatrix C e).submatrix id e =
      Matrix.fromBlocks
        ((normalizedTop C).submatrix id (e ∘ Sum.inl))
        ((normalizedTop C).submatrix id (e ∘ Sum.inr)) 0 1 := by
  ext (i | j) (a | b) <;>
    simp [completionMatrix, complementSelector, Matrix.fromBlocks,
      Matrix.one_apply, Function.comp_def]

theorem complementSelector_mul
    {R ι κ ν : Type*} [CommRing R]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : Equiv.Perm (ι ⊕ κ)) (M : Matrix (ι ⊕ κ) ν R) :
    complementSelector e * M = M.submatrix (e ∘ Sum.inr) id := by
  ext j b
  simpa [complementSelector, Matrix.mul_apply, Function.comp_def] using
    congrArg (fun N : Matrix (ι ⊕ κ) ν R ↦ N (e (Sum.inr j)) b)
      (Matrix.one_mul M)

theorem complementSelector_mul_kernelCols
    {R ι κ : Type*} [CommRing R]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (C : Matrix κ ι R) (e : Equiv.Perm (ι ⊕ κ)) :
    complementSelector e * Matrix.fromRows C.transpose 1 =
      ((normalizedKernel C).submatrix id (e ∘ Sum.inr)).transpose := by
  rw [complementSelector_mul]
  ext j b
  rcases h : e (Sum.inr j) with (a | k)
  · simp [normalizedKernel, Function.comp_def, h]
  · simp [normalizedKernel, Function.comp_def, h, Matrix.one_apply, eq_comm]

theorem completionMatrix_mul_normalizedShear
    {R ι κ : Type*} [CommRing R]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (C : Matrix κ ι R) (e : Equiv.Perm (ι ⊕ κ)) :
    completionMatrix C e * normalizedShear C =
      Matrix.fromBlocks 1 0
        (complementSelector e * Matrix.fromRows 1 0)
        (((normalizedKernel C).submatrix id (e ∘ Sum.inr)).transpose) := by
  rw [completionMatrix, normalizedShear]
  rw [← Matrix.fromCols_fromRows_eq_fromBlocks]
  rw [Matrix.fromRows_mul_fromCols]
  rw [complementSelector_mul_kernelCols]
  ext (i | j) (a | b) <;>
    simp [normalizedTop, Matrix.fromCols_mul_fromRows]

/-- Normalized complementary maximal minors, with the shuffle sign explicit. -/
theorem normalized_complementary_minor
    {R ι κ : Type*} [CommRing R]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (C : Matrix κ ι R) (e : Equiv.Perm (ι ⊕ κ)) :
    ((normalizedTop C).submatrix id (e ∘ Sum.inl)).det =
      (Equiv.Perm.sign e : R) *
        ((normalizedKernel C).submatrix id (e ∘ Sum.inr)).det := by
  let Hminor := (normalizedTop C).submatrix id (e ∘ Sum.inl)
  let Yminor := (normalizedKernel C).submatrix id (e ∘ Sum.inr)
  let Rfull := completionMatrix C e
  let G := normalizedShear C
  have hshuffle := completionMatrix_submatrix_shuffle C e
  have hmul := completionMatrix_mul_normalizedShear C e
  have hdetG : G.det = 1 := by
    dsimp only [G, normalizedShear]
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_one, one_mul]
  have hdetShuffle : Hminor.det = (Equiv.Perm.sign e : R) * Rfull.det := by
    calc
      Hminor.det =
          (Matrix.fromBlocks Hminor
            ((normalizedTop C).submatrix id (e ∘ Sum.inr)) 0 1).det := by
        rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
      _ = (Rfull.submatrix id e).det := by
        rw [hshuffle]
      _ = (Equiv.Perm.sign e : R) * Rfull.det := Matrix.det_permute' e Rfull
  have hdetMul : Rfull.det = Yminor.det := by
    calc
      Rfull.det = (Rfull * G).det := by
        rw [Matrix.det_mul, hdetG, mul_one]
      _ = (Matrix.fromBlocks 1 0
          (complementSelector e * Matrix.fromRows 1 0) Yminor.transpose).det := by
        rw [hmul]
      _ = Yminor.det := by
        rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul,
          Matrix.det_transpose]
  rw [hdetShuffle, hdetMul]

/-! ## Paired shuffles -/

/-- Act on arbitrary pair labels and leave the two sides fixed. -/
def pairBlockPermOf {α : Type*} (σ : Equiv.Perm α) :
    Equiv.Perm (α × Fin 2) :=
  Equiv.prodCongrLeft (fun _ : Fin 2 ↦ σ)

@[simp]
theorem pairBlockPermOf_apply {α : Type*} (σ : Equiv.Perm α)
    (q : α) (side : Fin 2) :
    pairBlockPermOf σ (q, side) = (σ q, side) := by
  rfl

/-- Duplicating every label into an adjacent pair makes every label permutation even. -/
@[simp]
theorem pairBlockPermOf_sign {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) : Equiv.Perm.sign (pairBlockPermOf σ) = 1 := by
  rw [pairBlockPermOf, Equiv.Perm.sign_prodCongrLeft]
  simp

/-! ### The fixed natural-power/anti-pair shuffle -/

/-- Extend a permutation of `Fin n` by fixing the new last element. -/
def extendLast {n : Nat} (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + 1)) :=
  ((finSuccEquivLast (n := n)).symm).permCongr σ.optionCongr

@[simp]
theorem extendLast_castSucc {n : Nat} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    extendLast σ i.castSucc = (σ i).castSucc := by
  simp [extendLast, Equiv.permCongr_apply]

@[simp]
theorem extendLast_last {n : Nat} (σ : Equiv.Perm (Fin n)) :
    extendLast σ (Fin.last n) = Fin.last n := by
  simp [extendLast, Equiv.permCongr_apply]

@[simp]
theorem extendLast_sign {n : Nat} (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign (extendLast σ) = Equiv.Perm.sign σ := by
  simp [extendLast]

/-- Extend a permutation by fixing the new zero and shifting its old action. -/
def extendZero {n : Nat} (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + 1)) :=
  Equiv.Perm.decomposeFin.symm (0, σ)

@[simp]
theorem extendZero_zero {n : Nat} (σ : Equiv.Perm (Fin n)) :
    extendZero σ 0 = 0 := by
  simp [extendZero]

@[simp]
theorem extendZero_succ {n : Nat} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    extendZero σ i.succ = (σ i).succ := by
  simp [extendZero]

@[simp]
theorem extendZero_sign {n : Nat} (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign (extendZero σ) = Equiv.Perm.sign σ := by
  simp [extendZero]

/--
The fixed permutation sending adjacent pair order
`L₀,R₀,L₁,R₁,...` to nested natural-power order
`L₀,L₁,...,R₁,R₀`.  The recursion removes `L₀`, rotates `R₀`
across an even number of remaining columns, and recurses on the tail.
-/
def antiPowerPerm : (s : Nat) → Equiv.Perm (Fin (2 * s))
  | 0 => Equiv.refl _
  | s + 1 =>
      extendZero ((finRotate (2 * s + 1)).symm.trans
        (extendLast (antiPowerPerm s)))

/-- The fixed natural-power/anti-pair permutation is always even. -/
@[simp]
theorem antiPowerPerm_sign (s : Nat) :
    Equiv.Perm.sign (antiPowerPerm s) = 1 := by
  induction s with
  | zero => simp [antiPowerPerm]
  | succ s ih =>
      simp [antiPowerPerm, ih, sign_finRotate, pow_mul]

theorem finRotate_symm_zero_eq_last (n : Nat) :
    (finRotate (n + 1)).symm 0 = Fin.last n := by
  apply (finRotate (n + 1)).symm_apply_eq.mpr
  simp

theorem finRotate_symm_succ_eq_castSucc {n : Nat} (i : Fin n) :
    (finRotate (n + 1)).symm i.succ = i.castSucc := by
  apply Fin.ext
  rw [coe_finRotate_symm_of_ne_zero (by simp)]
  rfl

@[simp]
theorem pairCol_succ_zero_left (s : Nat) :
    pairCol (s + 1) 0 0 = 0 := by
  ext
  simp [pairCol, pairColumnEquiv, finProdFinEquiv]

@[simp]
theorem pairCol_succ_zero_right (s : Nat) :
    pairCol (s + 1) 0 1 = (0 : Fin (2 * s + 1)).succ := by
  ext
  simp [pairCol, pairColumnEquiv, finProdFinEquiv]

@[simp]
theorem pairCol_right_castSucc_eq_left_succ {s : Nat} (q : Fin s) :
    (pairCol s q 1).castSucc = (pairCol s q 0).succ := by
  ext
  simp [pairCol, pairColumnEquiv, finProdFinEquiv]
  omega

@[simp]
theorem pairCol_succ_succ_left {s : Nat} (q : Fin s) :
    pairCol (s + 1) q.succ 0 = ((pairCol s q 1).castSucc).succ := by
  ext
  simp [pairCol, pairColumnEquiv, finProdFinEquiv]
  omega

@[simp]
theorem pairCol_succ_succ_right {s : Nat} (q : Fin s) :
    pairCol (s + 1) q.succ 1 = (pairCol s q 1).succ.succ := by
  ext
  simp [pairCol, pairColumnEquiv, finProdFinEquiv]
  omega

/-- The recursive permutation has the advertised nested-pair values. -/
theorem antiPowerPerm_pair_values (s : Nat) :
    (∀ q : Fin s, ((antiPowerPerm s (pairCol s q 0) : Fin (2 * s)) : Nat) = q) ∧
    (∀ q : Fin s, ((antiPowerPerm s (pairCol s q 1) : Fin (2 * s)) : Nat) =
      2 * s - 1 - q) := by
  induction s with
  | zero =>
      constructor <;> intro q <;> exact Fin.elim0 q
  | succ s ih =>
      constructor
      · intro q
        refine Fin.cases ?_ (fun q ↦ ?_) q
        · simp [antiPowerPerm]
        · rw [pairCol_succ_succ_left, antiPowerPerm, extendZero_succ,
            Equiv.trans_apply, pairCol_right_castSucc_eq_left_succ,
            finRotate_symm_succ_eq_castSucc, extendLast_castSucc]
          simpa using congrArg Nat.succ (ih.1 q)
      · intro q
        refine Fin.cases ?_ (fun q ↦ ?_) q
        · rw [pairCol_succ_zero_right, antiPowerPerm, extendZero_succ,
            Equiv.trans_apply, finRotate_symm_zero_eq_last, extendLast_last]
          simp
          omega
        · rw [pairCol_succ_succ_right, antiPowerPerm, extendZero_succ,
            Equiv.trans_apply, finRotate_symm_succ_eq_castSucc,
            extendLast_castSucc]
          simp only [Fin.val_succ, Fin.val_castSucc]
          rw [ih.2 q]
          omega

/-- Pair labels followed by a side, interpreted as nested anti-diagonal powers. -/
def antiDiagonalPairEquiv (s : Nat) : Fin s × Fin 2 ≃ Fin (2 * s) :=
  (pairColumnEquiv s).trans (antiPowerPerm s)

theorem antiDiagonalPairEquiv_left_value {s : Nat} (q : Fin s) :
    ((antiDiagonalPairEquiv s (q, 0) : Fin (2 * s)) : Nat) = q :=
  (antiPowerPerm_pair_values s).1 q

theorem antiDiagonalPairEquiv_right_value {s : Nat} (q : Fin s) :
    ((antiDiagonalPairEquiv s (q, 1) : Fin (2 * s)) : Nat) =
      2 * s - 1 - q :=
  (antiPowerPerm_pair_values s).2 q

/-! ### Natural low/high power coordinates -/

/-- The reference pair labels: the first `m` labels, followed by the last two. -/
def referencePairEquiv (m : Nat) : Fin m ⊕ Fin 2 ≃ Fin (m + 2) :=
  finSumFinEquiv

/-- Decode natural low/high blocks into adjacent pair coordinates. -/
def naturalPairDecode (m : Nat) :
    Fin (2 * m) ⊕ Fin 4 ≃ (Fin m × Fin 2) ⊕ (Fin 2 × Fin 2) :=
  Equiv.sumCongr (pairColumnEquiv m).symm (pairColumnEquiv 2).symm

/-- Concatenate the natural low block `0..2m-1` and the final four powers. -/
def naturalPowerEquiv (m : Nat) :
    Fin (2 * m) ⊕ Fin 4 ≃ Fin (2 * (m + 2)) :=
  finSumFinEquiv.trans (finCongr (by omega))

@[simp]
theorem naturalPowerEquiv_apply_left_value (m : Nat) (i : Fin (2 * m)) :
    ((naturalPowerEquiv m (Sum.inl i) : Fin (2 * (m + 2))) : Nat) = i := by
  rfl

@[simp]
theorem naturalPowerEquiv_apply_right_value (m : Nat) (j : Fin 4) :
    ((naturalPowerEquiv m (Sum.inr j) : Fin (2 * (m + 2))) : Nat) =
      2 * m + j := by
  rfl

/-- Reference adjacent-pair listing, before the fixed anti-diagonal shuffle. -/
def referenceAdjacentEquiv (m : Nat) :
    Fin (2 * m) ⊕ Fin 4 ≃ Fin (2 * (m + 2)) :=
  (naturalPairDecode m).trans
    (((Equiv.sumProdDistrib (Fin m) (Fin 2) (Fin 2)).symm.trans
      ((referencePairEquiv m).prodCongr (Equiv.refl (Fin 2)))).trans
        (pairColumnEquiv (m + 2)))

/-- The reference adjacent-pair listing is exactly natural concatenation. -/
theorem referenceAdjacentEquiv_eq_naturalPowerEquiv (m : Nat) :
    referenceAdjacentEquiv m = naturalPowerEquiv m := by
  ext x
  rcases x with (i | j)
  · let qs := (pairColumnEquiv m).symm i
    have hi : pairColumnEquiv m qs = i := (pairColumnEquiv m).apply_symm_apply i
    rw [← hi]
    rcases qs with ⟨q, side⟩
    fin_cases side
    · simp [referenceAdjacentEquiv, naturalPairDecode,
        referencePairEquiv, pairColumnEquiv, finProdFinEquiv,
        finCongr_apply]
    · simp [referenceAdjacentEquiv, naturalPairDecode,
        referencePairEquiv, pairColumnEquiv, finProdFinEquiv,
        finCongr_apply]
      omega
  · let qs := (pairColumnEquiv 2).symm j
    have hj : pairColumnEquiv 2 qs = j := (pairColumnEquiv 2).apply_symm_apply j
    rw [← hj]
    rcases qs with ⟨q, side⟩
    fin_cases side
    · simp [referenceAdjacentEquiv, naturalPairDecode,
        referencePairEquiv, pairColumnEquiv, finProdFinEquiv,
        finCongr_apply]
      omega
    · simp [referenceAdjacentEquiv, naturalPairDecode,
        referencePairEquiv, pairColumnEquiv, finProdFinEquiv,
        finCongr_apply]
      omega

/-- Distribute a pair-label split over the common two-column side. -/
def pairedColumnEquiv {α β γ : Type*} (p : α ⊕ β ≃ γ) :
    (α × Fin 2) ⊕ (β × Fin 2) ≃ γ × Fin 2 :=
  (Equiv.sumProdDistrib α β (Fin 2)).symm.trans
    (p.prodCongr (Equiv.refl (Fin 2)))

@[simp]
theorem pairedColumnEquiv_apply_left {α β γ : Type*} (p : α ⊕ β ≃ γ)
    (a : α) (side : Fin 2) :
    pairedColumnEquiv p (Sum.inl (a, side)) = (p (Sum.inl a), side) := by
  rfl

@[simp]
theorem pairedColumnEquiv_apply_right {α β γ : Type*} (p : α ⊕ β ≃ γ)
    (b : β) (side : Fin 2) :
    pairedColumnEquiv p (Sum.inr (b, side)) = (p (Sum.inr b), side) := by
  rfl

/-- Coordinate transition from one pair-label split to another. -/
def pairedTransition {α β γ : Type*} (selected reference : α ⊕ β ≃ γ) :
    Equiv.Perm ((α × Fin 2) ⊕ (β × Fin 2)) :=
  (pairedColumnEquiv selected).trans (pairedColumnEquiv reference).symm

/-- A transition between two whole-pair enumerations has positive sign. -/
@[simp]
theorem pairedTransition_sign {α β γ : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    (selected reference : α ⊕ β ≃ γ) :
    Equiv.Perm.sign (pairedTransition selected reference) = 1 := by
  let d := Equiv.sumProdDistrib α β (Fin 2)
  let σ : Equiv.Perm (α ⊕ β) := selected.trans reference.symm
  have hconj : pairedTransition selected reference =
      d.permCongr (pairBlockPermOf σ) := by
    ext x
    rcases x with (⟨a, side⟩ | ⟨b, side⟩) <;>
      simp [pairedTransition, pairedColumnEquiv, pairBlockPermOf, d, σ,
        Equiv.permCongr_apply]
  rw [hconj, Equiv.Perm.sign_permCongr, pairBlockPermOf_sign]

@[simp]
theorem pairedTransition_reference_apply {α β γ : Type*}
    (selected reference : α ⊕ β ≃ γ)
    (x : (α × Fin 2) ⊕ (β × Fin 2)) :
    pairedColumnEquiv reference (pairedTransition selected reference x) =
      pairedColumnEquiv selected x := by
  simp [pairedTransition]

/-! ## Sorted finite-set interface -/

/-- Identify membership in a finite-set complement with nonmembership. -/
def finsetComplementSubtypeEquiv {γ : Type*} [Fintype γ] [DecidableEq γ]
    (S : Finset γ) : {x // x ∈ Sᶜ} ≃ {x // x ∉ S} :=
  Equiv.subtypeEquivRight (fun x ↦ by simp)

/-- Enumerate `S` first and `Sᶜ` second, sorting each part increasingly. -/
def selectedComplementPairEquiv {m : Nat} (S : Finset (Fin (m + 2)))
    (hs : S.card = m) (hc : Sᶜ.card = 2) :
    Fin m ⊕ Fin 2 ≃ Fin (m + 2) :=
  (Equiv.sumCongr (sortedPairEquiv S hs)
      ((sortedPairEquiv Sᶜ hc).trans (finsetComplementSubtypeEquiv S))).trans
    (Equiv.sumCompl (fun x ↦ x ∈ S))

@[simp]
theorem selectedComplementPairEquiv_apply_left {m : Nat}
    (S : Finset (Fin (m + 2))) (hs : S.card = m) (hc : Sᶜ.card = 2)
    (q : Fin m) :
    selectedComplementPairEquiv S hs hc (Sum.inl q) =
      (sortedPairVectorOfCard S hs).get q := by
  rfl

@[simp]
theorem selectedComplementPairEquiv_apply_right {m : Nat}
    (S : Finset (Fin (m + 2))) (hs : S.card = m) (hc : Sᶜ.card = 2)
    (q : Fin 2) :
    selectedComplementPairEquiv S hs hc (Sum.inr q) =
      (sortedPairVectorOfCard Sᶜ hc).get q := by
  rfl

/-- The paired column shuffle attached to a sorted finite set `S`. -/
def finsetPairedShuffle {m : Nat} (S : Finset (Fin (m + 2)))
    (hs : S.card = m) (hc : Sᶜ.card = 2) :
    Equiv.Perm ((Fin m × Fin 2) ⊕ (Fin 2 × Fin 2)) :=
  pairedTransition (selectedComplementPairEquiv S hs hc) (referencePairEquiv m)

@[simp]
theorem finsetPairedShuffle_sign {m : Nat} (S : Finset (Fin (m + 2)))
    (hs : S.card = m) (hc : Sᶜ.card = 2) :
    Equiv.Perm.sign (finsetPairedShuffle S hs hc) = 1 := by
  simp [finsetPairedShuffle]

/-- Selected pairs, then their complement, interpreted in natural power coordinates. -/
def selectedAntiListing {m : Nat} (S : Finset (Fin (m + 2)))
    (hs : S.card = m) (hc : Sᶜ.card = 2) :
    Fin (2 * m) ⊕ Fin 4 ≃ Fin (2 * (m + 2)) :=
  (naturalPairDecode m).trans
    ((pairedColumnEquiv (selectedComplementPairEquiv S hs hc)).trans
      (antiDiagonalPairEquiv (m + 2)))

/-- The selected/complement column shuffle, now relative to the natural low/high split. -/
def naturalFinsetShuffle {m : Nat} (S : Finset (Fin (m + 2)))
    (hs : S.card = m) (hc : Sᶜ.card = 2) :
    Equiv.Perm (Fin (2 * m) ⊕ Fin 4) :=
  (selectedAntiListing S hs hc).trans (naturalPowerEquiv m).symm

/-- The `S`-dependent part of the natural shuffle; it only moves whole pairs. -/
def naturalPairTransition {m : Nat} (S : Finset (Fin (m + 2)))
    (hs : S.card = m) (hc : Sᶜ.card = 2) :
    Equiv.Perm (Fin (2 * m) ⊕ Fin 4) :=
  (naturalPairDecode m).symm.permCongr (finsetPairedShuffle S hs hc)

/-- The fixed natural-power to anti-pair shuffle. -/
def fixedAntiPowerShuffle (m : Nat) :
    Equiv.Perm (Fin (2 * m) ⊕ Fin 4) :=
  (naturalPowerEquiv m).symm.permCongr (antiPowerPerm (m + 2))

theorem naturalFinsetShuffle_eq_transition_fixed {m : Nat}
    (S : Finset (Fin (m + 2))) (hs : S.card = m) (hc : Sᶜ.card = 2) :
    naturalFinsetShuffle S hs hc =
      (naturalPairTransition S hs hc).trans (fixedAntiPowerShuffle m) := by
  ext x
  apply (naturalPowerEquiv m).injective
  simp only [naturalFinsetShuffle, selectedAntiListing, naturalPairTransition,
    fixedAntiPowerShuffle, Equiv.trans_apply, Equiv.permCongr_apply,
    Equiv.apply_symm_apply]
  rw [← referenceAdjacentEquiv_eq_naturalPowerEquiv m]
  simp only [referenceAdjacentEquiv, finsetPairedShuffle]
  simpa only [antiDiagonalPairEquiv, Equiv.trans_apply, Equiv.symm_symm,
    Equiv.apply_symm_apply] using (congrArg
    (fun z ↦ antiPowerPerm (m + 2) (pairColumnEquiv (m + 2) z))
    (pairedTransition_reference_apply
      (selectedComplementPairEquiv S hs hc) (referencePairEquiv m)
      (naturalPairDecode m x))).symm

/-- Both the `S`-dependent pair shuffle and the fixed anti-pair shuffle are even. -/
@[simp]
theorem naturalFinsetShuffle_sign {m : Nat} (S : Finset (Fin (m + 2)))
    (hs : S.card = m) (hc : Sᶜ.card = 2) :
    Equiv.Perm.sign (naturalFinsetShuffle S hs hc) = 1 := by
  rw [naturalFinsetShuffle_eq_transition_fixed]
  simp [naturalPairTransition, fixedAntiPowerShuffle]

/-! ### Natural-power matrices and their selected columns

The column convention in the next definitions is the one needed by the
Vandermonde factorization: the left summand is the natural low-power block
`0,1,...,2m-1`, and the right summand is the natural high-power block
`2m,...,2m+3`.  The inverse anti-diagonal equivalence converts each natural
power back to its pair label and side in the production wide matrix.
-/

/-- `X` with columns expressed in the natural low/high power split. -/
def naturalReindexedX {R : Type*} {m : Nat}
    (X : Fin (m + 2) → Fin (2 * m) → Fin 2 → R) :
    Matrix (Fin (2 * m)) (Fin (2 * m) ⊕ Fin 4) R :=
  (widePairMatrix X).submatrix id
    ((antiDiagonalPairEquiv (m + 2)).symm ∘ naturalPowerEquiv m)

/-- `Y` with columns expressed in the same natural low/high power split. -/
def naturalReindexedY {R : Type*} {m : Nat}
    (Y : Fin (m + 2) → Fin 4 → Fin 2 → R) :
    Matrix (Fin 4) (Fin (2 * m) ⊕ Fin 4) R :=
  (widePairMatrix (m := 2) Y).submatrix id
    ((antiDiagonalPairEquiv (m + 2)).symm ∘ naturalPowerEquiv m)

/-- On the selected branch, the natural shuffle gives exactly the production
sorted selected-pair column, including side order `0,1`. -/
theorem naturalFinsetShuffle_selectedColumn_left {m : Nat}
    (S : Finset (Fin (m + 2))) (hs : S.card = m) (hc : Sᶜ.card = 2)
    (col : Fin (2 * m)) :
    (antiDiagonalPairEquiv (m + 2)).symm
        (naturalPowerEquiv m (naturalFinsetShuffle S hs hc (Sum.inl col))) =
      selectedPairColumn (sortedPairVectorOfCard S hs) col := by
  simp [naturalFinsetShuffle, selectedAntiListing, naturalPairDecode,
    selectedPairColumn]
  rcases h : (pairColumnEquiv m).symm col with ⟨q, side⟩
  simp

/-- On the complementary branch, the same shuffle gives exactly the production
sorted complement-pair column, again in side order `0,1`. -/
theorem naturalFinsetShuffle_selectedColumn_right {m : Nat}
    (S : Finset (Fin (m + 2))) (hs : S.card = m) (hc : Sᶜ.card = 2)
    (col : Fin 4) :
    (antiDiagonalPairEquiv (m + 2)).symm
        (naturalPowerEquiv m (naturalFinsetShuffle S hs hc (Sum.inr col))) =
      selectedPairColumn (sortedPairVectorOfCard Sᶜ hc) col := by
  simp [naturalFinsetShuffle, selectedAntiListing, naturalPairDecode,
    selectedPairColumn]
  rcases h : (pairColumnEquiv 2).symm col with ⟨q, side⟩
  simp

/-- Selecting the left branch of the natural shuffle recovers the literal
production selected-pair matrix. -/
theorem naturalReindexedX_selected_left
    {R : Type*} {m : Nat}
    (X : Fin (m + 2) → Fin (2 * m) → Fin 2 → R)
    (S : Finset (Fin (m + 2))) (hs : S.card = m) (hc : Sᶜ.card = 2) :
    (naturalReindexedX X).submatrix id
        (naturalFinsetShuffle S hs hc ∘ Sum.inl) =
      selectedPairMatrix X (sortedPairVectorOfCard S hs) := by
  ext row col
  simp only [naturalReindexedX, Matrix.submatrix_apply, Function.comp_apply,
    widePairMatrix, selectedPairMatrix_apply]
  rw [naturalFinsetShuffle_selectedColumn_left S hs hc col]
  simp [selectedPairColumn]

/-- Selecting the right branch recovers the literal production matrix for the
sorted complementary pair set. -/
theorem naturalReindexedY_selected_right
    {R : Type*} {m : Nat}
    (Y : Fin (m + 2) → Fin 4 → Fin 2 → R)
    (S : Finset (Fin (m + 2))) (hs : S.card = m) (hc : Sᶜ.card = 2) :
    (naturalReindexedY Y).submatrix id
        (naturalFinsetShuffle S hs hc ∘ Sum.inr) =
      selectedPairMatrix Y (sortedPairVectorOfCard Sᶜ hc) := by
  ext row col
  simp only [naturalReindexedY, Matrix.submatrix_apply, Function.comp_apply,
    widePairMatrix, selectedPairMatrix_apply]
  rw [naturalFinsetShuffle_selectedColumn_right S hs hc col]
  simp [selectedPairColumn]

theorem fin_compl_card_eq_two {m : Nat} (S : Finset (Fin (m + 2)))
    (hs : S.card = m) : Sᶜ.card = 2 := by
  rw [Finset.card_compl, Fintype.card_fin, hs]
  omega

/-! ### Natural-split complementary minors

These are the adapters intended for the Colombo Vandermonde/kernel matrices.
Unlike the pair-reference lemmas below, their normalization hypotheses use the
natural power split: low powers `0..2m-1` form the square block `A`, while the
four high powers `2m..2m+3` form the identity block of the kernel.
-/

/-- Complementary paired minors from a normalization in natural power order. -/
theorem selectedPairDetFinset_complement_of_natural_normalized
    {R : Type*} [CommRing R] {m : Nat}
    (X : Fin (m + 2) → Fin (2 * m) → Fin 2 → R)
    (Y : Fin (m + 2) → Fin 4 → Fin 2 → R)
    (A : Matrix (Fin (2 * m)) (Fin (2 * m)) R)
    (C : Matrix (Fin 4) (Fin (2 * m)) R)
    (hX : naturalReindexedX X = A * normalizedTop C)
    (hY : naturalReindexedY Y = normalizedKernel C)
    (S : Finset (Fin (m + 2))) (hs : S.card = m) :
    selectedPairDetFinset X S =
      A.det * selectedPairDetFinset (m := 2) Y Sᶜ := by
  let hc : Sᶜ.card = 2 := fin_compl_card_eq_two S hs
  let e := naturalFinsetShuffle S hs hc
  have hXsel := naturalReindexedX_selected_left X S hs hc
  have hYsel := naturalReindexedY_selected_right Y S hs hc
  have hcomp := normalized_complementary_minor (R := R) C e
  have hesign : (Equiv.Perm.sign e : R) = 1 := by
    simp [e]
  rw [hesign, one_mul] at hcomp
  have hXmatrix : selectedPairMatrix X (sortedPairVectorOfCard S hs) =
      A * (normalizedTop C).submatrix id (e ∘ Sum.inl) := by
    rw [← hXsel, hX]
    ext i j
    rfl
  have hYmatrix : selectedPairMatrix Y (sortedPairVectorOfCard Sᶜ hc) =
      (normalizedKernel C).submatrix id (e ∘ Sum.inr) := by
    rw [← hYsel, hY]
  rw [selectedPairDetFinset_eq X S hs,
    selectedPairDetFinset_eq (m := 2) Y Sᶜ hc]
  simp only [selectedPairDet]
  rw [hXmatrix, hYmatrix, Matrix.det_mul, hcomp]

/-- The natural-split formula with the determinant scalar named `V`, matching
the conclusion expected by `P4Complement.hcompl`. -/
theorem selectedPairDetFinset_complement_of_natural_normalized_eq
    {R : Type*} [CommRing R] {m : Nat}
    (X : Fin (m + 2) → Fin (2 * m) → Fin 2 → R)
    (Y : Fin (m + 2) → Fin 4 → Fin 2 → R)
    (A : Matrix (Fin (2 * m)) (Fin (2 * m)) R)
    (C : Matrix (Fin 4) (Fin (2 * m)) R)
    (hX : naturalReindexedX X = A * normalizedTop C)
    (hY : naturalReindexedY Y = normalizedKernel C)
    (V : R) (hV : A.det = V)
    (S : Finset (Fin (m + 2))) (hs : S.card = m) :
    selectedPairDetFinset X S =
      V * selectedPairDetFinset (m := 2) Y Sᶜ := by
  rw [← hV]
  exact selectedPairDetFinset_complement_of_natural_normalized
    X Y A C hX hY S hs

/-- Exact quantified `hcompl` shape obtained from the natural low/high split. -/
theorem p4_hcompl_of_natural_normalized
    {R : Type*} [CommRing R] {m : Nat}
    (X : Fin (m + 2) → Fin (2 * m) → Fin 2 → R)
    (Y : Fin (m + 2) → Fin 4 → Fin 2 → R)
    (A : Matrix (Fin (2 * m)) (Fin (2 * m)) R)
    (C : Matrix (Fin 4) (Fin (2 * m)) R)
    (hX : naturalReindexedX X = A * normalizedTop C)
    (hY : naturalReindexedY Y = normalizedKernel C)
    (V : R) (hV : A.det = V) :
    ∀ S ∈ (Finset.univ : Finset (Fin (m + 2))).powersetCard m,
      selectedPairDetFinset X S =
        V * selectedPairDetFinset (m := 2) Y Sᶜ := by
  intro S hS
  exact selectedPairDetFinset_complement_of_natural_normalized_eq
    X Y A C hX hY V hV S (Finset.mem_powersetCard.mp hS).2

end ColomboGeneralK2
