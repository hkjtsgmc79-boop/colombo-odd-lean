import ColomboGeneralK2.ComplementaryMinor
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Polynomial.Basic

/-!
# The concrete Vandermonde kernel used by the Colombo `k = 2` reduction

This module proves the concrete elementary half of the complementary-minor
argument.  For `2 * m` roots, `powerMatrix x` has columns indexed by the
powers `0, ..., 2 * m + 3`.  The four rows of `rawKernelMatrix x` are the
coefficient vectors of

`F, X * F, X^2 * F, X^3 * F`,

where `F = ∏ i, (X - C (x i))`.

The raw high-degree `4 x 4` block is unit lower triangular, not literally the
identity.  A normalized kernel matrix with identity high block is defined at
the end of the file.
-/

open scoped BigOperators

open Finset Matrix Polynomial

namespace ColomboGeneralK2.VandermondeKernel

variable {K : Type*} [Field K]

noncomputable section

/-- The `2m x (2m+4)` matrix whose `(i,j)` entry is `x_i^j`. -/
def powerMatrix (m : Nat) (x : Fin (2 * m) → K) :
    Matrix (Fin (2 * m)) (Fin (2 * m + 4)) K :=
  fun i j ↦ x i ^ (j : Nat)

/-- The monic polynomial with the prescribed (labelled) roots. -/
def rootPolynomial (m : Nat) (x : Fin (2 * m) → K) : K[X] :=
  ∏ i : Fin (2 * m), (X - C (x i))

/-- The polynomial `X^a F`, for `0 ≤ a < 4`. -/
def shiftedRootPolynomial (m : Nat) (x : Fin (2 * m) → K) (a : Fin 4) : K[X] :=
  X ^ (a : Nat) * rootPolynomial m x

/-- Coefficient rows of `F, XF, X^2F, X^3F`, in increasing degree order. -/
def rawKernelMatrix (m : Nat) (x : Fin (2 * m) → K) :
    Matrix (Fin 4) (Fin (2 * m + 4)) K :=
  fun a j ↦ (shiftedRootPolynomial m x a).coeff (j : Nat)

/-- Embed the first `2m` columns into all `2m+4` power columns. -/
def lowColumn (m : Nat) : Fin (2 * m) → Fin (2 * m + 4) :=
  Fin.castLE (Nat.le_add_right (2 * m) 4)

/-- Embed the four high-degree columns `2m, ..., 2m+3`. -/
def highColumn (m : Nat) (a : Fin 4) : Fin (2 * m + 4) :=
  ⟨2 * m + a, by omega⟩

/-- The first `2m` columns are literally mathlib's Vandermonde matrix. -/
theorem powerMatrix_lowBlock (m : Nat) (x : Fin (2 * m) → K) :
    (powerMatrix m x).submatrix id (lowColumn m) = Matrix.vandermonde x := by
  ext i j
  rfl

/-- Consequently, the leading square minor has the standard Vandermonde product. -/
theorem det_powerMatrix_lowBlock (m : Nat) (x : Fin (2 * m) → K) :
    ((powerMatrix m x).submatrix id (lowColumn m)).det =
      ∏ i : Fin (2 * m), ∏ j ∈ Finset.Ioi i, (x j - x i) := by
  rw [powerMatrix_lowBlock, Matrix.det_vandermonde]

theorem rootPolynomial_monic (m : Nat) (x : Fin (2 * m) → K) :
    (rootPolynomial m x).Monic := by
  classical
  simp only [rootPolynomial]
  exact monic_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C (x i)

@[simp]
theorem rootPolynomial_natDegree (m : Nat) (x : Fin (2 * m) → K) :
    (rootPolynomial m x).natDegree = 2 * m := by
  classical
  simp [rootPolynomial]

@[simp]
theorem rootPolynomial_eval_root (m : Nat) (x : Fin (2 * m) → K)
    (i : Fin (2 * m)) :
    (rootPolynomial m x).eval (x i) = 0 := by
  classical
  simp only [rootPolynomial, Polynomial.eval_prod, eval_sub, eval_X, eval_C]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

@[simp]
theorem shiftedRootPolynomial_eval_root (m : Nat) (x : Fin (2 * m) → K)
    (a : Fin 4) (i : Fin (2 * m)) :
    (shiftedRootPolynomial m x a).eval (x i) = 0 := by
  simp [shiftedRootPolynomial, Polynomial.eval_mul]

theorem shiftedRootPolynomial_monic (m : Nat) (x : Fin (2 * m) → K)
    (a : Fin 4) :
    (shiftedRootPolynomial m x a).Monic := by
  exact (monic_X_pow (a : Nat)).mul (rootPolynomial_monic m x)

theorem shiftedRootPolynomial_natDegree_lt (m : Nat) (x : Fin (2 * m) → K)
    (a : Fin 4) :
    (shiftedRootPolynomial m x a).natDegree < 2 * m + 4 := by
  rw [shiftedRootPolynomial, natDegree_X_pow_mul]
  · simp only [rootPolynomial_natDegree]
    omega
  · exact (rootPolynomial_monic m x).ne_zero

/-- Every root row annihilates every coefficient row. -/
theorem powerMatrix_mul_rawKernelMatrix_transpose (m : Nat)
    (x : Fin (2 * m) → K) :
    powerMatrix m x * (rawKernelMatrix m x)ᵀ = 0 := by
  ext i a
  rw [Matrix.mul_apply]
  change (∑ j : Fin (2 * m + 4),
    x i ^ (j : Nat) * (shiftedRootPolynomial m x a).coeff (j : Nat)) = 0
  simp_rw [mul_comm (x i ^ (_ : Nat))]
  have hpdeg : shiftedRootPolynomial m x a ∈ Polynomial.degreeLT K (2 * m + 4) :=
    Polynomial.mem_degreeLT.mpr <|
      (natDegree_lt_iff_degree_lt (shiftedRootPolynomial_monic m x a).ne_zero).mp
        (shiftedRootPolynomial_natDegree_lt m x a)
  have heval := Polynomial.eval_eq_sum_degreeLTEquiv hpdeg (x i)
  simpa [Polynomial.degreeLTEquiv, shiftedRootPolynomial_eval_root] using heval.symm

/-- The high-degree `4 x 4` block of the raw coefficient matrix. -/
def rawHighBlock (m : Nat) (x : Fin (2 * m) → K) : Matrix (Fin 4) (Fin 4) K :=
  (rawKernelMatrix m x).submatrix id (highColumn m)

/-- The raw high block has ones on its diagonal. -/
@[simp]
theorem rawHighBlock_diagonal (m : Nat) (x : Fin (2 * m) → K) (a : Fin 4) :
    rawHighBlock m x a a = 1 := by
  rw [rawHighBlock, Matrix.submatrix_apply]
  simp only [id_eq, rawKernelMatrix, shiftedRootPolynomial, highColumn]
  rw [coeff_X_pow_mul']
  split_ifs with h
  · have hsub : 2 * m + (a : Nat) - (a : Nat) = 2 * m := by omega
    rw [hsub, ← rootPolynomial_natDegree m x]
    exact (rootPolynomial_monic m x).coeff_natDegree
  · exfalso
    apply h
    omega

/-- Entries strictly above the diagonal of the raw high block vanish. -/
theorem rawHighBlock_above (m : Nat) (x : Fin (2 * m) → K)
    {a b : Fin 4} (hab : a < b) :
    rawHighBlock m x a b = 0 := by
  rw [rawHighBlock, Matrix.submatrix_apply]
  simp only [id_eq, rawKernelMatrix, shiftedRootPolynomial, highColumn]
  rw [coeff_X_pow_mul']
  split_ifs with h
  · apply coeff_eq_zero_of_natDegree_lt
    rw [rootPolynomial_natDegree]
    omega
  · rfl

/-- Thus the true raw high block is unit lower triangular. -/
theorem rawHighBlock_lowerTriangular (m : Nat) (x : Fin (2 * m) → K) :
    (rawHighBlock m x).BlockTriangular OrderDual.toDual := by
  intro a b hab
  exact rawHighBlock_above m x hab

/-- The only determinant fact needed from the high block is `det = 1`. -/
@[simp]
theorem det_rawHighBlock (m : Nat) (x : Fin (2 * m) → K) :
    (rawHighBlock m x).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (rawHighBlock_lowerTriangular m x)]
  simp

/-- Row-normalize the raw kernel basis so that its high block becomes `I₄`. -/
def normalizedKernelMatrix (m : Nat) (x : Fin (2 * m) → K) :
    Matrix (Fin 4) (Fin (2 * m + 4)) K :=
  (rawHighBlock m x)⁻¹ * rawKernelMatrix m x

/-- The normalized rows still lie in the kernel of the power matrix. -/
theorem powerMatrix_mul_normalizedKernelMatrix_transpose (m : Nat)
    (x : Fin (2 * m) → K) :
    powerMatrix m x * (normalizedKernelMatrix m x)ᵀ = 0 := by
  rw [normalizedKernelMatrix, Matrix.transpose_mul, ← Matrix.mul_assoc,
    powerMatrix_mul_rawKernelMatrix_transpose]
  simp

/-- The promised identity high block holds after, and only after, row normalization. -/
theorem normalizedKernelMatrix_highBlock (m : Nat) (x : Fin (2 * m) → K) :
    (normalizedKernelMatrix m x).submatrix id (highColumn m) = 1 := by
  rw [normalizedKernelMatrix,
    Matrix.submatrix_mul _ _ id (Equiv.refl (Fin 4)) (highColumn m)
      (Equiv.refl (Fin 4)).bijective]
  simp only [Matrix.submatrix_id_id, Equiv.coe_refl]
  change (rawHighBlock m x)⁻¹ * rawHighBlock m x = 1
  exact Matrix.nonsing_inv_mul _ (by simp)

/-- Row normalization preserves every `4 x 4` selected-column determinant. -/
theorem det_normalizedKernelMatrix_submatrix (m : Nat) (x : Fin (2 * m) → K)
    (cols : Fin 4 → Fin (2 * m + 4)) :
    ((normalizedKernelMatrix m x).submatrix id cols).det =
      ((rawKernelMatrix m x).submatrix id cols).det := by
  rw [normalizedKernelMatrix,
    Matrix.submatrix_mul _ _ id (Equiv.refl (Fin 4)) cols
      (Equiv.refl (Fin 4)).bijective]
  simp only [Matrix.submatrix_id_id, Equiv.coe_refl, Matrix.det_mul,
    Matrix.det_nonsing_inv, det_rawHighBlock, Ring.inverse_one, one_mul]

/-! ## Anti-diagonal pair wrappers -/

/-- Column pair `t` consists of the powers `t` and `2m+3-t`. -/
def pairedColumn (m : Nat) (t : Fin (m + 2)) (side : Fin 2) : Fin (2 * m + 4) :=
  if side = 0 then
    ⟨t, by omega⟩
  else
    ⟨2 * m + 3 - t, by omega⟩

@[simp]
theorem pairedColumn_zero (m : Nat) (t : Fin (m + 2)) :
    pairedColumn m t 0 = ⟨t, by omega⟩ := by
  simp [pairedColumn]

@[simp]
theorem pairedColumn_one (m : Nat) (t : Fin (m + 2)) :
    pairedColumn m t 1 = ⟨2 * m + 3 - t, by omega⟩ := by
  simp [pairedColumn]

theorem pairedColumn_injective (m : Nat) :
    Function.Injective
      (fun p : Fin (m + 2) × Fin 2 ↦ pairedColumn m p.1 p.2) := by
  rintro ⟨t, side⟩ ⟨u, side'⟩ h
  have hside : side = side' := by
    apply Fin.ext
    fin_cases side <;> fin_cases side' <;>
      simp [pairedColumn] at h ⊢ <;> omega
  subst side'
  have ht : t = u := by
    apply Fin.ext
    fin_cases side <;> simp [pairedColumn] at h ⊢ <;> omega
  exact Prod.ext ht rfl

theorem pairedColumn_surjective (m : Nat) :
    Function.Surjective
      (fun p : Fin (m + 2) × Fin 2 ↦ pairedColumn m p.1 p.2) := by
  intro j
  by_cases hj : (j : Nat) < m + 2
  · refine ⟨(⟨j, hj⟩, 0), ?_⟩
    apply Fin.ext
    simp [pairedColumn]
  · refine ⟨(⟨2 * m + 3 - (j : Nat), by omega⟩, 1), ?_⟩
    apply Fin.ext
    simp [pairedColumn]
    omega

theorem pairedColumn_bijective (m : Nat) :
    Function.Bijective
      (fun p : Fin (m + 2) × Fin 2 ↦ pairedColumn m p.1 p.2) :=
  ⟨pairedColumn_injective m, pairedColumn_surjective m⟩

/-- Reindex all `2m+4` columns as the `m+2` anti-diagonal pairs. -/
def antiDiagonalPairEquiv (m : Nat) :
    Fin (m + 2) × Fin 2 ≃ Fin (2 * m + 4) :=
  Equiv.ofBijective
    (fun p : Fin (m + 2) × Fin 2 ↦ pairedColumn m p.1 p.2)
    (pairedColumn_bijective m)

theorem sum_antiDiagonalPairs (m : Nat) (f : Fin (2 * m + 4) → K) :
    (∑ j : Fin (2 * m + 4), f j) =
      ∑ t : Fin (m + 2), (f (pairedColumn m t 0) + f (pairedColumn m t 1)) := by
  rw [← (antiDiagonalPairEquiv m).sum_comp f]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, antiDiagonalPairEquiv, Equiv.ofBijective_apply]

/-- The power matrix exposed in anti-diagonal two-column blocks. -/
def Xpair (m : Nat) (x : Fin (2 * m) → K) :
    Fin (m + 2) → Fin (2 * m) → Fin 2 → K :=
  fun t row side ↦ powerMatrix m x row (pairedColumn m t side)

/-- The raw coefficient kernel exposed in the same two-column blocks. -/
def rawYpair (m : Nat) (x : Fin (2 * m) → K) :
    Fin (m + 2) → Fin 4 → Fin 2 → K :=
  fun t row side ↦ rawKernelMatrix m x row (pairedColumn m t side)

/-- The normalized coefficient kernel exposed in the same two-column blocks. -/
def normalizedYpair (m : Nat) (x : Fin (2 * m) → K) :
    Fin (m + 2) → Fin 4 → Fin 2 → K :=
  fun t row side ↦ normalizedKernelMatrix m x row (pairedColumn m t side)

/-- The anti-diagonal binomial weight attached to pair `t`. -/
def binomialWeight (m : Nat) (t : Fin (m + 2)) : K :=
  (-1 : K) ^ (t : Nat) * (Nat.choose (2 * m + 3) (t : Nat) : K)

theorem neg_one_pow_antiDiagonal_complement (m : Nat) (t : Fin (m + 2)) :
    (-1 : K) ^ (2 * m + 3 - (t : Nat)) = -((-1 : K) ^ (t : Nat)) := by
  have ht : (t : Nat) ≤ 2 * m + 3 := by omega
  have hsq :
      (-1 : K) ^ (t : Nat) * (-1 : K) ^ (t : Nat) = 1 := by
    rw [← pow_add, (Even.add_self (t : Nat)).neg_one_pow]
  have hodd : Odd (2 * m + 3) := ⟨m + 1, by omega⟩
  calc
    (-1 : K) ^ (2 * m + 3 - (t : Nat)) =
        (-1 : K) ^ (2 * m + 3 - (t : Nat)) * 1 := by rw [mul_one]
    _ = (-1 : K) ^ (2 * m + 3 - (t : Nat)) *
          (((-1 : K) ^ (t : Nat)) * ((-1 : K) ^ (t : Nat))) := by rw [hsq]
    _ = (((-1 : K) ^ (2 * m + 3 - (t : Nat))) *
          ((-1 : K) ^ (t : Nat))) * ((-1 : K) ^ (t : Nat)) := by ring
    _ = (-1 : K) ^ (2 * m + 3) * ((-1 : K) ^ (t : Nat)) := by
      rw [← pow_add, Nat.sub_add_cancel ht]
    _ = -((-1 : K) ^ (t : Nat)) := by rw [hodd.neg_one_pow]; ring

/-- The odd binomial theorem grouped into anti-diagonal column pairs. -/
theorem paired_binomial_theorem (m : Nat) (a b : K) :
    (∑ t : Fin (m + 2), binomialWeight m t *
      (a ^ (t : Nat) * b ^ (2 * m + 3 - (t : Nat)) -
        a ^ (2 * m + 3 - (t : Nat)) * b ^ (t : Nat))) =
      (b - a) ^ (2 * m + 3) := by
  let summand : Fin (2 * m + 4) → K := fun j ↦
    (-a) ^ (j : Nat) * b ^ (2 * m + 3 - (j : Nat)) *
      (Nat.choose (2 * m + 3) (j : Nat) : K)
  calc
    (∑ t : Fin (m + 2), binomialWeight m t *
      (a ^ (t : Nat) * b ^ (2 * m + 3 - (t : Nat)) -
        a ^ (2 * m + 3 - (t : Nat)) * b ^ (t : Nat))) =
        ∑ j : Fin (2 * m + 4), summand j := by
      rw [sum_antiDiagonalPairs]
      apply Fintype.sum_congr
      intro t
      have ht : (t : Nat) ≤ 2 * m + 3 := by omega
      simp only [summand, pairedColumn_zero, pairedColumn_one]
      rw [neg_pow a (t : Nat),
        neg_pow a (2 * m + 3 - (t : Nat)),
        neg_one_pow_antiDiagonal_complement,
        Nat.sub_sub_self ht, Nat.choose_symm ht]
      simp only [binomialWeight]
      ring
    _ = (b - a) ^ (2 * m + 3) := by
      have hbin := add_pow (-a) b (2 * m + 3)
      rw [show -a + b = b - a by ring] at hbin
      rw [← Fin.sum_univ_eq_sum_range] at hbin
      simpa [summand, show 2 * m + 3 + 1 = 2 * m + 4 by omega] using hbin.symm

@[simp]
theorem pairWedge_Xpair (m : Nat) (x : Fin (2 * m) → K)
    (t : Fin (m + 2)) (i j : Fin (2 * m)) :
    ColomboGeneralK2.pairWedge (Xpair m x) t i j =
      x i ^ (t : Nat) * x j ^ (2 * m + 3 - (t : Nat)) -
        x i ^ (2 * m + 3 - (t : Nat)) * x j ^ (t : Nat) := by
  simp [ColomboGeneralK2.pairWedge, Xpair, powerMatrix]

/-- The concrete anti-diagonal pullback is the Colombo difference-power matrix. -/
theorem pullbackFinset_Xpair_binomialWeight (m : Nat) (x : Fin (2 * m) → K) :
    ColomboGeneralK2.pullbackFinset (Xpair m x) (binomialWeight m)
        (Finset.univ : Finset (Fin (m + 2))) =
      fun i j ↦ (x j - x i) ^ (2 * m + 3) := by
  ext i j
  simpa [ColomboGeneralK2.pullbackFinset] using
    paired_binomial_theorem m (x i) (x j)

/-- The four concrete columns selected by an ordered vector of two pairs. -/
def selectedPairedColumn (m : Nat) (pairs : List.Vector (Fin (m + 2)) 2) :
    Fin 4 → Fin (2 * m + 4) :=
  fun col ↦
    let qside := (ColomboGeneralK2.pairColumnEquiv 2).symm col
    pairedColumn m (pairs.get qside.1) qside.2

theorem selectedPairMatrix_rawYpair (m : Nat) (x : Fin (2 * m) → K)
    (pairs : List.Vector (Fin (m + 2)) 2) :
    ColomboGeneralK2.selectedPairMatrix (rawYpair m x) pairs =
      (rawKernelMatrix m x).submatrix id (selectedPairedColumn m pairs) := by
  ext row col
  simp [ColomboGeneralK2.selectedPairMatrix, rawYpair, selectedPairedColumn]

theorem selectedPairMatrix_normalizedYpair (m : Nat) (x : Fin (2 * m) → K)
    (pairs : List.Vector (Fin (m + 2)) 2) :
    ColomboGeneralK2.selectedPairMatrix (normalizedYpair m x) pairs =
      (normalizedKernelMatrix m x).submatrix id (selectedPairedColumn m pairs) := by
  ext row col
  simp [ColomboGeneralK2.selectedPairMatrix, normalizedYpair, selectedPairedColumn]

/-- Every selected two-pair minor is unchanged by normalizing the `Y` rows. -/
theorem selectedPairDet_normalizedYpair_eq_rawYpair (m : Nat)
    (x : Fin (2 * m) → K) (pairs : List.Vector (Fin (m + 2)) 2) :
    ColomboGeneralK2.selectedPairDet (normalizedYpair m x) pairs =
      ColomboGeneralK2.selectedPairDet (rawYpair m x) pairs := by
  rw [ColomboGeneralK2.selectedPairDet, ColomboGeneralK2.selectedPairDet,
    selectedPairMatrix_normalizedYpair, selectedPairMatrix_rawYpair]
  exact det_normalizedKernelMatrix_submatrix m x (selectedPairedColumn m pairs)

/-- The `Finset`-indexed two-pair minor API used by the complementary-minor
theorem is likewise invariant under row normalization. -/
theorem selectedPairDetFinset_normalizedYpair_eq_rawYpair (m : Nat)
    (x : Fin (2 * m) → K) (S : Finset (Fin (m + 2))) :
    ColomboGeneralK2.selectedPairDetFinset (m := 2) (normalizedYpair m x) S =
      ColomboGeneralK2.selectedPairDetFinset (m := 2) (rawYpair m x) S := by
  rw [ColomboGeneralK2.selectedPairDetFinset,
    ColomboGeneralK2.selectedPairDetFinset]
  split_ifs
  · exact selectedPairDet_normalizedYpair_eq_rawYpair m x _
  · rfl

/-! ## Natural low/high block coordinates -/

/-- The natural column split: powers `< 2m`, followed by the four high powers. -/
abbrev LowHighIndex (m : Nat) := Fin (2 * m) ⊕ Fin 4

/-- Unlike the anti-diagonal pair order, this is the ordinary low/high order. -/
def naturalColumnEquiv (m : Nat) : LowHighIndex m ≃ Fin (2 * m + 4) :=
  finSumFinEquiv

@[simp]
theorem naturalColumnEquiv_inl (m : Nat) (j : Fin (2 * m)) :
    naturalColumnEquiv m (Sum.inl j) = lowColumn m j := by
  apply Fin.ext
  rfl

@[simp]
theorem naturalColumnEquiv_inr (m : Nat) (j : Fin 4) :
    naturalColumnEquiv m (Sum.inr j) = highColumn m j := by
  apply Fin.ext
  rfl

/-- Horizontal concatenation with a sum-typed column index. -/
def horizontalBlocks {rows low high : Type*}
    (L : Matrix rows low K) (H : Matrix rows high K) :
    Matrix rows (low ⊕ high) K :=
  fun i col ↦ Sum.elim (L i) (H i) col

omit [Field K] in
@[simp]
theorem horizontalBlocks_inl {rows low high : Type*}
    (L : Matrix rows low K) (H : Matrix rows high K) (i : rows) (j : low) :
    horizontalBlocks L H i (Sum.inl j) = L i j :=
  rfl

omit [Field K] in
@[simp]
theorem horizontalBlocks_inr {rows low high : Type*}
    (L : Matrix rows low K) (H : Matrix rows high K) (i : rows) (j : high) :
    horizontalBlocks L H i (Sum.inr j) = H i j :=
  rfl

theorem mul_horizontalBlocks {rows mid low high : Type*}
    [Fintype mid] (M : Matrix rows mid K)
    (L : Matrix mid low K) (H : Matrix mid high K) :
    M * horizontalBlocks L H = horizontalBlocks (M * L) (M * H) := by
  ext i (j | j) <;> rfl

theorem horizontalBlocks_mul_transpose {rows rows' low high : Type*}
    [Fintype low] [Fintype high]
    (A : Matrix rows low K) (B : Matrix rows high K)
    (C : Matrix rows' low K) (D : Matrix rows' high K) :
    horizontalBlocks A B * (horizontalBlocks C D)ᵀ =
      A * Cᵀ + B * Dᵀ := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, horizontalBlocks,
    Fintype.sum_sum_type, Matrix.add_apply, Sum.elim_inl, Sum.elim_inr]

/-- The power matrix in natural low/high column coordinates. -/
def naturalPowerMatrix (m : Nat) (x : Fin (2 * m) → K) :
    Matrix (Fin (2 * m)) (LowHighIndex m) K :=
  (powerMatrix m x).submatrix id (naturalColumnEquiv m)

/-- The normalized kernel matrix in the same natural coordinates. -/
def naturalNormalizedKernelMatrix (m : Nat) (x : Fin (2 * m) → K) :
    Matrix (Fin 4) (LowHighIndex m) K :=
  (normalizedKernelMatrix m x).submatrix id (naturalColumnEquiv m)

/-- The square low-power block `A`. -/
def vandermondeBlock (m : Nat) (x : Fin (2 * m) → K) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) K :=
  (powerMatrix m x).submatrix id (lowColumn m)

/-- The high-power block `B` before deriving `B = -A Cᵀ`. -/
def highPowerBlock (m : Nat) (x : Fin (2 * m) → K) :
    Matrix (Fin (2 * m)) (Fin 4) K :=
  (powerMatrix m x).submatrix id (highColumn m)

/-- The low block `C` of the normalized kernel basis. -/
def kernelLowBlock (m : Nat) (x : Fin (2 * m) → K) :
    Matrix (Fin 4) (Fin (2 * m)) K :=
  (normalizedKernelMatrix m x).submatrix id (lowColumn m)

theorem vandermondeBlock_eq (m : Nat) (x : Fin (2 * m) → K) :
    vandermondeBlock m x = Matrix.vandermonde x :=
  powerMatrix_lowBlock m x

def vandermondeProduct (m : Nat) (x : Fin (2 * m) → K) : K :=
  ∏ i : Fin (2 * m), ∏ j ∈ Finset.Ioi i, (x j - x i)

theorem det_vandermondeBlock (m : Nat) (x : Fin (2 * m) → K) :
    (vandermondeBlock m x).det = vandermondeProduct m x :=
  det_powerMatrix_lowBlock m x

theorem naturalPowerMatrix_blocks (m : Nat) (x : Fin (2 * m) → K) :
    naturalPowerMatrix m x =
      horizontalBlocks (vandermondeBlock m x) (highPowerBlock m x) := by
  ext i (j | j) <;>
    simp [naturalPowerMatrix, vandermondeBlock, highPowerBlock]

theorem naturalNormalizedKernelMatrix_blocks (m : Nat)
    (x : Fin (2 * m) → K) :
    naturalNormalizedKernelMatrix m x =
      horizontalBlocks (kernelLowBlock m x) 1 := by
  ext i (j | j)
  · simp [naturalNormalizedKernelMatrix, kernelLowBlock]
  · change normalizedKernelMatrix m x i (highColumn m j) =
      (1 : Matrix (Fin 4) (Fin 4) K) i j
    exact congrFun (congrFun (normalizedKernelMatrix_highBlock m x) i) j

theorem naturalPower_mul_normalizedKernel_transpose (m : Nat)
    (x : Fin (2 * m) → K) :
    naturalPowerMatrix m x * (naturalNormalizedKernelMatrix m x)ᵀ = 0 := by
  ext i j
  have h := congrFun (congrFun
    (powerMatrix_mul_normalizedKernelMatrix_transpose m x) i) j
  rw [Matrix.mul_apply] at h ⊢
  simp only [Matrix.transpose_apply, Matrix.zero_apply] at h ⊢
  rw [← (naturalColumnEquiv m).sum_comp
    (fun k ↦ powerMatrix m x i k * normalizedKernelMatrix m x j k)] at h
  simpa [naturalPowerMatrix, naturalNormalizedKernelMatrix,
    Matrix.transpose_apply] using h

/-- Orthogonality forces the high block to be `-A Cᵀ`. -/
theorem highPowerBlock_eq_neg_mul_transpose (m : Nat)
    (x : Fin (2 * m) → K) :
    highPowerBlock m x =
      -(vandermondeBlock m x * (kernelLowBlock m x)ᵀ) := by
  have h := naturalPower_mul_normalizedKernel_transpose m x
  rw [naturalPowerMatrix_blocks, naturalNormalizedKernelMatrix_blocks,
    horizontalBlocks_mul_transpose] at h
  simp only [Matrix.transpose_one, Matrix.mul_one] at h
  exact eq_neg_of_add_eq_zero_right h

/-- `X = A * [I, -Cᵀ]` in the natural low/high column order. -/
theorem naturalPowerMatrix_factorization (m : Nat) (x : Fin (2 * m) → K) :
    naturalPowerMatrix m x =
      vandermondeBlock m x *
        horizontalBlocks (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) K)
          (-(kernelLowBlock m x)ᵀ) := by
  rw [naturalPowerMatrix_blocks, mul_horizontalBlocks]
  simp only [Matrix.mul_one, Matrix.mul_neg]
  rw [highPowerBlock_eq_neg_mul_transpose]

/-! ### Adapters to the abstract complementary-minor normal form -/

/-- The concrete factorization is definitionally the abstract
`A * normalizedTop C` normal form from `HComplAbstract`. -/
theorem naturalPowerMatrix_eq_mul_normalizedTop (m : Nat)
    (x : Fin (2 * m) → K) :
    naturalPowerMatrix m x =
      vandermondeBlock m x *
        ColomboGeneralK2.normalizedTop (kernelLowBlock m x) := by
  rw [naturalPowerMatrix_factorization]
  rfl

/-- The concrete normalized kernel is exactly the abstract `[C,I]` matrix. -/
theorem naturalNormalizedKernelMatrix_eq_normalizedKernel (m : Nat)
    (x : Fin (2 * m) → K) :
    naturalNormalizedKernelMatrix m x =
      ColomboGeneralK2.normalizedKernel (kernelLowBlock m x) := by
  rw [naturalNormalizedKernelMatrix_blocks]
  rfl

/-- A concrete witness that the unnormalized high block need not be `I₄`. -/
theorem rawHighBlock_not_always_one :
    rawHighBlock (K := ℚ) 1 (fun i : Fin 2 ↦ if i = 0 then 0 else 1) 1 0 = -1 := by
  simp [rawHighBlock, rawKernelMatrix, shiftedRootPolynomial, rootPolynomial,
    highColumn, Fin.prod_univ_succ]

end

end ColomboGeneralK2.VandermondeKernel
