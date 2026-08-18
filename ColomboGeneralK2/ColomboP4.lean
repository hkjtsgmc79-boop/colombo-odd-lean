import ColomboGeneralK2.P4Complement
import ColomboGeneralK2.VandermondeKernel

/-!
# The concrete codimension-four reduction for Colombo's odd powers

This module connects the natural-power complementary-minor theorem to the
Vandermonde power matrix and its four-row polynomial kernel.  It records both
the normalized kernel identity and the raw coefficient-kernel identity; the
latter is valid because the normalizing row operation has determinant one.
-/

open scoped BigOperators

open Finset Matrix

namespace ColomboGeneralK2.VandermondeKernel

variable {K : Type*} [Field K]

noncomputable section

/-- The concrete anti-diagonal column formula agrees, value by value, with
the equivalence used by the abstract natural-power shuffle. -/
theorem pairedColumn_val_eq_abstract (m : Nat) (t : Fin (m + 2))
    (side : Fin 2) :
    (pairedColumn m t side : Nat) =
      (ColomboGeneralK2.antiDiagonalPairEquiv (m + 2) (t, side) : Nat) := by
  fin_cases side
  · change (pairedColumn m t 0 : Nat) =
      (ColomboGeneralK2.antiDiagonalPairEquiv (m + 2) (t, 0) : Nat)
    simpa [pairedColumn] using
      (ColomboGeneralK2.antiDiagonalPairEquiv_left_value t).symm
  · change (pairedColumn m t 1 : Nat) =
      (ColomboGeneralK2.antiDiagonalPairEquiv (m + 2) (t, 1) : Nat)
    rw [ColomboGeneralK2.antiDiagonalPairEquiv_right_value]
    simp only [pairedColumn_one]
    omega

/-- The abstract natural reindexing of the concrete power pairs is the
literal natural low/high power matrix. -/
theorem naturalReindexedX_Xpair (m : Nat) (x : Fin (2 * m) → K) :
    ColomboGeneralK2.naturalReindexedX (Xpair m x) =
      naturalPowerMatrix m x := by
  ext row col
  simp only [ColomboGeneralK2.naturalReindexedX,
    ColomboGeneralK2.widePairMatrix, Matrix.submatrix_apply, id_eq,
    Function.comp_apply, Xpair, naturalPowerMatrix]
  let p := (ColomboGeneralK2.antiDiagonalPairEquiv (m + 2)).symm
    (ColomboGeneralK2.naturalPowerEquiv m col)
  change powerMatrix m x row (pairedColumn m p.1 p.2) =
    powerMatrix m x row (naturalColumnEquiv m col)
  congr 1
  apply Fin.ext
  rw [pairedColumn_val_eq_abstract]
  have hp := (ColomboGeneralK2.antiDiagonalPairEquiv (m + 2)).apply_symm_apply
    (ColomboGeneralK2.naturalPowerEquiv m col)
  change ((ColomboGeneralK2.antiDiagonalPairEquiv (m + 2) p :
    Fin (2 * (m + 2))) : Nat) = _
  rw [hp]
  rcases col with (col | col)
  · rfl
  · rfl

/-- The same reindexing identifies the concrete normalized kernel pairs with
the literal natural low/high normalized kernel matrix. -/
theorem naturalReindexedY_normalizedYpair (m : Nat)
    (x : Fin (2 * m) → K) :
    ColomboGeneralK2.naturalReindexedY (normalizedYpair m x) =
      naturalNormalizedKernelMatrix m x := by
  ext row col
  simp only [ColomboGeneralK2.naturalReindexedY,
    ColomboGeneralK2.widePairMatrix, Matrix.submatrix_apply, id_eq,
    Function.comp_apply, normalizedYpair, naturalNormalizedKernelMatrix]
  let p := (ColomboGeneralK2.antiDiagonalPairEquiv (m + 2)).symm
    (ColomboGeneralK2.naturalPowerEquiv m col)
  change normalizedKernelMatrix m x row (pairedColumn m p.1 p.2) =
    normalizedKernelMatrix m x row (naturalColumnEquiv m col)
  congr 1
  apply Fin.ext
  rw [pairedColumn_val_eq_abstract]
  have hp := (ColomboGeneralK2.antiDiagonalPairEquiv (m + 2)).apply_symm_apply
    (ColomboGeneralK2.naturalPowerEquiv m col)
  change ((ColomboGeneralK2.antiDiagonalPairEquiv (m + 2) p :
    Fin (2 * (m + 2))) : Nat) = _
  rw [hp]
  rcases col with (col | col)
  · rfl
  · rfl

/-- Concrete `hX` for the natural complementary-minor theorem. -/
theorem naturalReindexedX_Xpair_normalized (m : Nat)
    (x : Fin (2 * m) → K) :
    ColomboGeneralK2.naturalReindexedX (Xpair m x) =
      vandermondeBlock m x *
        ColomboGeneralK2.normalizedTop (kernelLowBlock m x) := by
  rw [naturalReindexedX_Xpair]
  exact naturalPowerMatrix_eq_mul_normalizedTop m x

/-- Concrete `hY` for the natural complementary-minor theorem. -/
theorem naturalReindexedY_normalizedYpair_normalized (m : Nat)
    (x : Fin (2 * m) → K) :
    ColomboGeneralK2.naturalReindexedY (normalizedYpair m x) =
      ColomboGeneralK2.normalizedKernel (kernelLowBlock m x) := by
  rw [naturalReindexedY_normalizedYpair]
  exact naturalNormalizedKernelMatrix_eq_normalizedKernel m x

/-! ## Concrete complementary minors -/

/-- The complementary-minor identity for the row-normalized coefficient
kernel.  The scalar is exactly the Vandermonde product, with positive sign. -/
theorem normalizedYpair_hcompl (m : Nat) (x : Fin (2 * m) → K) :
    ∀ S ∈ (Finset.univ : Finset (Fin (m + 2))).powersetCard m,
      ColomboGeneralK2.selectedPairDetFinset (Xpair m x) S =
        vandermondeProduct m x *
          ColomboGeneralK2.selectedPairDetFinset (m := 2)
            (normalizedYpair m x) Sᶜ := by
  exact ColomboGeneralK2.p4_hcompl_of_natural_normalized
    (Xpair m x) (normalizedYpair m x)
    (vandermondeBlock m x) (kernelLowBlock m x)
    (naturalReindexedX_Xpair_normalized m x)
    (naturalReindexedY_normalizedYpair_normalized m x)
    (vandermondeProduct m x) (det_vandermondeBlock m x)

/-- Row normalization has determinant one, so the same complementary-minor
identity holds for the raw coefficient rows, in the same sign convention. -/
theorem rawYpair_hcompl (m : Nat) (x : Fin (2 * m) → K) :
    ∀ S ∈ (Finset.univ : Finset (Fin (m + 2))).powersetCard m,
      ColomboGeneralK2.selectedPairDetFinset (Xpair m x) S =
        vandermondeProduct m x *
          ColomboGeneralK2.selectedPairDetFinset (m := 2)
            (rawYpair m x) Sᶜ := by
  intro S hS
  simpa only [selectedPairDetFinset_normalizedYpair_eq_rawYpair] using
    normalizedYpair_hcompl m x S hS

/-- Every weighted four-row Pfaffian is unchanged when the coefficient-kernel
rows are normalized by the determinant-one high block. -/
theorem pfFour_pullback_normalizedYpair_eq_rawYpair (m : Nat)
    (x : Fin (2 * m) → K) (w : Fin (m + 2) → K) :
    ColomboGeneralK2.pfFour
        (ColomboGeneralK2.pullbackFinset (m := 2) (normalizedYpair m x) w
          Finset.univ) =
      ColomboGeneralK2.pfFour
        (ColomboGeneralK2.pullbackFinset (m := 2) (rawYpair m x) w
          Finset.univ) := by
  rw [← ColomboGeneralK2.recursivePf_two_eq_pfFour,
    ← ColomboGeneralK2.recursivePf_two_eq_pfFour,
    ColomboGeneralK2.recursivePf_pullback_fin,
    ColomboGeneralK2.recursivePf_pullback_fin]
  apply Finset.sum_congr rfl
  intro S hS
  rw [selectedPairDetFinset_normalizedYpair_eq_rawYpair]

/-- Concrete P4 reduction for arbitrary nonzero pair weights, stated with the
raw coefficient kernel. -/
theorem p4_raw_of_weight_ne_zero (m : Nat) (x : Fin (2 * m) → K)
    (w : Fin (m + 2) → K) (hw : ∀ t, w t ≠ 0) :
    ColomboGeneralK2.recursivePf m
        (ColomboGeneralK2.pullbackFinset (Xpair m x) w Finset.univ) =
      vandermondeProduct m x * (∏ t, w t) *
        ColomboGeneralK2.pfFour
          (ColomboGeneralK2.pullbackFinset (m := 2) (rawYpair m x)
            (fun t ↦ (w t)⁻¹) Finset.univ) := by
  exact ColomboGeneralK2.p4_complement_reduction
    (Xpair m x) (rawYpair m x) w hw (vandermondeProduct m x)
    (rawYpair_hcompl m x)

/-! ## Colombo's odd binomial weights -/

/-- The concrete Colombo P4 identity, conditional only on nonvanishing of the
anti-diagonal binomial weights. -/
theorem colomboP4_of_weight_ne_zero (m : Nat) (x : Fin (2 * m) → K)
    (hw : ∀ t, binomialWeight (K := K) m t ≠ 0) :
    ColomboGeneralK2.recursivePf m
        (fun i j ↦ (x j - x i) ^ (2 * m + 3)) =
      vandermondeProduct m x *
        (∏ t, binomialWeight (K := K) m t) *
          ColomboGeneralK2.pfFour
            (ColomboGeneralK2.pullbackFinset (m := 2) (rawYpair m x)
              (fun t ↦ (binomialWeight (K := K) m t)⁻¹) Finset.univ) := by
  rw [← pullbackFinset_Xpair_binomialWeight m x]
  exact p4_raw_of_weight_ne_zero m x (binomialWeight m) hw

/-- In characteristic zero every relevant binomial coefficient, hence every
anti-diagonal weight, is nonzero. -/
theorem binomialWeight_ne_zero [CharZero K] (m : Nat) (t : Fin (m + 2)) :
    binomialWeight (K := K) m t ≠ 0 := by
  apply mul_ne_zero
  · exact pow_ne_zero _ (by simp)
  · exact Nat.cast_ne_zero.mpr (Nat.choose_ne_zero (by omega))

/-- Characteristic-zero form of `colomboP4_of_weight_ne_zero`, with no
remaining weight hypothesis. -/
theorem colomboP4 [CharZero K] (m : Nat) (x : Fin (2 * m) → K) :
    ColomboGeneralK2.recursivePf m
        (fun i j ↦ (x j - x i) ^ (2 * m + 3)) =
      vandermondeProduct m x *
        (∏ t, binomialWeight (K := K) m t) *
          ColomboGeneralK2.pfFour
            (ColomboGeneralK2.pullbackFinset (m := 2) (rawYpair m x)
              (fun t ↦ (binomialWeight (K := K) m t)⁻¹) Finset.univ) := by
  exact colomboP4_of_weight_ne_zero m x (binomialWeight_ne_zero m)

end

end ColomboGeneralK2.VandermondeKernel
