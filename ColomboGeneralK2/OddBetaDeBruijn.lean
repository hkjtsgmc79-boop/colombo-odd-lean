import ColomboGeneralK2.OddBetaIntegral
import ColomboGeneralK2.OddDeBruijnIntegral
import ColomboGeneralK2.OddOrderedChamber

/-!
# The arbitrary-r, arbitrary-m Beta--de Bruijn bridge

This file combines the scalar Beta identity, the labelled full-domain
de Bruijn theorem, and the strict permutation chamber.  All normalizations
remain explicit: `1 / m!` is cancelled only against the `m!` labelled
chambers, and the sole column shuffle contributes `groupingSign m`.
-/

namespace ColomboGeneralK2.Odd

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- The recursive Pfaffian is homogeneous of degree `m`. -/
theorem recursivePf_const_mul {R : Type*} [CommRing R] :
    ∀ (m : Nat) (c : R) (A : Matrix (Fin (2 * m)) (Fin (2 * m)) R),
      recursivePf m (fun i j ↦ c * A i j) = c ^ m * recursivePf m A := by
  intro m
  induction m with
  | zero =>
      intro c A
      simp [recursivePf]
  | succ n ih =>
      intro c A
      simp only [recursivePf]
      rw [pow_succ, Finset.mul_sum]
      apply Fintype.sum_congr
      intro k
      have hrec :
          recursivePf n
              (Matrix.submatrix
                ((fun i j ↦ c * A i j) :
                  Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) R)
                (fun i ↦ Fin.succ (k.succAbove i))
                (fun j ↦ Fin.succ (k.succAbove j))) =
            c ^ n * recursivePf n
              (A.submatrix
                (fun i ↦ Fin.succ (k.succAbove i))
                (fun j ↦ Fin.succ (k.succAbove j))) := by
        change recursivePf n
            (fun i j ↦ c *
              (A.submatrix
                (fun i ↦ Fin.succ (k.succAbove i))
                (fun j ↦ Fin.succ (k.succAbove j))) i j) = _
        exact ih c _
      rw [hrec]
      ring

/-- The scalar Beta identity solved for its moment integral. -/
theorem beta_moment_eq_inv_mul_powerDifference {m : Nat} (r : Nat)
    (x : Fin (2 * m) → Real) :
    (fun i j ↦ ∫ t, pairWedge (betaColumns r x) t i j) =
      fun i j ↦ (betaConstant r)⁻¹ *
        powerDifference x (2 * r + 1) i j := by
  funext i j
  change (∫ t, betaSkewKernel r x t i j) = _
  have hc : betaConstant r ≠ 0 := by
    simp only [betaConstant]
    positivity
  rw [beta_power_difference r x i j]
  field_simp

/-- Full labelled de Bruijn plus permutation invariance removes the
factorial and leaves exactly the strict ordered chamber. -/
theorem orderedChamber_debruijn {m : Nat}
    (Z : Real → Fin (2 * m) → Fin 2 → Real)
    (hZ : PairIntegrable volume Z) :
    groupingSign m *
        recursivePf m (fun i j ↦ ∫ t, pairWedge Z t i j) =
      ∫ t in orderedChamber m,
        (groupedPairMatrix Z t).det ∂tupleVolume m := by
  let f : (Fin m → Real) → Real := fun t ↦
    (selectedPairMatrix Z (List.Vector.ofFn t)).det
  have hf : Integrable f (tupleVolume m) := by
    simpa [f, selectedPairDet] using
      selectedPairDet_ofFn_integrable volume Z hZ
  have hinv : ∀ (σ : Equiv.Perm (Fin m)) (t : Fin m → Real),
      f (σ • t) = f t := by
    intro σ t
    exact selectedPairMatrix_det_smul Z t σ
  have hlabelled :
      (∫ t : Fin m → Real, f t ∂tupleVolume m) =
        (Nat.factorial m : Real) *
          ∫ t in orderedChamber m, f t ∂tupleVolume m :=
    integral_eq_factorial_mul_orderedChamber f hf hinv
  have hpf :
      recursivePf m (fun i j ↦ ∫ t, pairWedge Z t i j) =
        ∫ t in orderedChamber m, f t ∂tupleVolume m := by
    calc
      recursivePf m (fun i j ↦ ∫ t, pairWedge Z t i j) =
          fullDomainCoefficient m *
            ∫ t : Fin m → Real, f t ∂tupleVolume m := by
        simpa [f] using recursivePf_debruijn_full_domain volume Z hZ
      _ = fullDomainCoefficient m *
          ((Nat.factorial m : Real) *
            ∫ t in orderedChamber m, f t ∂tupleVolume m) := by
        rw [hlabelled]
      _ = ∫ t in orderedChamber m, f t ∂tupleVolume m := by
        simp only [fullDomainCoefficient]
        have hfac : (Nat.factorial m : Real) ≠ 0 := by positivity
        field_simp
  rw [hpf]
  calc
    groupingSign m *
        (∫ t in orderedChamber m, f t ∂tupleVolume m) =
        ∫ t in orderedChamber m, groupingSign m * f t ∂tupleVolume m := by
      rw [integral_const_mul]
    _ = ∫ t in orderedChamber m,
        (groupedPairMatrix Z t).det ∂tupleVolume m := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [groupedPairMatrix_det]
      rfl

/-- The frozen generic ordered-chamber target is now proved. -/
theorem orderedChamber_debruijn_target (m : Nat)
    (Z : Real → Fin (2 * m) → Fin 2 → Real) :
    OrderedChamberDeBruijnTarget m Z := by
  intro hZ
  exact orderedChamber_debruijn Z hZ

/-- Colombo's exact Beta specialization: the moment scaling contributes
`betaConstant r ^ m`, with no extra factorial or local sign. -/
theorem colombo_ordered_beta_debruijn {m : Nat} (r : Nat)
    (x : Fin (2 * m) → Real) :
    ColomboOrderedBetaDeBruijnTarget r x := by
  intro hZ
  have hordered := orderedChamber_debruijn (betaColumns r x) hZ
  rw [beta_moment_eq_inv_mul_powerDifference r x,
    recursivePf_const_mul] at hordered
  change groupingSign m * recursivePf m (powerDifference x (2 * r + 1)) =
    betaConstant r ^ m *
      ∫ t in orderedChamber m,
        (groupedPairMatrix (betaColumns r x) t).det ∂tupleVolume m
  have hc : betaConstant r ≠ 0 := by
    simp only [betaConstant]
    positivity
  have hpow : betaConstant r ^ m * (betaConstant r)⁻¹ ^ m = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hc, one_pow]
  calc
    groupingSign m * recursivePf m (powerDifference x (2 * r + 1)) =
        (betaConstant r ^ m * (betaConstant r)⁻¹ ^ m) *
          (groupingSign m *
            recursivePf m (powerDifference x (2 * r + 1))) := by
      rw [hpow, one_mul]
    _ = betaConstant r ^ m *
        (groupingSign m * ((betaConstant r)⁻¹ ^ m *
          recursivePf m (powerDifference x (2 * r + 1)))) := by
      ring
    _ = betaConstant r ^ m *
        ∫ t in orderedChamber m,
          (groupedPairMatrix (betaColumns r x) t).det ∂tupleVolume m :=
      congrArg (fun y : Real ↦ betaConstant r ^ m * y) hordered

/-- The Beta-column integrability proof discharges the specialization's
only analytic premise. -/
theorem colombo_ordered_beta_debruijn_unconditional {m : Nat} (r : Nat)
    (x : Fin (2 * m) → Real) :
    groupingSign m * recursivePf m (powerDifference x (2 * r + 1)) =
      betaConstant r ^ m *
        ∫ t in orderedChamber m,
          (groupedSplitMatrix r x t).det ∂tupleVolume m := by
  exact colombo_ordered_beta_debruijn r x (betaColumns_pairIntegrable r x)

end

end ColomboGeneralK2.Odd
