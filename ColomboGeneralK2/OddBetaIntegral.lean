import ColomboGeneralK2.OddDeBruijnAnalyticTargets
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

namespace ColomboGeneralK2.Odd

open MeasureTheory
open scoped BigOperators

noncomputable section

private theorem beta_kernel_as_indicator (r : Nat) {a b t : Real} (_hab : a < b) :
    truncPow r (t - a) * truncPow r (b - t) =
      Set.indicator (Set.Ioo a b) (fun u : Real => (u - a) ^ r * (b - u) ^ r) t := by
  by_cases ht : t ∈ Set.Ioo a b
  · rw [Set.indicator_of_mem ht]
    rw [truncPow_of_pos (by linarith [ht.1]), truncPow_of_pos (by linarith [ht.2])]
  · rw [Set.indicator_of_notMem ht]
    by_cases hta : t ≤ a
    · rw [truncPow_of_nonpos (by linarith)]
      simp
    · have hat : a < t := lt_of_not_ge hta
      have hbt : b ≤ t := le_of_not_gt (fun htb => ht ⟨hat, htb⟩)
      have hzero : truncPow r (b - t) = 0 := truncPow_of_nonpos (by linarith)
      rw [hzero]
      simp

private theorem beta_kernel_as_indicator_eq_zero (r : Nat) {a b t : Real} (hba : b ≤ a) :
    truncPow r (t - a) * truncPow r (b - t) = 0 := by
  by_cases hta : t ≤ a
  · rw [truncPow_of_nonpos (by linarith)]
    simp
  · have hat : a < t := lt_of_not_ge hta
    have hbt : b - t ≤ 0 := by linarith
    rw [truncPow_of_nonpos hbt]
    simp

private theorem beta_kernel_integrable (r : Nat) (a b : Real) :
    Integrable (fun t => truncPow r (t - a) * truncPow r (b - t)) := by
  rcases lt_or_ge a b with hab | hba
  · let g : Real → Real := fun t => (t - a) ^ r * (b - t) ^ r
    have hg : IntegrableOn g (Set.Ioo a b) := by
      apply ((continuous_id.sub continuous_const).pow r).mul
        ((continuous_const.sub continuous_id).pow r) |>.continuousOn.integrableOn_Icc
        |>.mono_set Set.Ioo_subset_Icc_self
    have hfg : (fun t => truncPow r (t - a) * truncPow r (b - t)) =
        Set.indicator (Set.Ioo a b) g := by
      funext t
      exact beta_kernel_as_indicator r hab
    rw [hfg]
    exact hg.integrable_indicator measurableSet_Ioo
  · have hz : (fun t => truncPow r (t - a) * truncPow r (b - t)) = fun _ => 0 := by
      funext t
      exact beta_kernel_as_indicator_eq_zero r hba
    rw [hz]
    exact integrable_zero Real Real volume

/-- The paired truncated-power columns satisfy the entrywise integrability
hypothesis used by the arbitrary-size de Bruijn theorem. -/
theorem betaColumns_pairIntegrable {m : Nat} (r : Nat)
    (x : Fin (2 * m) → Real) :
    PairIntegrable volume (betaColumns r x) := by
  intro i j
  simpa [betaColumns, leftKernel, rightKernel] using
    beta_kernel_integrable r (x i) (x j)

private theorem beta_interval (r : Nat) {d : Real} (hd : 0 < d) :
    (∫ t in 0..d, t ^ r * (d - t) ^ r) =
      ((Nat.factorial r : Real) ^ 2 / Nat.factorial (2 * r + 1)) * d ^ (2 * r + 1) := by
  have h := Complex.betaIntegral_scaled ((r + 1 : Nat) : Complex)
    ((r + 1 : Nat) : Complex) hd
  have h₁ : ((r + 1 : Nat) : Complex) - 1 = (r : Complex) := by
    push_cast
    ring
  have h₂ : ((r + 1 : Nat) : Complex) + ((r + 1 : Nat) : Complex) - 1 =
      ((2 * r + 1 : Nat) : Complex) := by
    push_cast
    ring
  rw [h₁, h₂] at h
  simp only [Complex.cpow_natCast] at h
  have h' :
      (∫ t in 0..d, (t : Complex) ^ r * ((d : Complex) - t) ^ r) =
        (d : Complex) ^ (2 * r + 1) *
          Complex.betaIntegral ((r + 1 : Nat) : Complex) ((r + 1 : Nat) : Complex) := h
  have hr : 0 < (((r + 1 : Nat) : Complex)).re := by
    norm_cast
    omega
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ hr hr] at h'
  have hgamr : Complex.Gamma ((r + 1 : Nat) : Complex) = (Nat.factorial r : Complex) := by
    convert Complex.Gamma_nat_eq_factorial r using 1
    all_goals norm_num
  have hgam2 :
      Complex.Gamma (((r + 1 : Nat) : Complex) + ((r + 1 : Nat) : Complex)) =
        (Nat.factorial (2 * r + 1) : Complex) := by
    convert Complex.Gamma_nat_eq_factorial (2 * r + 1) using 1
    all_goals push_cast
    all_goals ring_nf
  rw [hgamr, hgam2] at h'
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  calc
    (∫ t in 0..d, ↑(t ^ r * (d - t) ^ r) : Complex) =
        ∫ t in 0..d, (t : Complex) ^ r * ((d : Complex) - t) ^ r := by
      apply intervalIntegral.integral_congr
      intro t _
      push_cast
      rfl
    _ =
        (d : Complex) ^ (2 * r + 1) *
          ((Nat.factorial r : Complex) * Nat.factorial r / Nat.factorial (2 * r + 1)) := h'
    _ = ↑(((Nat.factorial r : Real) ^ 2 / Nat.factorial (2 * r + 1)) * d ^ (2 * r + 1)) := by
      push_cast
      ring

private theorem beta_kernel_integral (r : Nat) {a b : Real} (hab : a < b) :
    (∫ t, truncPow r (t - a) * truncPow r (b - t)) =
      ((Nat.factorial r : Real) ^ 2 / Nat.factorial (2 * r + 1)) * (b - a) ^ (2 * r + 1) := by
  let g : Real → Real := fun t => (t - a) ^ r * (b - t) ^ r
  have hfg : (fun t => truncPow r (t - a) * truncPow r (b - t)) =
      Set.indicator (Set.Ioo a b) g := by
    funext t
    exact beta_kernel_as_indicator r hab
  rw [hfg, integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hab.le]
  have hshift : (∫ t in 0..b - a, g (t + a)) = ∫ t in 0 + a..(b - a) + a, g t :=
    intervalIntegral.integral_comp_add_right g a
  calc
    (∫ t in a..b, g t) = ∫ t in 0..b - a, g (t + a) := by
      convert hshift.symm using 1
      all_goals ring_nf
    _ = ((Nat.factorial r : Real) ^ 2 / Nat.factorial (2 * r + 1)) *
        (b - a) ^ (2 * r + 1) := by
      dsimp [g]
      convert beta_interval r (sub_pos.mpr hab) using 1
      · apply intervalIntegral.integral_congr
        intro t _
        ring

/-- The scalar Beta reduction for the odd power-difference kernel.

The first truncated-power product contributes on `x i < x j`, the second on
`x j < x i`; their relative minus sign is exactly what turns the latter case
into the odd power `(x j - x i)^(2*r+1)`. -/
theorem beta_power_difference {m : Nat} (r : Nat) (x : Fin (2 * m) → Real)
    (i j : Fin (2 * m)) :
    powerDifference x (2 * r + 1) i j =
      betaConstant r * ∫ t, betaSkewKernel r x t i j := by
  simp only [powerDifference, betaSkewKernel, leftKernel, rightKernel]
  have hleft := beta_kernel_integrable r (x i) (x j)
  have hright : Integrable
      (fun t => truncPow r (x i - t) * truncPow r (t - x j)) := by
    simpa [mul_comm] using beta_kernel_integrable r (x j) (x i)
  rw [integral_sub hleft hright]
  have hswap :
      (∫ t, truncPow r (x i - t) * truncPow r (t - x j)) =
        ∫ t, truncPow r (t - x j) * truncPow r (x i - t) := by
    apply integral_congr_ae
    filter_upwards [] with t
    exact mul_comm _ _
  rw [hswap]
  rcases lt_trichotomy (x i) (x j) with hij | hij | hji
  · have hzero :
        (fun t => truncPow r (t - x j) * truncPow r (x i - t)) = fun _ => 0 := by
        funext t
        exact beta_kernel_as_indicator_eq_zero r hij.le
    rw [beta_kernel_integral r hij, hzero, integral_zero]
    rw [betaConstant]
    field_simp [Nat.factorial_ne_zero]
    ring
  · rw [hij]
    simp [mul_comm]
  · have hzero :
        (fun t => truncPow r (t - x i) * truncPow r (x j - t)) = fun _ => 0 := by
        funext t
        exact beta_kernel_as_indicator_eq_zero r hji.le
    rw [hzero, integral_zero, beta_kernel_integral r hji]
    have hodd : Odd (2 * r + 1) := odd_two_mul_add_one r
    rw [show x j - x i = -(x i - x j) by ring, neg_pow, hodd.neg_one_pow]
    rw [betaConstant]
    field_simp [Nat.factorial_ne_zero]
    ring

end

end ColomboGeneralK2.Odd
