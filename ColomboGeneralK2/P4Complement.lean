import ColomboGeneralK2.GeneralADMS

/-!
# Codimension-four complementary-minor reduction

This module packages the finite-set complement, inverse-weight, and `4 x 4`
Pfaffian bookkeeping needed after `recursivePf_pullback_fin`.

The complementary-minor identity remains an explicit hypothesis of
`p4_complement_reduction`.  Consequently its sign and normalization stay
visible at the API boundary rather than being hidden in a choice of column
order or a project-local assumption.
-/

namespace ColomboGeneralK2

variable {K : Type*} [Field K]

theorem recursivePf_two_eq_pfFour (A : Matrix (Fin 4) (Fin 4) K) :
    recursivePf 2 A = pfFour A := by
  simp [recursivePf, pfFour, Fin.sum_univ_succ]
  ring

theorem mem_powersetCard_compl {m : Nat} (S : Finset (Fin (m + 2))) :
    S ∈ (Finset.univ : Finset (Fin (m + 2))).powersetCard m ↔
      Sᶜ ∈ (Finset.univ : Finset (Fin (m + 2))).powersetCard 2 := by
  simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and]
  rw [Finset.card_compl]
  simp only [Fintype.card_fin]
  omega

theorem sum_powersetCard_compl {m : Nat}
    (f g : Finset (Fin (m + 2)) → K)
    (hfg : ∀ S ∈ (Finset.univ : Finset (Fin (m + 2))).powersetCard m,
      f S = g Sᶜ) :
    (∑ S ∈ (Finset.univ : Finset (Fin (m + 2))).powersetCard m, f S) =
      ∑ T ∈ (Finset.univ : Finset (Fin (m + 2))).powersetCard 2, g T := by
  apply Finset.sum_nbij' (fun S ↦ Sᶜ) (fun T ↦ Tᶜ)
  · intro S hS
    exact (mem_powersetCard_compl S).mp hS
  · intro T hT
    apply (mem_powersetCard_compl Tᶜ).mpr
    simpa using hT
  · intro S hS
    simp
  · intro T hT
    simp
  · exact hfg

theorem totalWeight_mul_invWeight_compl {m : Nat}
    (w : Fin (m + 2) → K) (hw : ∀ t, w t ≠ 0)
    (S : Finset (Fin (m + 2))) :
    (∏ t, w t) * (∏ t ∈ Sᶜ, (w t)⁻¹) = ∏ t ∈ S, w t := by
  rw [← Finset.prod_mul_prod_compl S w]
  rw [Finset.prod_inv_distrib]
  have hc : (∏ t ∈ Sᶜ, w t) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun t ht ↦ hw t
  rw [mul_assoc, mul_inv_cancel₀ hc, mul_one]

/--
Reduce the full anti-diagonal minor sum to a four-row Pfaffian, conditional on
an explicitly supplied complementary-minor identity.  The hypothesis `hcompl`
is the remaining application-specific bridge between the concrete `X` and `Y`
matrices; no such identity is assumed globally by this library.
-/
theorem p4_complement_reduction {m : Nat}
    (X : Fin (m + 2) → Fin (2 * m) → Fin 2 → K)
    (Y : Fin (m + 2) → Fin 4 → Fin 2 → K)
    (w : Fin (m + 2) → K) (hw : ∀ t, w t ≠ 0) (V : K)
    (hcompl : ∀ S ∈ (Finset.univ : Finset (Fin (m + 2))).powersetCard m,
      selectedPairDetFinset X S = V * selectedPairDetFinset (m := 2) Y Sᶜ) :
    recursivePf m (pullbackFinset X w Finset.univ) =
      V * (∏ t, w t) *
        pfFour (pullbackFinset (m := 2) Y (fun t ↦ (w t)⁻¹) Finset.univ) := by
  rw [recursivePf_pullback_fin]
  have hY :
      pfFour (pullbackFinset (m := 2) Y (fun t ↦ (w t)⁻¹) Finset.univ) =
        ∑ T ∈ (Finset.univ : Finset (Fin (m + 2))).powersetCard 2,
          (∏ t ∈ T, (w t)⁻¹) * selectedPairDetFinset (m := 2) Y T := by
    rw [← recursivePf_two_eq_pfFour]
    exact recursivePf_pullback_fin (m := 2) Y (fun t ↦ (w t)⁻¹)
  rw [hY]
  calc
    (∑ S ∈ (Finset.univ : Finset (Fin (m + 2))).powersetCard m,
        (∏ t ∈ S, w t) * selectedPairDetFinset X S) =
      ∑ T ∈ (Finset.univ : Finset (Fin (m + 2))).powersetCard 2,
        V * (∏ t, w t) *
          ((∏ t ∈ T, (w t)⁻¹) * selectedPairDetFinset (m := 2) Y T) := by
      apply sum_powersetCard_compl
      intro S hS
      rw [hcompl S hS]
      rw [← totalWeight_mul_invWeight_compl w hw S]
      ring
    _ = V * (∏ t, w t) *
        (∑ T ∈ (Finset.univ : Finset (Fin (m + 2))).powersetCard 2,
          (∏ t ∈ T, (w t)⁻¹) * selectedPairDetFinset (m := 2) Y T) := by
      rw [Finset.mul_sum]

end ColomboGeneralK2
