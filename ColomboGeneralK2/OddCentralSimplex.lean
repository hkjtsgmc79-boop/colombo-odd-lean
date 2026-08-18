import ColomboGeneralK2.OddMVP1Signatures
import ColomboGeneralK2.OddOrderedChamber
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Positive measure of the central ordered simplex

For a strictly increasing `2m`-tuple, the first and second halves are
separated by the open gap between rows `m-1` and `m`.  The central simplex
places an ordered `m`-tuple in that gap.  It is a nonempty open subset of
finite-dimensional Lebesgue space and therefore has positive product volume.
-/

namespace ColomboGeneralK2.Odd

open MeasureTheory

noncomputable section

/-- The central simplex is open in the finite real product topology. -/
theorem isOpen_centralSimplex {m : Nat} (x : Fin (2 * m) → Real) :
    IsOpen (centralSimplex x) := by
  cases m with
  | zero =>
      have h : centralSimplex x = Set.univ := by
        ext t
        simp [centralSimplex, StrictMono]
      rw [h]
      exact isOpen_univ
  | succ n =>
      have h : centralSimplex x =
          (⋂ q : Fin n,
            {t : Fin (n + 1) → Real | t q.castSucc < t q.succ}) ∩
          (⋂ i : Fin (n + 1), ⋂ q : Fin (n + 1),
            {t : Fin (n + 1) → Real |
              x (groupedColumnEquiv (n + 1) (Sum.inl i)) < t q}) ∩
          (⋂ i : Fin (n + 1), ⋂ q : Fin (n + 1),
            {t : Fin (n + 1) → Real |
              t q < x (groupedColumnEquiv (n + 1) (Sum.inr i))}) := by
        ext t
        simp only [centralSimplex, Set.mem_setOf_eq, Set.mem_inter_iff,
          Set.mem_iInter, Fin.strictMono_iff_lt_succ]
        aesop
      rw [h]
      apply IsOpen.inter
      · apply IsOpen.inter
        · exact isOpen_iInter_of_finite fun q : Fin n ↦
            isOpen_lt (continuous_apply q.castSucc) (continuous_apply q.succ)
        · exact isOpen_iInter_of_finite fun i ↦
            isOpen_iInter_of_finite fun q : Fin (n + 1) ↦
              isOpen_lt continuous_const (continuous_apply q)
      · exact isOpen_iInter_of_finite fun i ↦
          isOpen_iInter_of_finite fun q : Fin (n + 1) ↦
            isOpen_lt (continuous_apply q) continuous_const

/-- The first index of a provably nonempty finite ordinal. -/
def firstIndex {m : Nat} (hm : 0 < m) : Fin m := ⟨0, hm⟩

/-- The last index of a provably nonempty finite ordinal. -/
def lastIndex {m : Nat} (hm : 0 < m) : Fin m := ⟨m - 1, by omega⟩

@[simp] theorem firstIndex_val {m : Nat} (hm : 0 < m) :
    (firstIndex hm : Nat) = 0 := rfl

@[simp] theorem lastIndex_val {m : Nat} (hm : 0 < m) :
    (lastIndex hm : Nat) = m - 1 := rfl

/-- The two grouped halves of a strictly increasing row tuple have a strict
gap between their extreme entries. -/
theorem grouped_half_gap {m : Nat} (hm : 0 < m)
    {x : Fin (2 * m) → Real} (hx : StrictMono x) :
    x (groupedColumnEquiv m (Sum.inl (lastIndex hm))) <
      x (groupedColumnEquiv m (Sum.inr (firstIndex hm))) := by
  apply hx
  change ((groupedPairColumnEquiv m (Sum.inl (lastIndex hm)) :
      Fin (2 * m)) : Nat) <
    ((groupedPairColumnEquiv m (Sum.inr (firstIndex hm)) : Fin (2 * m)) : Nat)
  rw [groupedPairColumnEquiv_left_val, groupedPairColumnEquiv_right_val]
  simp
  omega

/-- An explicit evenly spaced tuple lies in the central simplex. -/
theorem centralSimplex_nonempty {m : Nat} (hm : 0 < m)
    {x : Fin (2 * m) → Real} (hx : StrictMono x) :
    (centralSimplex x).Nonempty := by
  let a := x (groupedColumnEquiv m (Sum.inl (lastIndex hm)))
  let b := x (groupedColumnEquiv m (Sum.inr (firstIndex hm)))
  have hab : a < b := grouped_half_gap hm hx
  let t : Fin m → Real := fun q ↦
    a + (((q : Nat) + 1 : Nat) : Real) / (m + 1 : Nat) * (b - a)
  refine ⟨t, ?_, ?_⟩
  · intro i j hij
    have hden : (0 : Real) < (m + 1 : Nat) := by positivity
    have hnum : (((i : Nat) + 1 : Nat) : Real) <
        (((j : Nat) + 1 : Nat) : Real) := by
      norm_cast
      omega
    dsimp [t]
    have hgap : 0 < b - a := sub_pos.mpr hab
    nlinarith [div_lt_div_of_pos_right hnum hden]
  · intro i q
    have hden : (0 : Real) < (m + 1 : Nat) := by positivity
    have hqpos : (0 : Real) < (((q : Nat) + 1 : Nat) : Real) := by positivity
    have hqle : (((q : Nat) + 1 : Nat) : Real) < (m + 1 : Nat) := by
      exact_mod_cast Nat.succ_lt_succ q.isLt
    have hcoefpos : 0 <
        ((((q : Nat) + 1 : Nat) : Real) / (m + 1 : Nat)) :=
      div_pos hqpos hden
    have hcoeflt :
        ((((q : Nat) + 1 : Nat) : Real) / (m + 1 : Nat)) < 1 := by
      simpa using div_lt_one hden |>.mpr hqle
    have hgap : 0 < b - a := sub_pos.mpr hab
    have hat : a < t q := by
      dsimp [t]
      nlinarith
    have htb : t q < b := by
      dsimp [t]
      nlinarith
    constructor
    · exact lt_of_le_of_lt (hx.monotone (by
        change ((groupedPairColumnEquiv m (Sum.inl i) : Fin (2 * m)) : Nat) ≤
          ((groupedPairColumnEquiv m (Sum.inl (lastIndex hm)) :
            Fin (2 * m)) : Nat)
        rw [groupedPairColumnEquiv_left_val, groupedPairColumnEquiv_left_val]
        simp
        omega)) hat
    · exact lt_of_lt_of_le htb (hx.monotone (by
        change ((groupedPairColumnEquiv m (Sum.inr (firstIndex hm)) :
            Fin (2 * m)) : Nat) ≤
          ((groupedPairColumnEquiv m (Sum.inr i) : Fin (2 * m)) : Nat)
        rw [groupedPairColumnEquiv_right_val, groupedPairColumnEquiv_right_val]
        simp))

/-- The central simplex has positive finite product Lebesgue measure. -/
theorem tupleVolume_centralSimplex_pos {m : Nat} (hm : 0 < m)
    {x : Fin (2 * m) → Real} (hx : StrictMono x) :
    0 < tupleVolume m (centralSimplex x) := by
  change 0 < (Measure.pi fun _ : Fin m ↦ (volume : Measure Real))
    (centralSimplex x)
  rw [← volume_pi]
  exact (isOpen_centralSimplex x).measure_pos volume
    (centralSimplex_nonempty hm hx)

/-- A full-domain integrable function which is nonnegative on the ordered
chamber and strictly positive on the central simplex has strictly positive
ordered-chamber integral. -/
theorem orderedChamber_integral_pos_of_central {m : Nat} (hm : 0 < m)
    {x : Fin (2 * m) → Real} (hx : StrictMono x)
    (f : (Fin m → Real) → Real)
    (hf : Integrable f (tupleVolume m))
    (hnonneg : ∀ t ∈ orderedChamber m, 0 ≤ f t)
    (hstrict : ∀ t ∈ centralSimplex x, 0 < f t) :
    0 < ∫ t in orderedChamber m, f t ∂tupleVolume m := by
  have hae :
      0 ≤ᵐ[(tupleVolume m).restrict (orderedChamber m)] f := by
    filter_upwards [ae_restrict_mem (measurableSet_orderedChamber m)] with t ht
    exact hnonneg t ht
  apply (setIntegral_pos_iff_support_of_nonneg_ae hae hf.integrableOn).2
  refine lt_of_lt_of_le (tupleVolume_centralSimplex_pos hm hx)
    (measure_mono ?_)
  intro t ht
  exact ⟨(hstrict t ht).ne', ht.1⟩

end

end ColomboGeneralK2.Odd
