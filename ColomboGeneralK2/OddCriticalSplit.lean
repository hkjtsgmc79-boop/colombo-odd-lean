import ColomboGeneralK2.OddCriticalTieFree
import ColomboGeneralK2.OddPairedSplitLimit
import Mathlib.Data.Finset.Sort

/-!
# The arbitrary paired critical split determinant

The tie-free two-fan theorem is first transferred to arbitrary strictly
ordered, cross-family-distinct knot lists by sorting their disjoint union.
The remaining cross-family coincidences are then removed by a common positive
shift of the right knot list and recovered by continuity.
-/

namespace ColomboGeneralK2.Odd

open Filter
open scoped BigOperators Topology

noncomputable section

/-- No knot in the left family coincides with a knot in the right family. -/
def CrossFamilyDistinct {m : Nat} (s u : Fin m → Real) : Prop :=
  ∀ i j, s i ≠ u j

/-- A wrapper preventing the pre-existing lexicographic order on `Sum` from
interfering with the value-induced order used to sort the merged knots. -/
private structure SortedKnotLabel (m : Nat) where
  val : Fin m ⊕ Fin m
deriving DecidableEq, Fintype

private def sortedKnotLabelEquiv (m : Nat) :
    (Fin m ⊕ Fin m) ≃ SortedKnotLabel m where
  toFun := SortedKnotLabel.mk
  invFun := SortedKnotLabel.val
  left_inv _ := rfl
  right_inv _ := rfl

private theorem sumElim_injective_of_crossFamilyDistinct {m : Nat}
    {s u : Fin m → Real} (hs : StrictMono s) (hu : StrictMono u)
    (hcross : CrossFamilyDistinct s u) :
    Function.Injective (Sum.elim s u) := by
  intro a b hab
  cases a with
  | inl i =>
      cases b with
      | inl j =>
          simp only [Sum.elim_inl] at hab
          exact congrArg Sum.inl (hs.injective hab)
      | inr j =>
          simp only [Sum.elim_inl, Sum.elim_inr] at hab
          exact (hcross i j hab).elim
  | inr i =>
      cases b with
      | inl j =>
          simp only [Sum.elim_inr, Sum.elim_inl] at hab
          exact (hcross j i hab.symm).elim
      | inr j =>
          simp only [Sum.elim_inr] at hab
          exact congrArg Sum.inr (hu.injective hab)

private def anchorRadius {m : Nat} (x : Fin (2 * m) → Real)
    (s u : Fin m → Real) : Real :=
  ∑ i, |s i| + ∑ j, |u j| + ∑ k, |x k| + 1

private theorem abs_lt_anchorRadius_s {m : Nat} (x : Fin (2 * m) → Real)
    (s u : Fin m → Real) (i : Fin m) :
    |s i| < anchorRadius x s u := by
  have hi : |s i| ≤ ∑ j, |s j| :=
    Finset.single_le_sum (fun j _ ↦ abs_nonneg (s j)) (Finset.mem_univ i)
  have hu0 : 0 ≤ ∑ j, |u j| := Finset.sum_nonneg (fun j _ ↦ abs_nonneg (u j))
  have hx0 : 0 ≤ ∑ k, |x k| := Finset.sum_nonneg (fun k _ ↦ abs_nonneg (x k))
  unfold anchorRadius
  linarith

private theorem abs_lt_anchorRadius_u {m : Nat} (x : Fin (2 * m) → Real)
    (s u : Fin m → Real) (i : Fin m) :
    |u i| < anchorRadius x s u := by
  have hi : |u i| ≤ ∑ j, |u j| :=
    Finset.single_le_sum (fun j _ ↦ abs_nonneg (u j)) (Finset.mem_univ i)
  have hs0 : 0 ≤ ∑ j, |s j| := Finset.sum_nonneg (fun j _ ↦ abs_nonneg (s j))
  have hx0 : 0 ≤ ∑ k, |x k| := Finset.sum_nonneg (fun k _ ↦ abs_nonneg (x k))
  unfold anchorRadius
  linarith

private theorem abs_lt_anchorRadius_x {m : Nat} (x : Fin (2 * m) → Real)
    (s u : Fin m → Real) (i : Fin (2 * m)) :
    |x i| < anchorRadius x s u := by
  have hi : |x i| ≤ ∑ k, |x k| :=
    Finset.single_le_sum (fun k _ ↦ abs_nonneg (x k)) (Finset.mem_univ i)
  have hs0 : 0 ≤ ∑ j, |s j| := Finset.sum_nonneg (fun j _ ↦ abs_nonneg (s j))
  have hu0 : 0 ≤ ∑ j, |u j| := Finset.sum_nonneg (fun j _ ↦ abs_nonneg (u j))
  unfold anchorRadius
  linarith

/-- Sort two cross-family-distinct knot lists into genuine two-fan data. -/
private noncomputable def twoFanDataOfDistinct {m : Nat}
    (hm : 3 ≤ m) (x : Fin (2 * m) → Real) (s u : Fin m → Real)
    (hs : StrictMono s) (hu : StrictMono u) (hpair : Paired s u)
    (hcross : CrossFamilyDistinct s u) : TwoFanData m := by
  have hf0 : Function.Injective (Sum.elim s u) :=
    sumElim_injective_of_crossFamilyDistinct hs hu hcross
  let f : SortedKnotLabel m → Real := fun a ↦ Sum.elim s u a.val
  have hf : Function.Injective f := by
    intro a b hab
    cases a with
    | mk a =>
      cases b with
      | mk b =>
        exact congrArg SortedKnotLabel.mk (hf0 hab)
  letI : LinearOrder (SortedKnotLabel m) := LinearOrder.lift' f hf
  let e : Fin (2 * m) ≃o SortedKnotLabel m :=
    Fintype.orderIsoFinOfCardEq (SortedKnotLabel m) (k := 2 * m) (by
      simpa [two_mul] using
        (Fintype.card_congr (sortedKnotLabelEquiv m).symm))
  refine
    { hm := by omega
      merge :=
        { rank := (sortedKnotLabelEquiv m).trans e.symm.toEquiv
          left_strict := ?_
          right_strict := ?_
          paired := ?_ }
      z := fun q ↦ f (e q)
      z_strict := ?_
      leftAnchor := -anchorRadius x s u
      rightAnchor := anchorRadius x s u
      leftAnchor_lt := ?_
      lt_rightAnchor := ?_ }
  · intro i j hij
    apply e.symm.strictMono
    change s i < s j
    exact hs hij
  · intro i j hij
    apply e.symm.strictMono
    change u i < u j
    exact hu hij
  · intro j
    apply e.symm.strictMono
    change s j < u j
    exact hpair j
  · intro a b hab
    change f (e a) < f (e b)
    exact e.strictMono hab
  · intro q
    have hs0 : 0 ≤ ∑ i, |s i| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
    have hu0 : 0 ≤ ∑ i, |u i| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
    have hx0 : 0 ≤ ∑ i, |x i| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
    have hR : |f (e q)| < anchorRadius x s u := by
      cases hq : (e q).val with
      | inl i =>
        have hi : |s i| ≤ ∑ j, |s j| :=
          Finset.single_le_sum (fun j _ ↦ abs_nonneg (s j)) (Finset.mem_univ i)
        have hfe : f (e q) = s i := by simp [f, hq]
        rw [hfe]
        unfold anchorRadius
        linarith
      | inr i =>
        have hi : |u i| ≤ ∑ j, |u j| :=
          Finset.single_le_sum (fun j _ ↦ abs_nonneg (u j)) (Finset.mem_univ i)
        have hfe : f (e q) = u i := by simp [f, hq]
        rw [hfe]
        unfold anchorRadius
        linarith
    exact lt_of_lt_of_le (neg_lt_neg hR) (neg_abs_le _)
  · intro q
    have hs0 : 0 ≤ ∑ i, |s i| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
    have hu0 : 0 ≤ ∑ i, |u i| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
    have hx0 : 0 ≤ ∑ i, |x i| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
    have hR : |f (e q)| < anchorRadius x s u := by
      cases hq : (e q).val with
      | inl i =>
        have hi : |s i| ≤ ∑ j, |s j| :=
          Finset.single_le_sum (fun j _ ↦ abs_nonneg (s j)) (Finset.mem_univ i)
        have hfe : f (e q) = s i := by simp [f, hq]
        rw [hfe]
        unfold anchorRadius
        linarith
      | inr i =>
        have hi : |u i| ≤ ∑ j, |u j| :=
          Finset.single_le_sum (fun j _ ↦ abs_nonneg (u j)) (Finset.mem_univ i)
        have hfe : f (e q) = u i := by simp [f, hq]
        rw [hfe]
        unfold anchorRadius
        linarith
    exact lt_of_le_of_lt (le_abs_self _) hR

private theorem twoFanDataOfDistinct_s {m : Nat}
    (hm : 3 ≤ m) (x : Fin (2 * m) → Real) (s u : Fin m → Real)
    (hs : StrictMono s) (hu : StrictMono u) (hpair : Paired s u)
    (hcross : CrossFamilyDistinct s u) :
    (twoFanDataOfDistinct hm x s u hs hu hpair hcross).s = s := by
  funext i
  simp [twoFanDataOfDistinct, TwoFanData.s, TwoFanData.alpha,
    sortedKnotLabelEquiv]

private theorem twoFanDataOfDistinct_u {m : Nat}
    (hm : 3 ≤ m) (x : Fin (2 * m) → Real) (s u : Fin m → Real)
    (hs : StrictMono s) (hu : StrictMono u) (hpair : Paired s u)
    (hcross : CrossFamilyDistinct s u) :
    (twoFanDataOfDistinct hm x s u hs hu hpair hcross).u = u := by
  funext i
  simp [twoFanDataOfDistinct, TwoFanData.u, TwoFanData.beta,
    sortedKnotLabelEquiv]

private theorem twoFanDataOfDistinct_samplesInside {m : Nat}
    (hm : 3 ≤ m) (x : Fin (2 * m) → Real) (s u : Fin m → Real)
    (hs : StrictMono s) (hu : StrictMono u) (hpair : Paired s u)
    (hcross : CrossFamilyDistinct s u) :
    SamplesInsideAnchors (twoFanDataOfDistinct hm x s u hs hu hpair hcross) x := by
  intro i
  change -anchorRadius x s u < x i ∧ x i < anchorRadius x s u
  have h := abs_lt_anchorRadius_x x s u i
  exact ⟨lt_of_lt_of_le (neg_lt_neg h) (neg_abs_le (x i)),
    lt_of_le_of_lt (le_abs_self (x i)) h⟩

/-- The critical split determinant is nonnegative when the two knot families
are also distinct from one another. -/
theorem criticalSplitDet_distinct_nonneg {m : Nat} (hm : 3 ≤ m)
    {x : Fin (2 * m) → Real} {s u : Fin m → Real}
    (hx : StrictMono x) (hs : StrictMono s) (hu : StrictMono u)
    (hpair : Paired s u) (hcross : CrossFamilyDistinct s u) :
    0 ≤ splitDet (m - 2) x s u := by
  let D := twoFanDataOfDistinct hm x s u hs hu hpair hcross
  have hD := criticalSplitDet_tieFree_nonneg D hm x hx
    (twoFanDataOfDistinct_samplesInside hm x s u hs hu hpair hcross)
  simpa [D, twoFanDataOfDistinct_s hm x s u hs hu hpair hcross,
    twoFanDataOfDistinct_u hm x s u hs hu hpair hcross] using hD

/-- At positive exponent, translating the entire right knot family is a
continuous specialization of the split determinant. -/
private theorem splitDet_succ_tendsto_rightShift {m r : Nat}
    (x : Fin (2 * m) → Real) (s u : Fin m → Real) :
    Tendsto
      (fun ε : Real =>
        splitDet (r + 1) x s (fun q => u q + ε))
      (𝓝[>] 0) (𝓝 (splitDet (r + 1) x s u)) := by
  have hcont : Continuous (fun ε : Real =>
      splitDet (r + 1) x s (fun q => u q + ε)) := by
    apply Continuous.matrix_det
    apply continuous_pi
    intro i
    apply continuous_pi
    intro col
    cases hcol : (groupedColumnEquiv m).symm col with
    | inl q =>
        simp only [splitMatrix, hcol, leftKernel]
        exact continuous_const
    | inr q =>
        simp only [splitMatrix, hcol, rightKernel]
        exact (truncPow_succ_continuous r).comp
          (continuous_const.sub (continuous_const.add continuous_id))
  simpa using
    ((hcont.continuousAt : ContinuousAt _ (0 : Real)).tendsto.mono_left inf_le_left)

/-- For every critical degree `m - 2` with `m ≥ 3`, a strictly ordered paired
split determinant is nonnegative.  Cross-family ties are removed by a common
positive shift of the right family and restored by continuity. -/
theorem criticalSplitDet_nonneg_of_three_le {m : Nat} (hm : 3 ≤ m)
    {x : Fin (2 * m) → Real} {s u : Fin m → Real}
    (hx : StrictMono x) (hs : StrictMono s) (hu : StrictMono u)
    (hpair : Paired s u) :
    0 ≤ splitDet (m - 2) x s u := by
  have hright (ε : Real) : StrictMono (fun q => u q + ε) := by
    intro a b hab
    dsimp
    linarith [hu hab]
  have hpaired (ε : Real) (hε : 0 < ε) :
      Paired s (fun q => u q + ε) := by
    intro q
    dsimp
    linarith [hpair q]
  have hcross_one (i j : Fin m) :
      ∀ᶠ ε : Real in 𝓝[>] 0, s i ≠ u j + ε := by
    by_cases hd : 0 < s i - u j
    · have hmem : Set.Iio (s i - u j) ∈ 𝓝[>] (0 : Real) :=
        Filter.Eventually.filter_mono
          (show 𝓝[>] (0 : Real) ≤ 𝓝 0 from nhdsWithin_le_nhds)
          (Iio_mem_nhds hd)
      filter_upwards [hmem] with ε hε
      change ε < s i - u j at hε
      intro heq
      linarith
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      change 0 < ε at hε
      intro heq
      linarith
  have hcross : ∀ᶠ ε : Real in 𝓝[>] 0,
      CrossFamilyDistinct s (fun q => u q + ε) := by
    simpa [CrossFamilyDistinct] using
      ((Filter.eventually_all_finset (l := 𝓝[>] (0 : Real))
        (p := fun z ε => s z.1 ≠ u z.2 + ε)
        (Finset.univ : Finset (Fin m × Fin m))).mpr
        (by rintro ⟨i, j⟩ _; exact hcross_one i j))
  have hnonneg : ∀ᶠ ε : Real in 𝓝[>] 0,
      0 ≤ splitDet (m - 2) x s (fun q => u q + ε) := by
    filter_upwards [self_mem_nhdsWithin, hcross] with ε hε hdistinct
    change 0 < ε at hε
    exact criticalSplitDet_distinct_nonneg hm hx hs (hright ε)
      (hpaired ε hε) hdistinct
  have hdegree : m - 2 = (m - 3) + 1 := by omega
  have hlim : Tendsto
      (fun ε : Real => splitDet (m - 2) x s (fun q => u q + ε))
      (𝓝[>] 0) (𝓝 (splitDet (m - 2) x s u)) := by
    rw [hdegree]
    exact splitDet_succ_tendsto_rightShift (r := m - 3) x s u
  exact isClosed_Ici.mem_of_tendsto hlim hnonneg

end

end ColomboGeneralK2.Odd
