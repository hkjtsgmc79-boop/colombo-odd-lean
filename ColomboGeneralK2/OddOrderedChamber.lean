import ColomboGeneralK2.OddMVP1Signatures
import ColomboGeneralK2.OddDeBruijnFinite
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Group.FundamentalDomain

/-!
# Permutation chambers for the odd de Bruijn integral

This file equips labelled tuples with the coordinate-reindexing action of
`Equiv.Perm (Fin m)`.  It proves the algebraic symmetry and the fundamental-
domain reduction separately from the null-diagonal argument for real product
measure.
-/

namespace ColomboGeneralK2.Odd

open MeasureTheory
open scoped BigOperators Pointwise

noncomputable section

/-- Product measure on an `m`-tuple of real variables. -/
abbrev tupleVolume (m : Nat) : Measure (Fin m → Real) :=
  Measure.pi fun _ : Fin m ↦ (volume : Measure Real)

/-- A permutation acts on a labelled tuple by reindexing its coordinates. -/
instance tuplePermSMul (m : Nat) (I : Type*) :
    SMul (Equiv.Perm (Fin m)) (Fin m → I) :=
  ⟨fun σ t ↦ t ∘ σ.symm⟩

@[simp]
theorem tuplePerm_smul_apply {m : Nat} {I : Type*}
    (σ : Equiv.Perm (Fin m)) (t : Fin m → I) (i : Fin m) :
    (σ • t) i = t (σ.symm i) :=
  rfl

instance tuplePermMulAction (m : Nat) (I : Type*) :
    MulAction (Equiv.Perm (Fin m)) (Fin m → I) where
  one_smul t := by
    funext i
    change t ((1 : Equiv.Perm (Fin m)).symm i) = t i
    have hsymm : (1 : Equiv.Perm (Fin m)).symm = 1 := inv_one
    rw [hsymm]
    rfl
  mul_smul σ τ t := by
    funext i
    change t ((σ * τ).symm i) = t (τ.symm (σ.symm i))
    have hsymm : (σ * τ).symm = τ.symm * σ.symm := by
      change (σ * τ)⁻¹ = τ⁻¹ * σ⁻¹
      exact mul_inv_rev σ τ
    rw [hsymm, Equiv.Perm.mul_apply]

/-- Coordinate permutations preserve the finite real product measure. -/
theorem tuplePerm_measurePreserving {m : Nat} (σ : Equiv.Perm (Fin m)) :
    MeasurePreserving (fun t : Fin m → Real ↦ σ • t)
      (tupleVolume m) (tupleVolume m) := by
  have hfun : (fun t : Fin m → Real ↦ σ • t) =
      (MeasurableEquiv.piCongrLeft (fun _ : Fin m ↦ Real) σ) := by
    funext t i
    change t (σ.symm i) =
      Equiv.piCongrLeft (fun _ : Fin m ↦ Real) σ t i
    rw [Equiv.piCongrLeft_apply]
    simp only [eq_rec_constant]
  rw [hfun]
  exact measurePreserving_piCongrLeft
    (fun _ : Fin m ↦ (volume : Measure Real)) σ

instance tuplePermMeasurableConstSMul (m : Nat) :
    MeasurableConstSMul (Equiv.Perm (Fin m)) (Fin m → Real) :=
  ⟨fun σ ↦ (tuplePerm_measurePreserving σ).measurable⟩

instance tuplePermInvariantMeasure (m : Nat) :
    SMulInvariantMeasure (Equiv.Perm (Fin m)) (Fin m → Real)
      (tupleVolume m) :=
  ⟨fun σ s hs ↦ by
    let h := tuplePerm_measurePreserving σ
    calc
      tupleVolume m ((fun t : Fin m → Real ↦ σ • t) ⁻¹' s) =
          Measure.map (fun t : Fin m → Real ↦ σ • t)
            (tupleVolume m) s := (Measure.map_apply h.measurable hs).symm
      _ = tupleVolume m s := by rw [h.map_eq]⟩

/-- The strict ordered chamber is measurable. -/
theorem measurableSet_orderedChamber (m : Nat) :
    MeasurableSet (orderedChamber m) := by
  cases m with
  | zero =>
      have h : orderedChamber 0 = Set.univ := by
        ext t
        simp [orderedChamber, StrictMono]
      rw [h]
      exact MeasurableSet.univ
  | succ n =>
      have h : orderedChamber (n + 1) =
          ⋂ i : Fin n,
            {t : Fin (n + 1) → Real | t i.castSucc < t i.succ} := by
        ext t
        simp [orderedChamber, Fin.strictMono_iff_lt_succ]
      rw [h]
      exact MeasurableSet.iInter fun i ↦
        measurableSet_lt (measurable_pi_apply _) (measurable_pi_apply _)

/-- Any injective tuple can be moved into the strict ordered chamber. -/
theorem exists_perm_smul_mem_orderedChamber {m : Nat}
    (t : Fin m → Real) (ht : Function.Injective t) :
    ∃ σ : Equiv.Perm (Fin m), σ • t ∈ orderedChamber m := by
  refine ⟨(Tuple.sort t).symm, ?_⟩
  simpa only [orderedChamber, tuplePerm_smul_apply, Equiv.symm_symm,
    Function.comp_apply] using
      (Tuple.monotone_sort t).strictMono_of_injective
        (ht.comp (Tuple.sort t).injective)

/-- Distinct coordinate permutations give disjoint strict chambers. -/
theorem disjoint_smul_orderedChamber {m : Nat}
    (σ : Equiv.Perm (Fin m)) (hσ : σ ≠ 1) :
    Disjoint (σ • orderedChamber m) (orderedChamber m) := by
  rw [Set.disjoint_left]
  intro t htσ ht
  rw [Set.mem_smul_set_iff_inv_smul_mem] at htσ
  have hmonoσ : Monotone (t ∘ σ) := by
    simpa only [tuplePerm_smul_apply, inv_inv, Function.comp_apply] using
      (show StrictMono (σ⁻¹ • t) from htσ).monotone
  have hmonoOne : Monotone (t ∘ (1 : Equiv.Perm (Fin m))) := by
    simpa using (show StrictMono t from ht).monotone
  have heq := Tuple.unique_monotone hmonoσ hmonoOne
  apply hσ
  apply Equiv.ext
  intro i
  apply (show StrictMono t from ht).injective
  have hi := congrFun heq i
  simpa using hi

/-- Once repeated-coordinate tuples are known to be null, the strict ordered
chamber is a fundamental domain for coordinate permutations. -/
theorem orderedChamber_isFundamentalDomain_of_ae_injective {m : Nat}
    (hae : ∀ᵐ t : Fin m → Real ∂tupleVolume m, Function.Injective t) :
    IsFundamentalDomain (Equiv.Perm (Fin m)) (orderedChamber m)
      (tupleVolume m) := by
  refine IsFundamentalDomain.mk''
    (measurableSet_orderedChamber m).nullMeasurableSet ?_ ?_ ?_
  · filter_upwards [hae] with t ht
    exact exists_perm_smul_mem_orderedChamber t ht
  · intro σ hσ
    exact (disjoint_smul_orderedChamber σ hσ).aedisjoint
  · intro σ
    exact (tuplePerm_measurePreserving σ).quasiMeasurePreserving

/-- Difference of two coordinate projections.  Its kernel is the collision
hyperplane for the corresponding labelled variables. -/
def coordinateDifference {m : Nat} (i j : Fin m) :
    (Fin m → Real) →ₗ[Real] Real :=
  (LinearMap.proj i : (Fin m → Real) →ₗ[Real] Real) - LinearMap.proj j

@[simp]
theorem coordinateDifference_apply {m : Nat} (i j : Fin m)
    (t : Fin m → Real) :
    coordinateDifference i j t = t i - t j := by
  simp [coordinateDifference]

/-- A collision hyperplane has zero finite-dimensional Lebesgue measure. -/
theorem tupleVolume_collision_zero {m : Nat} (i j : Fin m) (hij : i ≠ j) :
    tupleVolume m {t | t i = t j} = 0 := by
  change (Measure.pi fun _ : Fin m ↦ (volume : Measure Real))
    {t | t i = t j} = 0
  rw [← volume_pi]
  have hset : {t : Fin m → Real | t i = t j} =
      (coordinateDifference i j).ker := by
    ext t
    simp [LinearMap.mem_ker, sub_eq_zero]
  rw [hset]
  apply Measure.addHaar_submodule
  rw [Ne, LinearMap.ker_eq_top]
  intro hzero
  let t : Fin m → Real := fun k ↦ if k = i then 1 else 0
  have ht := congrArg
    (fun f : (Fin m → Real) →ₗ[Real] Real ↦ f t) hzero
  have hji : j ≠ i := Ne.symm hij
  simp [coordinateDifference, t, hji] at ht

/-- Almost every labelled real tuple has pairwise distinct coordinates. -/
theorem tupleVolume_ae_injective {m : Nat} :
    ∀ᵐ t : Fin m → Real ∂tupleVolume m, Function.Injective t := by
  have hpairs : ∀ i j : Fin m,
      ∀ᵐ t : Fin m → Real ∂tupleVolume m,
        i ≠ j → t i ≠ t j := by
    intro i j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ hne ↦ (hne hij).elim
    · have hz := tupleVolume_collision_zero i j hij
      have hne : ∀ᵐ t : Fin m → Real ∂tupleVolume m, t i ≠ t j := by
        rw [MeasureTheory.ae_iff]
        simpa only [Set.mem_setOf_eq, not_ne_iff] using hz
      exact hne.mono fun _ h _ ↦ h
  filter_upwards [Filter.eventually_all.2 fun i ↦
    Filter.eventually_all.2 fun j ↦ hpairs i j] with t ht
  intro i j heq
  by_contra hij
  exact ht i j hij heq

/-- The strict ordered chamber is an unconditional fundamental domain for
coordinate permutations under finite real product measure. -/
theorem orderedChamber_isFundamentalDomain (m : Nat) :
    IsFundamentalDomain (Equiv.Perm (Fin m)) (orderedChamber m)
      (tupleVolume m) :=
  orderedChamber_isFundamentalDomain_of_ae_injective
    tupleVolume_ae_injective

/-- A permutation-invariant integrable function has full labelled integral
equal to `m!` times its integral over the strict ordered chamber. -/
theorem integral_eq_factorial_mul_orderedChamber {m : Nat}
    (f : (Fin m → Real) → Real)
    (hf : Integrable f (tupleVolume m))
    (hinv : ∀ (σ : Equiv.Perm (Fin m)) (t : Fin m → Real),
      f (σ • t) = f t) :
    (∫ t, f t ∂tupleVolume m) =
      (Nat.factorial m : Real) *
        ∫ t in orderedChamber m, f t ∂tupleVolume m := by
  calc
    (∫ t, f t ∂tupleVolume m) =
        ∑' σ : Equiv.Perm (Fin m),
          ∫ t in orderedChamber m, f (σ • t) ∂tupleVolume m :=
      (orderedChamber_isFundamentalDomain m).integral_eq_tsum'' f hf
    _ = ∑' _σ : Equiv.Perm (Fin m),
        ∫ t in orderedChamber m, f t ∂tupleVolume m := by
      apply tsum_congr
      intro σ
      apply integral_congr_ae
      filter_upwards [] with t
      exact hinv σ t
    _ = (Nat.factorial m : Real) *
        ∫ t in orderedChamber m, f t ∂tupleVolume m := by
      rw [tsum_fintype]
      simp [Fintype.card_perm, nsmul_eq_mul]

/-- Relabelling whole adjacent pairs over an arbitrary label type does not
change the selected determinant. -/
theorem selectedPairMatrix_det_ofFn_comp_perm_generic
    {m : Nat} {I R : Type*} [CommRing R]
    (Z : I → Fin (2 * m) → Fin 2 → R) (t : Fin m → I)
    (σ : Equiv.Perm (Fin m)) :
    (selectedPairMatrix Z (List.Vector.ofFn (t ∘ σ))).det =
      (selectedPairMatrix Z (List.Vector.ofFn t)).det := by
  classical
  let τ : Equiv.Perm (Fin (2 * m)) :=
    (pairColumnEquiv m).permCongr (pairBlockPerm σ)
  have hmatrix : selectedPairMatrix Z (List.Vector.ofFn (t ∘ σ)) =
      (selectedPairMatrix Z (List.Vector.ofFn t)).submatrix id τ := by
    ext row col
    let qside := (pairColumnEquiv m).symm col
    have hcol : col = pairColumnEquiv m qside :=
      (pairColumnEquiv m).apply_symm_apply col |>.symm
    rw [hcol]
    simp [selectedPairMatrix, Matrix.submatrix_apply, List.Vector.get_ofFn,
      Function.comp_apply, τ, qside, Equiv.permCongr_apply, pairBlockPerm]
  rw [hmatrix, Matrix.det_permute', Equiv.Perm.sign_permCongr,
    pairBlockPerm_sign]
  simp

/-- Adjacent-pair determinants are invariant under permutation of their
labelled integration variables. -/
theorem selectedPairMatrix_det_smul {m : Nat} {I R : Type*} [CommRing R]
    (Z : I → Fin (2 * m) → Fin 2 → R) (t : Fin m → I)
    (σ : Equiv.Perm (Fin m)) :
    (selectedPairMatrix Z (List.Vector.ofFn (σ • t))).det =
      (selectedPairMatrix Z (List.Vector.ofFn t)).det := by
  simpa only [tuplePerm_smul_apply, Function.comp_apply] using
    selectedPairMatrix_det_ofFn_comp_perm_generic Z t σ.symm

/-- The paper-facing grouped determinant has the same variable-permutation
invariance. -/
theorem groupedPairMatrix_det_smul {m : Nat} {I R : Type*} [CommRing R]
    (Z : I → Fin (2 * m) → Fin 2 → R) (t : Fin m → I)
    (σ : Equiv.Perm (Fin m)) :
    (groupedPairMatrix Z (σ • t)).det = (groupedPairMatrix Z t).det := by
  rw [groupedPairMatrix_det, groupedPairMatrix_det,
    selectedPairMatrix_det_smul]

end

end ColomboGeneralK2.Odd
