import ColomboGeneralK2.ComplementaryMinor

/-!
# Finite labelled full-domain de Bruijn expansion

This file upgrades `recursivePf_pullback_fin`, whose right hand side is
indexed by unordered `m`-element subsets, to the labelled full-domain sum
over functions `Fin m → Fin s`.  The displayed theorem below is exactly the
statement in the accompanying notes: the factor `m!` occurs on the Pfaffian
side, rather than after cancelling it in a ring where cancellation need not
be valid.
-/

namespace ColomboGeneralK2

open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- A repeated label gives two identical left columns, hence zero determinant. -/
theorem selectedPairMatrix_det_zero_of_not_injective {m s : Nat}
    (Z : Fin s → Fin (2 * m) → Fin 2 → R) (x : Fin m → Fin s)
    (hx : ¬ Function.Injective x) :
    (selectedPairMatrix Z (List.Vector.ofFn x)).det = 0 := by
  classical
  obtain ⟨q, r, hxr, hqr⟩ := Function.not_injective_iff.mp hx
  apply Matrix.det_zero_of_column_eq (i := pairCol m q 0) (j := pairCol m r 0)
  · intro h
    apply hqr
    have hp : (q, (0 : Fin 2)) = (r, 0) := by
      apply (pairColumnEquiv m).injective
      exact h
    exact congrArg Prod.fst hp
  · intro row
    simp only [selectedPairMatrix_pairCol, List.Vector.get_ofFn, hxr]

/-- Relabelling whole adjacent pairs does not change the selected determinant. -/
theorem selectedPairMatrix_det_ofFn_comp_perm {m s : Nat}
    (Z : Fin s → Fin (2 * m) → Fin 2 → R) (x : Fin m → Fin s)
    (σ : Equiv.Perm (Fin m)) :
    (selectedPairMatrix Z (List.Vector.ofFn (x ∘ σ))).det =
      (selectedPairMatrix Z (List.Vector.ofFn x)).det := by
  classical
  let τ : Equiv.Perm (Fin (2 * m)) :=
    (pairColumnEquiv m).permCongr (pairBlockPerm σ)
  have hmatrix : selectedPairMatrix Z (List.Vector.ofFn (x ∘ σ)) =
      (selectedPairMatrix Z (List.Vector.ofFn x)).submatrix id τ := by
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

/-- The weight product is unchanged by a permutation of tuple positions. -/
theorem tuple_weight_comp_perm {m s : Nat} (w : Fin s → R)
    (x : Fin m → Fin s) (σ : Equiv.Perm (Fin m)) :
    (∏ q, w (x (σ q))) = ∏ q, w (x q) := by
  exact Fintype.prod_equiv σ (fun q ↦ w (x (σ q)))
    (fun q ↦ w (x q)) (fun _ ↦ rfl)

abbrev InjectiveTuple (m s : Nat) :=
  {x : Fin m → Fin s // Function.Injective x}

abbrev LabelSet (m s : Nat) :=
  {S : Finset (Fin s) // S ∈ (Finset.univ : Finset (Fin s)).powersetCard m}

/-- The finite image of an injective labelled tuple, with its cardinality proof. -/
def tupleImage {m s : Nat} (x : InjectiveTuple m s) : LabelSet m s :=
  ⟨Finset.univ.image x.1, by
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [Finset.card_image_of_injective _ x.2]
    simp⟩

/-- The tuple obtained by listing a fixed label set in a prescribed order. -/
def tupleOf {m s : Nat} (S : LabelSet m s) (σ : Equiv.Perm (Fin m)) :
    InjectiveTuple m s :=
  ⟨fun q ↦ ((sortedPairEquiv S.1 (Finset.mem_powersetCard.mp S.2).2) (σ q)).1,
    by
      intro q r h
      apply σ.injective
      apply (sortedPairEquiv S.1 (Finset.mem_powersetCard.mp S.2).2).injective
      exact Subtype.ext h⟩

theorem tupleImage_tupleOf {m s : Nat} (S : LabelSet m s)
    (σ : Equiv.Perm (Fin m)) : tupleImage (tupleOf S σ) = S := by
  apply Subtype.ext
  change Finset.univ.image (tupleOf S σ).1 = S.1
  ext t
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨q, hq⟩
    rw [← hq]
    exact ((sortedPairEquiv S.1 (Finset.mem_powersetCard.mp S.2).2) (σ q)).2
  · intro ht
    let e := sortedPairEquiv S.1 (Finset.mem_powersetCard.mp S.2).2
    refine ⟨σ.symm (e.symm ⟨t, ht⟩), ?_⟩
    simp only [tupleOf, Equiv.apply_symm_apply]
    change (sortedPairVectorOfCard S.1
      (Finset.mem_powersetCard.mp S.2).2).get (e.symm ⟨t, ht⟩) = t
    rw [← sortedPairEquiv_apply]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨t, ht⟩)

theorem tupleOf_injective {m s : Nat} (S : LabelSet m s) :
    Function.Injective (tupleOf S) := by
  intro σ τ h
  ext q
  have hq := congrArg (fun y : InjectiveTuple m s ↦ y.1 q) h
  exact congrArg Fin.val ((sortedPairEquiv S.1
    (Finset.mem_powersetCard.mp S.2).2).injective (Subtype.ext hq))

theorem tupleOf_surjective_fiber {m s : Nat} (S : LabelSet m s) :
    Function.Surjective (fun σ : Equiv.Perm (Fin m) ↦
      (⟨tupleOf S σ, tupleImage_tupleOf S σ⟩ :
        {x : InjectiveTuple m s // tupleImage x = S})) := by
  intro x
  let e := sortedPairEquiv S.1 (Finset.mem_powersetCard.mp S.2).2
  have himg : (tupleImage x.1).1 = S.1 := congrArg Subtype.val x.2
  let ex : Fin m ≃ S.1 :=
    Equiv.ofBijective (fun q ↦ ⟨x.1.1 q, by
      have hxmem : x.1.1 q ∈ (tupleImage x.1).1 := by
        change x.1.1 q ∈ Finset.univ.image x.1.1
        exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
      rw [himg] at hxmem
      exact hxmem⟩) ⟨by
        intro a b hab
        apply x.1.2
        exact congrArg Subtype.val hab, by
        intro y
        have hymem : y.1 ∈ (tupleImage x.1).1 := by
          rw [himg]
          exact y.2
        change y.1 ∈ Finset.univ.image x.1.1 at hymem
        obtain ⟨q, -, hq⟩ := Finset.mem_image.mp hymem
        exact ⟨q, Subtype.ext hq⟩⟩
  let σ : Equiv.Perm (Fin m) := ex.trans e.symm
  refine ⟨σ, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext q
  change (e (σ q)).1 = x.1.1 q
  simp [σ, ex]

def tupleTerm {m s : Nat} (Z : Fin s → Fin (2 * m) → Fin 2 → R)
    (w : Fin s → R) (x : Fin m → Fin s) : R :=
  (∏ q, w (x q)) * (selectedPairMatrix Z (List.Vector.ofFn x)).det

theorem tupleTerm_comp_perm {m s : Nat}
    (Z : Fin s → Fin (2 * m) → Fin 2 → R) (w : Fin s → R)
    (x : Fin m → Fin s) (σ : Equiv.Perm (Fin m)) :
    tupleTerm Z w (x ∘ σ) = tupleTerm Z w x := by
  unfold tupleTerm
  rw [show (∏ q, w ((x ∘ σ) q)) = ∏ q, w (x q) by
    simpa only [Function.comp_apply] using tuple_weight_comp_perm w x σ]
  rw [selectedPairMatrix_det_ofFn_comp_perm]

theorem sum_tupleTerm_fiber {m s : Nat}
    (Z : Fin s → Fin (2 * m) → Fin 2 → R) (w : Fin s → R)
    (S : LabelSet m s) :
    (∑ x : {x : InjectiveTuple m s // tupleImage x = S}, tupleTerm Z w x.1.1) =
      (m.factorial : R) *
        ((∏ t ∈ S.1, w t) * selectedPairDetFinset Z S.1) := by
  classical
  let f : Equiv.Perm (Fin m) → {x : InjectiveTuple m s // tupleImage x = S} :=
    fun σ ↦ ⟨tupleOf S σ, tupleImage_tupleOf S σ⟩
  have hf : Function.Bijective f := ⟨by
      intro σ τ h
      apply tupleOf_injective S
      exact congrArg Subtype.val h,
    tupleOf_surjective_fiber S⟩
  have hsum : (∑ x : {x : InjectiveTuple m s // tupleImage x = S},
      tupleTerm Z w x.1.1) =
      ∑ σ : Equiv.Perm (Fin m), tupleTerm Z w (tupleOf S σ).1 := by
    symm
    apply Fintype.sum_bijective f hf
    intro σ
    rfl
  rw [hsum]
  have hconst : ∀ σ : Equiv.Perm (Fin m),
      tupleTerm Z w (tupleOf S σ).1 =
        tupleTerm Z w (tupleOf S (Equiv.refl _)).1 := by
    intro σ
    simpa [tupleOf, Function.comp_def] using
      tupleTerm_comp_perm Z w (tupleOf S (Equiv.refl _)).1 σ
  calc
    _ = ∑ _ : Equiv.Perm (Fin m),
        tupleTerm Z w (tupleOf S (Equiv.refl _)).1 := by
      apply Finset.sum_congr rfl
      intro σ _
      exact hconst σ
    _ = (Fintype.card (Equiv.Perm (Fin m)) : R) *
        tupleTerm Z w (tupleOf S (Equiv.refl _)).1 := by simp
    _ = _ := by
      rw [Fintype.card_perm, Fintype.card_fin]
      congr 1
      have hvector : List.Vector.ofFn (tupleOf S (Equiv.refl _)).1 =
          sortedPairVectorOfCard S.1 (Finset.mem_powersetCard.mp S.2).2 := by
        apply List.Vector.eq
        simp [tupleOf, sortedPairEquiv_apply]
      have hweight : (∏ q, w ((tupleOf S (Equiv.refl _)).1 q)) =
          ∏ t ∈ S.1, w t := by
        let e := sortedPairEquiv S.1 (Finset.mem_powersetCard.mp S.2).2
        calc
          _ = ∏ q, w ((e q).1) := by simp [tupleOf, e]
          _ = ∏ t : S.1, w t := e.prod_comp (fun t ↦ w t)
          _ = _ := by rw [← Finset.prod_attach S.1 w, Finset.attach_eq_univ]
      unfold tupleTerm
      rw [hweight, hvector]
      rw [show (selectedPairMatrix Z
        (sortedPairVectorOfCard S.1 (Finset.mem_powersetCard.mp S.2).2)).det =
          selectedPairDetFinset Z S.1 by
        simpa [selectedPairDet] using (selectedPairDetFinset_eq Z S.1
          (Finset.mem_powersetCard.mp S.2).2).symm]

theorem sum_tupleTerm_eq_factorial_mul_subset_sum {m s : Nat}
    (Z : Fin s → Fin (2 * m) → Fin 2 → R) (w : Fin s → R) :
    (∑ x : Fin m → Fin s, tupleTerm Z w x) =
      (m.factorial : R) *
        ∑ S ∈ (Finset.univ : Finset (Fin s)).powersetCard m,
          (∏ t ∈ S, w t) * selectedPairDetFinset Z S := by
  classical
  have hzero : ∀ x : Fin m → Fin s, ¬ Function.Injective x → tupleTerm Z w x = 0 := by
    intro x hx
    unfold tupleTerm
    rw [selectedPairMatrix_det_zero_of_not_injective Z x hx]
    simp
  have hinjective : (∑ x : Fin m → Fin s, tupleTerm Z w x) =
      ∑ x : InjectiveTuple m s, tupleTerm Z w x.1 := by
    calc
      _ = ∑ x ∈ (Finset.univ : Finset (Fin m → Fin s)) with Function.Injective x,
          tupleTerm Z w x := by
        symm
        apply Finset.sum_filter_of_ne
        intro x _ hx
        by_contra h
        exact hx (hzero x h)
      _ = _ := Finset.sum_subtype (p := Function.Injective)
        (Finset.univ.filter Function.Injective) (by intro x; simp) (tupleTerm Z w)
  rw [hinjective]
  calc
    _ = ∑ S : LabelSet m s,
        ∑ x ∈ (Finset.univ : Finset (InjectiveTuple m s)) with tupleImage x = S,
          tupleTerm Z w x.1 := by
      exact (Finset.sum_fiberwise Finset.univ tupleImage (fun x ↦ tupleTerm Z w x.1)).symm
    _ = ∑ S : LabelSet m s,
        ∑ x : {x : InjectiveTuple m s // tupleImage x = S}, tupleTerm Z w x.1 := by
      apply Finset.sum_congr rfl
      intro S _
      exact Finset.sum_subtype (p := fun x : InjectiveTuple m s ↦ tupleImage x = S)
        (Finset.univ.filter fun x : InjectiveTuple m s ↦ tupleImage x = S)
        (by intro x; simp) (fun x ↦ tupleTerm Z w x.1)
    _ = ∑ S : LabelSet m s,
        (m.factorial : R) *
          ((∏ t ∈ S.1, w t) * selectedPairDetFinset Z S.1) := by
      apply Finset.sum_congr rfl
      intro S _
      exact sum_tupleTerm_fiber Z w S
    _ = ∑ S ∈ (Finset.univ : Finset (Fin s)).powersetCard m,
        (m.factorial : R) * ((∏ t ∈ S, w t) * selectedPairDetFinset Z S) := by
      symm
      exact Finset.sum_subtype _ (by simp) (fun S ↦
        (m.factorial : R) * ((∏ t ∈ S, w t) * selectedPairDetFinset Z S))
    _ = _ := by rw [Finset.mul_sum]

/--
The finite labelled full-domain de Bruijn expansion.  No cancellation of
`m!` is used, so the formula remains valid in arbitrary characteristics.
-/
theorem factorial_mul_recursivePf_pullback_eq_sum_tuple
    {R : Type*} [CommRing R] {m s : Nat}
    (Z : Fin s → Fin (2 * m) → Fin 2 → R)
    (w : Fin s → R) :
    (m.factorial : R) *
        recursivePf m (pullbackFinset Z w Finset.univ) =
      ∑ x : Fin m → Fin s,
        (∏ q, w (x q)) *
          (selectedPairMatrix Z (List.Vector.ofFn x)).det := by
  rw [recursivePf_pullback_fin]
  exact (sum_tupleTerm_eq_factorial_mul_subset_sum Z w).symm

end ColomboGeneralK2
