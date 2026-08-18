import ColomboGeneralK2.GeneralADPf
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.NodupEquivFin

/-!
# General anti-diagonal minor summation

This file proves the symbolic `2m x 2s` anti-diagonal Pfaffian
minor-summation identity.  Selected pair blocks are put in canonical sorted
order, and every summand on the determinant side is a genuine `Matrix.det`.
The proof is valid over an arbitrary commutative ring, including
characteristic two.
-/

namespace ColomboGeneralK2

section WideMatrixAdapter

variable {R I : Type*}

/-- The literal `2m x 2s` matrix before selecting any pair blocks. -/
def widePairMatrix {m : Nat} (Z : I → Fin (2 * m) → Fin 2 → R) :
    Matrix (Fin (2 * m)) (I × Fin 2) R :=
  fun row col ↦ Z col.1 row col.2

/-- The adjacent columns selected by a vector of pair labels. -/
def selectedPairColumn {m : Nat} (pairs : List.Vector I m) :
    Fin (2 * m) → I × Fin 2 :=
  fun col ↦
    let qside := (pairColumnEquiv m).symm col
    (pairs.get qside.1, qside.2)

/-- `selectedPairMatrix` really is a square submatrix of the wide matrix. -/
theorem selectedPairMatrix_eq_wide_submatrix {m : Nat}
    (Z : I → Fin (2 * m) → Fin 2 → R) (pairs : List.Vector I m) :
    selectedPairMatrix Z pairs =
      (widePairMatrix Z).submatrix id (selectedPairColumn pairs) := by
  rfl

end WideMatrixAdapter

section WideDeterminantAdapter

variable {R I : Type*} [CommRing R]

/-- The selected-pair determinant is the determinant of that literal submatrix. -/
theorem selectedPairDet_eq_wide_submatrix_det {m : Nat}
    (Z : I → Fin (2 * m) → Fin 2 → R) (pairs : List.Vector I m) :
    selectedPairDet Z pairs =
      ((widePairMatrix Z).submatrix id (selectedPairColumn pairs)).det := by
  rw [selectedPairDet, selectedPairMatrix_eq_wide_submatrix]

end WideDeterminantAdapter

theorem sort_erase {I : Type*} [LinearOrder I] (S : Finset I) (t : I) :
    (S.erase t).sort = (S.sort).erase t := by
  apply List.SortedLT.eq_of_mem_iff (Finset.sortedLT_sort (S.erase t))
    ((Finset.sortedLT_sort S).pairwise.erase t).sortedLT
  intro x
  rw [Finset.mem_sort, (Finset.sort_nodup S (fun a b ↦ a ≤ b)).mem_erase_iff,
    Finset.mem_sort]
  simp

theorem erasePairVector_eq_eraseIdx {I : Type*} {n : Nat}
    (v : List.Vector I (n + 1)) (h : Fin (n + 1)) :
    erasePairVector v h = v.eraseIdx h := by
  apply List.Vector.ext
  intro q
  simp only [erasePairVector, List.Vector.get_ofFn]
  rcases v with ⟨l, hl⟩
  rcases h with ⟨h, hh⟩
  rcases q with ⟨q, hq⟩
  simp only [List.Vector.get, List.Vector.eraseIdx]
  simp only [List.get_eq_getElem]
  simp only [List.getElem_eraseIdx]
  simp only [Fin.succAbove, Fin.lt_def]
  have hcast : ((⟨q, hq⟩ : Fin n).castSucc : Nat) = q := rfl
  simp only [hcast]
  split_ifs <;> simp_all

def sortedPairVector {I : Type*} [LinearOrder I] (S : Finset I) :
    List.Vector I S.card :=
  ⟨S.sort, Finset.length_sort (s := S) (fun a b ↦ a ≤ b)⟩

def sortedPairVectorOfCard {I : Type*} [LinearOrder I] {m : Nat}
    (S : Finset I) (hs : S.card = m) : List.Vector I m :=
  ⟨S.sort, (Finset.length_sort (s := S) (fun a b ↦ a ≤ b)).trans hs⟩

theorem sortedPairVectorOfCard_get_mem {I : Type*} [LinearOrder I] {m : Nat}
    (S : Finset I) (hs : S.card = m) (h : Fin m) :
    (sortedPairVectorOfCard S hs).get h ∈ S := by
  apply (Finset.mem_sort (s := S) (fun a b ↦ a ≤ b)).mp
  exact List.get_mem _ _

def sortedPairEquiv {I : Type*} [LinearOrder I] {m : Nat}
    (S : Finset I) (hs : S.card = m) : Fin m ≃ {x // x ∈ S} :=
  (finCongr ((Finset.length_sort (s := S) (fun a b ↦ a ≤ b)).trans hs)).symm |>.trans
    ((Finset.sort_nodup S (fun a b ↦ a ≤ b)).getEquiv S.sort) |>.trans
      (Equiv.subtypeEquivRight fun x ↦ Finset.mem_sort (s := S) (fun a b ↦ a ≤ b))

@[simp]
theorem sortedPairEquiv_apply {I : Type*} [LinearOrder I] {m : Nat}
    (S : Finset I) (hs : S.card = m) (h : Fin m) :
    ((sortedPairEquiv S hs h : {x // x ∈ S}) : I) =
      (sortedPairVectorOfCard S hs).get h := by
  rfl

theorem eraseSortedPairVector {I : Type*} [LinearOrder I] {n : Nat} (S : Finset I)
    (hs : S.card = n + 1) (h : Fin (n + 1)) :
    let v := sortedPairVectorOfCard S hs
    erasePairVector v h =
      sortedPairVectorOfCard (S.erase (v.get h)) (by
        rw [Finset.card_erase_of_mem]
        · omega
        · exact sortedPairVectorOfCard_get_mem S hs h) := by
  dsimp only
  rw [erasePairVector_eq_eraseIdx]
  apply Subtype.ext
  simp only [List.Vector.eraseIdx_val, sortedPairVectorOfCard]
  rw [sort_erase]
  symm
  simpa only using (Finset.sort_nodup S (fun a b ↦ a ≤ b)).erase_get
    (h.cast (by simpa using hs.symm))

variable {R I : Type*} [CommRing R] [LinearOrder I]

def selectedPairDetFinset {m : Nat} (Z : I → Fin (2 * m) → Fin 2 → R)
    (S : Finset I) : R :=
  if hs : S.card = m then selectedPairDet Z (sortedPairVectorOfCard S hs) else 0

theorem selectedPairDetFinset_eq {m : Nat} (Z : I → Fin (2 * m) → Fin 2 → R)
    (S : Finset I) (hs : S.card = m) :
    selectedPairDetFinset Z S = selectedPairDet Z (sortedPairVectorOfCard S hs) := by
  simp [selectedPairDetFinset, hs]

theorem selectedPairDetFinset_owner_laplace {n : Nat}
    (Z : I → Fin (2 * (n + 1)) → Fin 2 → R)
    (S : Finset I) (hs : S.card = n + 1) :
    selectedPairDetFinset Z S =
      ∑ t ∈ S, ∑ k : Fin (2 * n + 1),
        (-1 : R) ^ (k : Nat) * pairWedge Z t 0 (Fin.succ k) *
          selectedPairDetFinset (eraseFirstPartnerRows Z k) (S.erase t) := by
  rw [selectedPairDetFinset_eq Z S hs]
  rw [selectedPairDet_owner_laplace]
  let g : I → R := fun t ↦ ∑ k : Fin (2 * n + 1),
    (-1 : R) ^ (k : Nat) * pairWedge Z t 0 (Fin.succ k) *
      selectedPairDetFinset (eraseFirstPartnerRows Z k) (S.erase t)
  let e := sortedPairEquiv S hs
  calc
    _ = ∑ h : Fin (n + 1), g (e h) := by
      apply Fintype.sum_congr
      intro h
      have ht : (sortedPairVectorOfCard S hs).get h ∈ S :=
        sortedPairVectorOfCard_get_mem S hs h
      have hcard : (S.erase ((sortedPairVectorOfCard S hs).get h)).card = n := by
        rw [Finset.card_erase_of_mem ht, hs]
        omega
      have herase := eraseSortedPairVector S hs h
      dsimp only [g, e]
      simp only [sortedPairEquiv_apply]
      apply Fintype.sum_congr
      intro k
      rw [selectedPairDetFinset_eq _ _ hcard]
      rw [← herase]
    _ = ∑ t : {x // x ∈ S}, g t :=
      (e.sum_comp (fun t : {x // x ∈ S} ↦ g t))
    _ = ∑ t ∈ S, g t := by
      rw [← Finset.sum_attach S g]
      rw [Finset.attach_eq_univ]
    _ = _ := by rfl

def sideAugmentedMatrix {n : Nat}
    (Z : I → Fin (2 * (n + 1)) → Fin 2 → R)
    (pairs : List.Vector I n) (t : I) (side : Fin 2) :
    Matrix (Fin (2 * n + 1)) (Fin (2 * n + 1)) R :=
  fun row col ↦ Fin.cases (Z t (Fin.succ row) side)
    (fun c ↦
      let qside := (pairColumnEquiv n).symm c
      Z (pairs.get qside.1) (Fin.succ row) qside.2) col

omit [CommRing R] [LinearOrder I] in
theorem sideAugmentedMatrix_submatrix {n : Nat}
    (Z : I → Fin (2 * (n + 1)) → Fin 2 → R)
    (pairs : List.Vector I n) (t : I) (side : Fin 2) (k : Fin (2 * n + 1)) :
    (sideAugmentedMatrix Z pairs t side).submatrix k.succAbove Fin.succ =
      selectedPairMatrix (eraseFirstPartnerRows Z k) pairs := by
  ext row col
  simp [sideAugmentedMatrix, selectedPairMatrix, eraseFirstPartnerRows]

omit [LinearOrder I] in
theorem sideAugmentedMatrix_det_zero {n : Nat}
    (Z : I → Fin (2 * (n + 1)) → Fin 2 → R)
    (pairs : List.Vector I n) (h : Fin n) (side : Fin 2) :
    (sideAugmentedMatrix Z pairs (pairs.get h) side).det = 0 := by
  apply Matrix.det_zero_of_column_eq (i := 0) (j := Fin.succ (pairCol n h side))
  · exact ne_of_lt (Fin.succ_pos _)
  intro row
  simp [sideAugmentedMatrix, pairCol]

omit [LinearOrder I] in
theorem sideContraction_zero {n : Nat}
    (Z : I → Fin (2 * (n + 1)) → Fin 2 → R)
    (pairs : List.Vector I n) (h : Fin n) (side : Fin 2) :
    (∑ k : Fin (2 * n + 1),
      (-1 : R) ^ (k : Nat) * Z (pairs.get h) (Fin.succ k) side *
        selectedPairDet (eraseFirstPartnerRows Z k) pairs) = 0 := by
  have hz := sideAugmentedMatrix_det_zero Z pairs h side
  rw [Matrix.det_succ_column_zero] at hz
  simpa only [sideAugmentedMatrix, Fin.cases_zero, selectedPairDet,
    sideAugmentedMatrix_submatrix] using hz

omit [LinearOrder I] in
theorem pairContraction_mem_zero {n : Nat}
    (Z : I → Fin (2 * (n + 1)) → Fin 2 → R)
    (pairs : List.Vector I n) (h : Fin n) :
    (∑ k : Fin (2 * n + 1),
      (-1 : R) ^ (k : Nat) * pairWedge Z (pairs.get h) 0 (Fin.succ k) *
        selectedPairDet (eraseFirstPartnerRows Z k) pairs) = 0 := by
  have hR := sideContraction_zero Z pairs h (1 : Fin 2)
  have hL := sideContraction_zero Z pairs h (0 : Fin 2)
  calc
    _ = Z (pairs.get h) 0 0 *
          (∑ k : Fin (2 * n + 1), (-1 : R) ^ (k : Nat) *
            Z (pairs.get h) (Fin.succ k) 1 *
              selectedPairDet (eraseFirstPartnerRows Z k) pairs) -
        Z (pairs.get h) 0 1 *
          (∑ k : Fin (2 * n + 1), (-1 : R) ^ (k : Nat) *
            Z (pairs.get h) (Fin.succ k) 0 *
              selectedPairDet (eraseFirstPartnerRows Z k) pairs) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        simp only [pairWedge]
        ring
    _ = 0 := by rw [hR, hL]; ring

theorem marked_powersetCard_sum {A : Type*} [AddCommMonoid A]
    (U : Finset I) (n : Nat) (F : I → Finset I → A) :
    (∑ chosen ∈ U.powersetCard (n + 1),
      ∑ t ∈ chosen, F t (chosen.erase t)) =
    ∑ t ∈ U, ∑ rest ∈ (U.erase t).powersetCard n, F t rest := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij'
      (fun marked _ ↦ ⟨marked.2, marked.1.erase marked.2⟩)
      (fun marked _ ↦ ⟨insert marked.1 marked.2, marked.1⟩) ?_ ?_ ?_ ?_ ?_
  · intro ⟨chosen, t⟩ hr
    simp only [Finset.mem_sigma, Finset.mem_powersetCard] at hr ⊢
    rcases hr with ⟨⟨hsub, hcard⟩, ht⟩
    refine ⟨hsub ht, ?_⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      exact Finset.mem_erase.mpr
        ⟨(Finset.mem_erase.mp hx).1, hsub (Finset.mem_erase.mp hx).2⟩
    · rw [Finset.card_erase_of_mem ht, hcard]
      omega
  · intro ⟨t, rest⟩ hr
    simp only [Finset.mem_sigma, Finset.mem_powersetCard] at hr ⊢
    rcases hr with ⟨htU, hsub, hcard⟩
    have htRest : t ∉ rest := by
      intro ht
      exact (Finset.mem_erase.mp (hsub ht)).1 rfl
    refine ⟨?_, Finset.mem_insert_self t rest⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with (rfl | hx)
      · exact htU
      · exact (Finset.mem_erase.mp (hsub hx)).2
    · rw [Finset.card_insert_of_notMem htRest, hcard]
  · intro ⟨chosen, t⟩ hr
    simp only [Finset.mem_sigma] at hr
    simp [Finset.insert_erase hr.2]
  · intro ⟨t, rest⟩ hr
    simp only [Finset.mem_sigma, Finset.mem_powersetCard] at hr
    have htRest : t ∉ rest := by
      intro ht
      exact (Finset.mem_erase.mp (hr.2.1 ht)).1 rfl
    simp [htRest]
  · intro ⟨chosen, t⟩ hr
    rfl

def finsetADMSRhs (m : Nat) (Z : I → Fin (2 * m) → Fin 2 → R)
    (w : I → R) (U : Finset I) : R :=
  ∑ S ∈ U.powersetCard m,
    (∏ t ∈ S, w t) * selectedPairDetFinset Z S

theorem finsetADMSRhs_marked_recurrence {n : Nat}
    (Z : I → Fin (2 * (n + 1)) → Fin 2 → R)
    (w : I → R) (U : Finset I) :
    finsetADMSRhs (n + 1) Z w U =
      ∑ t ∈ U, ∑ rest ∈ (U.erase t).powersetCard n,
        w t * (∏ r ∈ rest, w r) *
          (∑ k : Fin (2 * n + 1),
            (-1 : R) ^ (k : Nat) * pairWedge Z t 0 (Fin.succ k) *
              selectedPairDetFinset (eraseFirstPartnerRows Z k) rest) := by
  let F : I → Finset I → R := fun t rest ↦
    w t * (∏ r ∈ rest, w r) *
      (∑ k : Fin (2 * n + 1),
        (-1 : R) ^ (k : Nat) * pairWedge Z t 0 (Fin.succ k) *
          selectedPairDetFinset (eraseFirstPartnerRows Z k) rest)
  calc
    finsetADMSRhs (n + 1) Z w U =
        ∑ S ∈ U.powersetCard (n + 1), ∑ t ∈ S, F t (S.erase t) := by
      simp only [finsetADMSRhs]
      apply Finset.sum_congr rfl
      intro S hS
      have hs : S.card = n + 1 := (Finset.mem_powersetCard.mp hS).2
      rw [selectedPairDetFinset_owner_laplace Z S hs]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      dsimp only [F]
      rw [← Finset.mul_prod_erase S w ht]
    _ = ∑ t ∈ U, ∑ rest ∈ (U.erase t).powersetCard n, F t rest :=
      marked_powersetCard_sum U n F
    _ = _ := by rfl

theorem pairContraction_finset_mem_zero {n : Nat}
    (Z : I → Fin (2 * (n + 1)) → Fin 2 → R)
    (S : Finset I) (hs : S.card = n) {t : I} (ht : t ∈ S) :
    (∑ k : Fin (2 * n + 1),
      (-1 : R) ^ (k : Nat) * pairWedge Z t 0 (Fin.succ k) *
        selectedPairDetFinset (eraseFirstPartnerRows Z k) S) = 0 := by
  let e := sortedPairEquiv S hs
  let h : Fin n := e.symm ⟨t, ht⟩
  have heq : (sortedPairVectorOfCard S hs).get h = t := by
    rw [← sortedPairEquiv_apply]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨t, ht⟩)
  have hz := pairContraction_mem_zero Z (sortedPairVectorOfCard S hs) h
  calc
    _ = ∑ k : Fin (2 * n + 1),
        (-1 : R) ^ (k : Nat) * pairWedge Z t 0 (Fin.succ k) *
          selectedPairDet (eraseFirstPartnerRows Z k) (sortedPairVectorOfCard S hs) := by
      apply Fintype.sum_congr
      intro k
      rw [selectedPairDetFinset_eq _ _ hs]
    _ = 0 := by simpa only [heq] using hz

theorem weighted_contraction_powerset_erase {n : Nat}
    (Z : I → Fin (2 * (n + 1)) → Fin 2 → R) (w : I → R)
    (U : Finset I) {t : I} (_htU : t ∈ U) :
    (∑ S ∈ (U.erase t).powersetCard n,
      (∏ r ∈ S, w r) *
        (∑ k : Fin (2 * n + 1),
          (-1 : R) ^ (k : Nat) * pairWedge Z t 0 (Fin.succ k) *
            selectedPairDetFinset (eraseFirstPartnerRows Z k) S)) =
    ∑ S ∈ U.powersetCard n,
      (∏ r ∈ S, w r) *
        (∑ k : Fin (2 * n + 1),
          (-1 : R) ^ (k : Nat) * pairWedge Z t 0 (Fin.succ k) *
            selectedPairDetFinset (eraseFirstPartnerRows Z k) S) := by
  apply Finset.sum_subset
  · intro S hS
    rw [Finset.mem_powersetCard] at hS ⊢
    exact ⟨fun x hx ↦ (Finset.mem_erase.mp (hS.1 hx)).2, hS.2⟩
  · intro S hSU hSnot
    rw [Finset.mem_powersetCard] at hSU
    have htS : t ∈ S := by
      by_contra htS
      apply hSnot
      rw [Finset.mem_powersetCard]
      refine ⟨?_, hSU.2⟩
      intro x hx
      exact Finset.mem_erase.mpr ⟨by
        intro hxt
        subst x
        exact htS hx, hSU.1 hx⟩
    rw [pairContraction_finset_mem_zero Z S hSU.2 htS]
    simp

theorem contraction_expand_rhs {n : Nat}
    (Z : I → Fin (2 * (n + 1)) → Fin 2 → R) (w : I → R)
    (V : Finset I) (t : I) :
    (∑ k : Fin (2 * n + 1),
      (-1 : R) ^ (k : Nat) * pairWedge Z t 0 (Fin.succ k) *
        finsetADMSRhs n (eraseFirstPartnerRows Z k) w V) =
    ∑ S ∈ V.powersetCard n,
      (∏ r ∈ S, w r) *
        (∑ k : Fin (2 * n + 1),
          (-1 : R) ^ (k : Nat) * pairWedge Z t 0 (Fin.succ k) *
            selectedPairDetFinset (eraseFirstPartnerRows Z k) S) := by
  simp only [finsetADMSRhs]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem rhs_contraction_erase {n : Nat}
    (Z : I → Fin (2 * (n + 1)) → Fin 2 → R) (w : I → R)
    (U : Finset I) {t : I} (htU : t ∈ U) :
    (∑ k : Fin (2 * n + 1),
      (-1 : R) ^ (k : Nat) * pairWedge Z t 0 (Fin.succ k) *
        finsetADMSRhs n (eraseFirstPartnerRows Z k) w (U.erase t)) =
    ∑ k : Fin (2 * n + 1),
      (-1 : R) ^ (k : Nat) * pairWedge Z t 0 (Fin.succ k) *
        finsetADMSRhs n (eraseFirstPartnerRows Z k) w U := by
  rw [contraction_expand_rhs, contraction_expand_rhs]
  exact weighted_contraction_powerset_erase Z w U htU

def pullbackFinset {m : Nat} (Z : I → Fin (2 * m) → Fin 2 → R)
    (w : I → R) (U : Finset I) : Matrix (Fin (2 * m)) (Fin (2 * m)) R :=
  fun i j ↦ ∑ t ∈ U, w t * pairWedge Z t i j

theorem finsetADMSRhs_row_recurrence {n : Nat}
    (Z : I → Fin (2 * (n + 1)) → Fin 2 → R)
    (w : I → R) (U : Finset I) :
    finsetADMSRhs (n + 1) Z w U =
      ∑ k : Fin (2 * n + 1),
        (-1 : R) ^ (k : Nat) * pullbackFinset Z w U 0 (Fin.succ k) *
          finsetADMSRhs n (eraseFirstPartnerRows Z k) w U := by
  rw [finsetADMSRhs_marked_recurrence]
  calc
    _ = ∑ t ∈ U, w t *
        (∑ k : Fin (2 * n + 1),
          (-1 : R) ^ (k : Nat) * pairWedge Z t 0 (Fin.succ k) *
            finsetADMSRhs n (eraseFirstPartnerRows Z k) w (U.erase t)) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [contraction_expand_rhs]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rest hrest
      ring
    _ = ∑ t ∈ U, w t *
        (∑ k : Fin (2 * n + 1),
          (-1 : R) ^ (k : Nat) * pairWedge Z t 0 (Fin.succ k) *
            finsetADMSRhs n (eraseFirstPartnerRows Z k) w U) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [rhs_contraction_erase Z w U ht]
    _ = _ := by
      simp only [pullbackFinset]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro t ht
      ring

def recursivePf : (m : Nat) → Matrix (Fin (2 * m)) (Fin (2 * m)) R → R
  | 0, _ => 1
  | n + 1, A =>
      ∑ k : Fin (2 * n + 1),
        (-1 : R) ^ (k : Nat) * A 0 (Fin.succ k) *
          recursivePf n
            (A.submatrix (fun i ↦ Fin.succ (k.succAbove i))
              (fun j ↦ Fin.succ (k.succAbove j)))

omit [LinearOrder I] in
theorem pullbackFinset_eraseFirstPartnerRows {n : Nat}
    (Z : I → Fin (2 * (n + 1)) → Fin 2 → R)
    (w : I → R) (U : Finset I) (k : Fin (2 * n + 1)) :
    pullbackFinset (eraseFirstPartnerRows Z k) w U =
      (pullbackFinset Z w U).submatrix
        (fun i ↦ Fin.succ (k.succAbove i))
        (fun j ↦ Fin.succ (k.succAbove j)) := by
  rfl

theorem finsetADMSRhs_zero
    (Z : I → Fin 0 → Fin 2 → R) (w : I → R) (U : Finset I) :
    finsetADMSRhs 0 Z w U = 1 := by
  simp [finsetADMSRhs, selectedPairDetFinset, selectedPairDet,
    sortedPairVectorOfCard]

theorem recursivePf_pullbackFinset (m : Nat)
    (Z : I → Fin (2 * m) → Fin 2 → R) (w : I → R) (U : Finset I) :
    recursivePf m (pullbackFinset Z w U) = finsetADMSRhs m Z w U := by
  induction m with
  | zero =>
      rw [finsetADMSRhs_zero]
      rfl
  | succ n ih =>
      rw [finsetADMSRhs_row_recurrence]
      simp only [recursivePf]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← pullbackFinset_eraseFirstPartnerRows]
      rw [ih]

/--
The full symbolic `2m x 2s` AD-MS identity.  The `s` adjacent column pairs are
indexed by `Fin s`; every size-`m` subset contributes the determinant of its
literal selected square submatrix.
-/
theorem recursivePf_pullback_fin {m s : Nat}
    (Z : Fin s → Fin (2 * m) → Fin 2 → R) (w : Fin s → R) :
    recursivePf m (pullbackFinset Z w Finset.univ) =
      ∑ S ∈ Finset.univ.powersetCard m,
        (∏ t ∈ S, w t) * selectedPairDetFinset Z S := by
  simpa only [finsetADMSRhs] using
    (recursivePf_pullbackFinset m Z w (Finset.univ : Finset (Fin s)))

end ColomboGeneralK2
