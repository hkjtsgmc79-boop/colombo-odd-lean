import ColomboGeneralK2.OddDeBruijnAnalyticTargets

/-!
# Measure-theoretic labelled de Bruijn identity

This file proves the arbitrary-size full-domain identity frozen in
`OddDeBruijnAnalyticTargets`.  The proof follows the owner-pair Laplace
recursion from `GeneralADPf`: after removing one labelled integration
coordinate, finite-product Fubini separates its wedge factor from the
remaining determinant.  `PairIntegrable` is exactly what is needed for the
finite sums under the integral.
-/

namespace ColomboGeneralK2.Odd

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {X : Type*} [MeasurableSpace X] (mu : Measure X)

/-- `PairIntegrable` also controls the reversed monomial in a wedge. -/
theorem pairWedge_integrable {m : Nat}
    {Z : X → Fin (2 * m) → Fin 2 → Real}
    (hZ : PairIntegrable mu Z) (i j : Fin (2 * m)) :
    Integrable (fun t ↦ pairWedge Z t i j) mu := by
  have hij := hZ i j
  have hji := hZ j i
  apply hij.sub
  simpa only [mul_comm] using hji

/-- Deleting the two owner rows preserves the entrywise integrability
hypothesis needed by the recursive Pfaffian. -/
theorem pairIntegrable_eraseFirstPartnerRows {n : Nat}
    {Z : X → Fin (2 * (n + 1)) → Fin 2 → Real}
    (hZ : PairIntegrable mu Z) (k : Fin (2 * n + 1)) :
    PairIntegrable mu (eraseFirstPartnerRows Z k) := by
  intro i j
  simpa only [eraseFirstPartnerRows] using
    hZ (Fin.succ (k.succAbove i)) (Fin.succ (k.succAbove j))

/-- Fubini after separating one coordinate of a finite product.  This scalar
identity is valid with the Bochner integral's usual zero convention; the
integrability hypotheses are needed separately when distributing integrals
over finite sums. -/
theorem integral_mul_coord_erase {n : Nat} (h : Fin (n + 1))
    [SigmaFinite mu]
    (f : X → Real) (g : (Fin n → X) → Real) :
    (∫ t : Fin (n + 1) → X,
        f (t h) * g (fun q ↦ t (h.succAbove q))
        ∂(Measure.pi fun _ : Fin (n + 1) ↦ mu)) =
      (∫ x, f x ∂mu) *
        ∫ y : Fin n → X, g y ∂(Measure.pi fun _ : Fin n ↦ mu) := by
  calc
    _ = ∫ z : X × (Fin n → X), f z.1 * g z.2
        ∂(mu.prod (Measure.pi fun _ : Fin n ↦ mu)) := by
      rw [← (measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) ↦ mu) h).integral_comp']
      rfl
    _ = _ := integral_prod_mul f g

/-- Integrable version of `integral_mul_coord_erase`. -/
theorem integrable_mul_coord_erase {n : Nat} (h : Fin (n + 1))
    [SigmaFinite mu]
    {f : X → Real} {g : (Fin n → X) → Real}
    (hf : Integrable f mu)
    (hg : Integrable g (Measure.pi fun _ : Fin n ↦ mu)) :
    Integrable
      (fun t : Fin (n + 1) → X ↦
        f (t h) * g (fun q ↦ t (h.succAbove q)))
      (Measure.pi fun _ : Fin (n + 1) ↦ mu) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ X) h
  have hp : Integrable (fun z : X × (Fin n → X) ↦ f z.1 * g z.2)
      (mu.prod (Measure.pi fun _ : Fin n ↦ mu)) :=
    hf.mul_prod hg
  have hc := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) ↦ mu) h).integrable_comp_of_integrable hp
  change Integrable ((fun z : X × (Fin n → X) ↦ f z.1 * g z.2) ∘ e)
    (Measure.pi fun _ : Fin (n + 1) ↦ mu)
  exact hc

/-- Owner-pair Laplace expansion specialized to a labelled function tuple. -/
theorem selectedPairDet_ofFn_owner_laplace {n : Nat}
    {I : Type*} (Z : I → Fin (2 * (n + 1)) → Fin 2 → Real)
    (t : Fin (n + 1) → I) :
    selectedPairDet Z (List.Vector.ofFn t) =
      ∑ h : Fin (n + 1), ∑ k : Fin (2 * n + 1),
        (-1 : Real) ^ (k : Nat) * pairWedge Z (t h) 0 (Fin.succ k) *
          selectedPairDet (eraseFirstPartnerRows Z k)
            (List.Vector.ofFn fun q ↦ t (h.succAbove q)) := by
  simpa only [List.Vector.get_ofFn, erasePairVector] using
    selectedPairDet_owner_laplace Z (List.Vector.ofFn t)

/-- The labelled determinant is integrable on the full finite product under
the frozen entrywise hypothesis. -/
theorem selectedPairDet_ofFn_integrable [SigmaFinite mu] : ∀ {m : Nat}
    (Z : X → Fin (2 * m) → Fin 2 → Real), PairIntegrable mu Z →
      Integrable (fun t : Fin m → X ↦
        selectedPairDet Z (List.Vector.ofFn t))
        (Measure.pi fun _ : Fin m ↦ mu) := by
  intro m
  induction m with
  | zero =>
      intro Z hZ
      letI : IsFiniteMeasure (Measure.pi fun _ : Fin 0 ↦ mu) :=
        ⟨by rw [Measure.pi_empty_univ]; exact ENNReal.one_lt_top⟩
      simp [selectedPairDet]
  | succ n ih =>
      intro Z hZ
      rw [show (fun t : Fin (n + 1) → X ↦
          selectedPairDet Z (List.Vector.ofFn t)) =
          fun t ↦ ∑ h : Fin (n + 1), ∑ k : Fin (2 * n + 1),
            (-1 : Real) ^ (k : Nat) * pairWedge Z (t h) 0 (Fin.succ k) *
              selectedPairDet (eraseFirstPartnerRows Z k)
                (List.Vector.ofFn fun q ↦ t (h.succAbove q)) by
        funext t
        exact selectedPairDet_ofFn_owner_laplace Z t]
      apply integrable_finsetSum Finset.univ
      intro h hh
      apply integrable_finsetSum Finset.univ
      intro k hk
      have hw : Integrable (fun x ↦ pairWedge Z x 0 (Fin.succ k)) mu :=
        pairWedge_integrable mu hZ 0 (Fin.succ k)
      have hd : Integrable
          (fun y : Fin n → X ↦ selectedPairDet (eraseFirstPartnerRows Z k)
            (List.Vector.ofFn y))
          (Measure.pi fun _ : Fin n ↦ mu) :=
        ih (eraseFirstPartnerRows Z k)
          (pairIntegrable_eraseFirstPartnerRows mu hZ k)
      have hp := integrable_mul_coord_erase mu h hw hd
      simpa only [mul_assoc] using
        hp.const_mul ((-1 : Real) ^ (k : Nat))

/-- Integrating the owner-pair Laplace expansion separates the chosen wedge
from the determinant in the remaining coordinates. -/
theorem integral_selectedPairDet_ofFn_succ {n : Nat}
    [SigmaFinite mu]
    (Z : X → Fin (2 * (n + 1)) → Fin 2 → Real)
    (hZ : PairIntegrable mu Z) :
    (∫ t : Fin (n + 1) → X,
        selectedPairDet Z (List.Vector.ofFn t)
        ∂(Measure.pi fun _ : Fin (n + 1) ↦ mu)) =
      ∑ _h : Fin (n + 1), ∑ k : Fin (2 * n + 1),
        (-1 : Real) ^ (k : Nat) *
          (∫ x, pairWedge Z x 0 (Fin.succ k) ∂mu) *
          ∫ y : Fin n → X,
            selectedPairDet (eraseFirstPartnerRows Z k) (List.Vector.ofFn y)
            ∂(Measure.pi fun _ : Fin n ↦ mu) := by
  have hterm : ∀ (h : Fin (n + 1)) (k : Fin (2 * n + 1)),
      Integrable
        (fun t : Fin (n + 1) → X ↦
          (-1 : Real) ^ (k : Nat) * pairWedge Z (t h) 0 (Fin.succ k) *
            selectedPairDet (eraseFirstPartnerRows Z k)
              (List.Vector.ofFn fun q ↦ t (h.succAbove q)))
        (Measure.pi fun _ : Fin (n + 1) ↦ mu) := by
    intro h k
    have hw : Integrable (fun x ↦ pairWedge Z x 0 (Fin.succ k)) mu :=
      pairWedge_integrable mu hZ 0 (Fin.succ k)
    have hd : Integrable
        (fun y : Fin n → X ↦ selectedPairDet (eraseFirstPartnerRows Z k)
          (List.Vector.ofFn y))
        (Measure.pi fun _ : Fin n ↦ mu) :=
      selectedPairDet_ofFn_integrable mu (eraseFirstPartnerRows Z k)
        (pairIntegrable_eraseFirstPartnerRows mu hZ k)
    have hp := integrable_mul_coord_erase mu h hw hd
    simpa only [mul_assoc] using hp.const_mul ((-1 : Real) ^ (k : Nat))
  calc
    _ = ∫ t : Fin (n + 1) → X,
        ∑ h : Fin (n + 1), ∑ k : Fin (2 * n + 1),
          (-1 : Real) ^ (k : Nat) * pairWedge Z (t h) 0 (Fin.succ k) *
            selectedPairDet (eraseFirstPartnerRows Z k)
              (List.Vector.ofFn fun q ↦ t (h.succAbove q))
        ∂(Measure.pi fun _ : Fin (n + 1) ↦ mu) := by
      apply integral_congr_ae
      filter_upwards [] with t
      exact selectedPairDet_ofFn_owner_laplace Z t
    _ = ∑ h : Fin (n + 1), ∑ k : Fin (2 * n + 1),
        ∫ t : Fin (n + 1) → X,
          (-1 : Real) ^ (k : Nat) * pairWedge Z (t h) 0 (Fin.succ k) *
            selectedPairDet (eraseFirstPartnerRows Z k)
              (List.Vector.ofFn fun q ↦ t (h.succAbove q))
          ∂(Measure.pi fun _ : Fin (n + 1) ↦ mu) := by
      rw [integral_finsetSum Finset.univ]
      · apply Fintype.sum_congr
        intro h
        rw [integral_finsetSum Finset.univ]
        intro k hk
        exact hterm h k
      · intro h hh
        exact integrable_finsetSum Finset.univ (fun k hk ↦ hterm h k)
    _ = _ := by
      apply Fintype.sum_congr
      intro h
      apply Fintype.sum_congr
      intro k
      calc
        (∫ t : Fin (n + 1) → X,
            (-1 : Real) ^ (k : Nat) * pairWedge Z (t h) 0 (Fin.succ k) *
              selectedPairDet (eraseFirstPartnerRows Z k)
                (List.Vector.ofFn fun q ↦ t (h.succAbove q))
            ∂(Measure.pi fun _ : Fin (n + 1) ↦ mu)) =
            (-1 : Real) ^ (k : Nat) *
              ∫ t : Fin (n + 1) → X,
                pairWedge Z (t h) 0 (Fin.succ k) *
                  selectedPairDet (eraseFirstPartnerRows Z k)
                    (List.Vector.ofFn fun q ↦ t (h.succAbove q))
                ∂(Measure.pi fun _ : Fin (n + 1) ↦ mu) := by
          simpa only [mul_assoc] using integral_const_mul
            ((-1 : Real) ^ (k : Nat))
            (fun t : Fin (n + 1) → X ↦
              pairWedge Z (t h) 0 (Fin.succ k) *
                selectedPairDet (eraseFirstPartnerRows Z k)
                  (List.Vector.ofFn fun q ↦ t (h.succAbove q)))
        _ = _ := by
          rw [integral_mul_coord_erase mu h
            (fun x ↦ pairWedge Z x 0 (Fin.succ k))
            (fun y ↦ selectedPairDet (eraseFirstPartnerRows Z k)
              (List.Vector.ofFn y))]
          ring

/-- The moment matrix of an owner-row deletion is the corresponding
submatrix of the original moment matrix. -/
theorem integral_pairWedge_eraseFirstPartnerRows {n : Nat}
    (Z : X → Fin (2 * (n + 1)) → Fin 2 → Real)
    (k : Fin (2 * n + 1)) :
    (fun i j ↦ ∫ x, pairWedge (eraseFirstPartnerRows Z k) x i j ∂mu) =
      Matrix.submatrix
        ((fun i j ↦ ∫ x, pairWedge Z x i j ∂mu) :
          Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) Real)
        (fun i ↦ Fin.succ (k.succAbove i))
        (fun j ↦ Fin.succ (k.succAbove j)) := by
  rfl

/-- Factorial form of the arbitrary-size labelled full-domain de Bruijn
identity.  Keeping the factorial on the Pfaffian side makes the recursive
proof and its normalization explicit. -/
theorem factorial_mul_recursivePf_eq_integral_selectedPairDet [SigmaFinite mu] : ∀ {m : Nat}
    (Z : X → Fin (2 * m) → Fin 2 → Real), PairIntegrable mu Z →
      (Nat.factorial m : Real) *
          recursivePf m (fun i j ↦ ∫ x, pairWedge Z x i j ∂mu) =
        ∫ t : Fin m → X, selectedPairDet Z (List.Vector.ofFn t)
          ∂(Measure.pi fun _ : Fin m ↦ mu) := by
  intro m
  induction m with
  | zero =>
      intro Z hZ
      simp [recursivePf, selectedPairDet, measureReal_def]
  | succ n ih =>
      intro Z hZ
      rw [integral_selectedPairDet_ofFn_succ mu Z hZ]
      simp_rw [← ih (eraseFirstPartnerRows Z _)
        (pairIntegrable_eraseFirstPartnerRows mu hZ _)]
      simp only [recursivePf, Nat.factorial_succ]
      simp_rw [integral_pairWedge_eraseFirstPartnerRows mu]
      rw [Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro k
      push_cast
      ring

/-- Arbitrary-size measure-theoretic de Bruijn identity on the labelled full
domain, with the coefficient in the paper-facing `1 / m!` direction. -/
theorem recursivePf_debruijn_full_domain {m : Nat}
    [SigmaFinite mu]
    (Z : X → Fin (2 * m) → Fin 2 → Real)
    (hZ : PairIntegrable mu Z) :
    recursivePf m (fun i j ↦ ∫ x, pairWedge Z x i j ∂mu) =
      fullDomainCoefficient m *
        ∫ t : Fin m → X,
          (selectedPairMatrix Z (List.Vector.ofFn t)).det
          ∂(Measure.pi fun _ : Fin m ↦ mu) := by
  have hfactorial :=
    factorial_mul_recursivePf_eq_integral_selectedPairDet mu Z hZ
  change recursivePf m (fun i j ↦ ∫ x, pairWedge Z x i j ∂mu) =
    fullDomainCoefficient m *
      ∫ t : Fin m → X, selectedPairDet Z (List.Vector.ofFn t)
        ∂(Measure.pi fun _ : Fin m ↦ mu)
  rw [← hfactorial]
  simp only [fullDomainCoefficient]
  have hne : (Nat.factorial m : Real) ≠ 0 := by positivity
  field_simp

/-- The frozen MVP-1 full-domain target is inhabited under exactly its
declared hypotheses. -/
theorem recursivePf_beta_debruijn_full_domain {m : Nat}
    [SigmaFinite mu]
    (Z : X → Fin (2 * m) → Fin 2 → Real) :
    FullDomainDeBruijnTarget mu m Z := by
  intro hZ
  exact recursivePf_debruijn_full_domain mu Z hZ

end

end ColomboGeneralK2.Odd
