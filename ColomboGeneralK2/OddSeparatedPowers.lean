import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue

/-!
# Shifted separated-power kernels

This file records the algebraic seam in the shifted-centre proof of the
separated-powers lemma.  The intended strictness statement is the all-rank
fact that, for strictly increasing lists `y`, `z` with `y i < z j` and
`m - 1 ≤ r`, the determinant of `(z j - y i)^r` is positive.

Mathlib supplies the ordinary Vandermonde determinant, but currently has no
generalized-Vandermonde sign theorem (nor a rectangular Cauchy--Binet minor
formula).  The factorisation below is the exact binomial expansion required
by that missing sign argument; it deliberately does not postulate a total
positivity hypothesis.
-/

open scoped BigOperators

open Finset Matrix

open Polynomial

namespace ColomboGeneralK2.OddSeparatedPowers

noncomputable section

/-- The separated power kernel. -/
def separatedPowerMatrix (m r : Nat) (y z : Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun i j ↦ (z j - y i) ^ r

/-- The left shifted-binomial factor, with the binomial coefficient included. -/
def shiftedLeft (m r : Nat) (c : ℝ) (y : Fin m → ℝ) :
    Matrix (Fin m) (Fin (r + 1)) ℝ :=
  fun i k ↦ (r.choose (k : Nat) : ℝ) * (c - y i) ^ (k : Nat)

/-- The right shifted-binomial factor. -/
def shiftedRight (m r : Nat) (c : ℝ) (z : Fin m → ℝ) :
    Matrix (Fin (r + 1)) (Fin m) ℝ :=
  fun k j ↦ (z j - c) ^ (r - (k : Nat))

/--
Shifting the centre does not change the kernel, and gives precisely the
binomial matrix factorisation used in the corrected strictness proof.
-/
theorem separatedPowerMatrix_eq_shifted_mul (m r : Nat) (c : ℝ)
    (y z : Fin m → ℝ) :
    separatedPowerMatrix m r y z = shiftedLeft m r c y * shiftedRight m r c z := by
  ext i j
  change (z j - y i) ^ r = ∑ k : Fin (r + 1),
    ((r.choose (k : Nat) : ℝ) * (c - y i) ^ (k : Nat)) *
      (z j - c) ^ (r - (k : Nat))
  rw [Finset.sum_fin_eq_sum_range]
  rw [show z j - y i = (c - y i) + (z j - c) by ring, add_pow]
  apply Finset.sum_congr rfl
  intro k hk
  rw [dif_pos (Finset.mem_range.mp hk)]
  ring

/-- A shift point turns a strict gap into positive coordinates on both sides. -/
theorem shifted_coordinates_pos {m : Nat} {c : ℝ} {y z : Fin m → ℝ}
    (hy : ∀ i, y i < c) (hz : ∀ j, c < z j) :
    (∀ i, 0 < c - y i) ∧ (∀ j, 0 < z j - c) := by
  constructor
  · intro i
    linarith [hy i]
  · intro j
    linarith [hz j]

/-! ## Generalized Vandermonde signs -/

/-- The monomial evaluation matrix used below. -/
def generalizedVandermonde (m : Nat) (x : Fin m → ℝ) (e : Fin m → Nat) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun i j ↦ x i ^ e j

/-- A nonzero real polynomial has strictly fewer sign variations than nonzero
coefficients.  This small complement to Descartes' rule is useful for sparse
polynomials. -/
theorem signVariations_lt_card_support {P : ℝ[X]} (hP : P ≠ 0) :
    P.signVariations < P.support.card := by
  induction hs : P.support.card using Nat.strong_induction_on generalizing P with
  | h n ih =>
      by_cases hE : P.eraseLead = 0
      · have hcard : P.support.card = 1 :=
          Polynomial.card_support_eq_one_of_eraseLead_eq_zero hP hE
        have hn : n = 1 := by omega
        subst n
        rw [← Polynomial.eraseLead_add_C_mul_X_pow P, hE, zero_add,
          Polynomial.C_mul_X_pow_eq_monomial]
        simp [hP]
      · have hlt : P.eraseLead.support.card < n := by
          rw [← hs]
          exact Polynomial.eraseLead_support_card_lt hP
        calc
          P.signVariations ≤ P.eraseLead.signVariations + 1 :=
            Polynomial.signVariations_le_eraseLead_succ P
          _ < P.eraseLead.support.card + 1 :=
            Nat.add_lt_add_right (ih _ hlt hE rfl) 1
          _ = P.support.card := Polynomial.card_support_eraseLead_add_one hP
          _ = n := hs

/-- The support of a finite sum of monomials is contained in the set of their
exponents. -/
theorem support_sum_monomial_subset {m : Nat} (e : Fin m → Nat) (a : Fin m → ℝ) :
    (∑ j, Polynomial.monomial (e j) (a j)).support ⊆ Finset.univ.image e := by
  intro n hn
  rw [Polynomial.mem_support_iff] at hn
  by_contra hne
  simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists] at hne
  have hcoeff : (∑ j, Polynomial.monomial (e j) (a j)).coeff n = 0 := by
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    apply Finset.sum_eq_zero
    intro j hj
    rw [if_neg]
    exact hne j
  exact hn hcoeff

/-- Distinct positive nodes and distinct exponents give a nonsingular
generalized Vandermonde matrix.  The proof uses the sparse form of Descartes'
rule of signs. -/
theorem generalizedVandermonde_det_ne_zero {m : Nat} {x : Fin m → ℝ}
    {e : Fin m → Nat} (hxpos : ∀ i, 0 < x i) (hxin : Function.Injective x)
    (hein : Function.Injective e) : (generalizedVandermonde m x e).det ≠ 0 := by
  intro hdet
  obtain ⟨a, ha, hMa⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let P : ℝ[X] := ∑ j, Polynomial.monomial (e j) (a j)
  have hP : P ≠ 0 := by
    intro hzero
    apply ha
    funext j
    have hcoeff := congr_arg (fun Q : ℝ[X] ↦ Q.coeff (e j)) hzero
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
      Polynomial.coeff_zero] at hcoeff
    rw [Finset.sum_eq_single j] at hcoeff
    · simpa using hcoeff
    · intro k hk hkj
      rw [if_neg]
      exact fun h ↦ hkj (hein h)
    · simp
  have hroot (i : Fin m) : x i ∈ P.roots := by
    rw [Polynomial.mem_roots hP, Polynomial.IsRoot.def]
    have hi := congr_fun hMa i
    simpa [P, Polynomial.eval_finsetSum, generalizedVandermonde, Matrix.mulVec,
      dotProduct, mul_comm] using hi
  have hroot_count : m ≤ P.roots.countP (0 < ·) := by
    rw [Multiset.countP_eq_card_filter]
    calc
      m = (Finset.univ.image x).card := by
        rw [Finset.card_image_of_injective _ hxin, Finset.card_univ, Fintype.card_fin]
      _ ≤ (P.roots.filter (0 < ·)).toFinset.card := by
        apply Finset.card_le_card
        intro u hu
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hu
        obtain ⟨i, rfl⟩ := hu
        simp [hroot i, hxpos i]
      _ ≤ (P.roots.filter (0 < ·)).card :=
        Multiset.toFinset_card_le (P.roots.filter (0 < ·))
  have hsupport : P.support.card ≤ m := by
    calc
      P.support.card ≤ (Finset.univ.image e).card :=
        Finset.card_le_card (support_sum_monomial_subset e a)
      _ ≤ Finset.univ.card := Finset.card_image_le
      _ = m := by simp
  have hdesc := Polynomial.roots_countP_pos_le_signVariations P
  have hsv := signVariations_lt_card_support hP
  omega

/-- At geometric positive nodes, a generalized Vandermonde is an ordinary
Vandermonde after transposition. -/
theorem generalizedVandermonde_two_pow_det_pos {m : Nat} {e : Fin m → Nat}
    (he : StrictMono e) :
    0 < (generalizedVandermonde m (fun i ↦ (2 : ℝ) ^ (i : Nat)) e).det := by
  have hmatrix : generalizedVandermonde m (fun i ↦ (2 : ℝ) ^ (i : Nat)) e =
      (Matrix.vandermonde fun j ↦ (2 : ℝ) ^ e j)ᵀ := by
    ext i j
    change ((2 : ℝ) ^ (i : Nat)) ^ e j = ((2 : ℝ) ^ e j) ^ (i : Nat)
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [hmatrix, Matrix.det_transpose, Matrix.det_vandermonde]
  apply Finset.prod_pos
  intro i hi
  apply Finset.prod_pos
  intro j hj
  rw [sub_pos]
  exact pow_lt_pow_right₀ (by norm_num) (he (Finset.mem_Ioi.mp hj))

/-- A generalized Vandermonde determinant is positive at positive strictly
increasing nodes and strictly increasing exponents.  Nonsingularity comes
from Descartes' rule; a straight-line deformation to geometric nodes fixes
the sign. -/
theorem generalizedVandermonde_det_pos {m : Nat} {x : Fin m → ℝ}
    {e : Fin m → Nat} (hxpos : ∀ i, 0 < x i) (hx : StrictMono x)
    (he : StrictMono e) : 0 < (generalizedVandermonde m x e).det := by
  let q : Fin m → ℝ := fun i ↦ (2 : ℝ) ^ (i : Nat)
  have hqpos : ∀ i, 0 < q i := fun i ↦ by simp [q]
  have hq : StrictMono q := by
    intro i j hij
    exact pow_lt_pow_right₀ (by norm_num) hij
  let path : ℝ → Fin m → ℝ := fun s i ↦ (1 - s) * x i + s * q i
  let f : ℝ → ℝ := fun s ↦ (generalizedVandermonde m (path s) e).det
  have hfcont : Continuous f := by
    apply Continuous.matrix_det
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    dsimp [f, generalizedVandermonde, path]
    fun_prop
  have hpath (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
      (∀ i, 0 < path s i) ∧ StrictMono (path s) := by
    have hs0 : 0 ≤ s := hs.1
    have hs1 : s ≤ 1 := hs.2
    have h1s : 0 ≤ 1 - s := sub_nonneg.mpr hs1
    constructor
    · intro i
      by_cases hsZ : s = 0
      · simp [path, hsZ, hxpos i]
      · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hsZ)
        have hleft : 0 ≤ (1 - s) * x i := mul_nonneg h1s (hxpos i).le
        have hright : 0 < s * q i := mul_pos hspos (hqpos i)
        simpa [path] using add_pos_of_nonneg_of_pos hleft hright
    · intro i j hij
      by_cases hsZ : s = 0
      · simpa [path, hsZ] using hx hij
      · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hsZ)
        have hleft : 0 ≤ (1 - s) * (x j - x i) :=
          mul_nonneg h1s (sub_nonneg.mpr (hx hij).le)
        have hright : 0 < s * (q j - q i) :=
          mul_pos hspos (sub_pos.mpr (hq hij))
        have hsum : 0 < (1 - s) * (x j - x i) + s * (q j - q i) :=
          add_pos_of_nonneg_of_pos hleft hright
        dsimp [path]
        linarith
  have hfne (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) : f s ≠ 0 := by
    have hp := hpath s hs
    exact generalizedVandermonde_det_ne_zero hp.1 hp.2.injective he.injective
  have hf1 : 0 < f 1 := by
    simpa [f, path, q] using generalizedVandermonde_two_pow_det_pos he
  have hf0nonneg : 0 ≤ f 0 := by
    by_contra hneg
    have hf0neg : f 0 < 0 := lt_of_not_ge hneg
    have hzmem : (0 : ℝ) ∈ Set.Icc (f 0) (f 1) := ⟨hf0neg.le, hf1.le⟩
    obtain ⟨s, hs, hfs⟩ :=
      intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hfcont.continuousOn hzmem
    exact hfne s hs (by simpa using hfs)
  have hf0ne : f 0 ≠ 0 := hfne 0 (by simp)
  have hf0pos : 0 < f 0 := lt_of_le_of_ne hf0nonneg (Ne.symm hf0ne)
  simpa [f, path] using hf0pos

/-! ## A finite rectangular Cauchy--Binet formula -/

/-- The range of an injection between finite ordinals, as a finset. -/
def injectionRange {m n : Nat} (p : Fin m → Fin n) : Finset (Fin n) :=
  Finset.univ.image p

/-- An injection onto its range, bundled as an equivalence. -/
noncomputable def injectionRangeEquiv {m n : Nat} (p : Fin m → Fin n)
    (hp : Function.Injective p) : Fin m ≃ injectionRange p :=
  Equiv.ofBijective (fun i ↦ ⟨p i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩) <| by
    constructor
    · intro i j hij
      exact hp (Subtype.ext_iff.mp hij)
    · intro u
      obtain ⟨i, hi, hpi⟩ := Finset.mem_image.mp u.2
      exact ⟨i, Subtype.ext hpi⟩

/-- The increasing enumeration of the range of an injection. -/
noncomputable def sortedInjection {m n : Nat} (p : Fin m → Fin n)
    (hp : Function.Injective p) : Fin m ↪o Fin n :=
  Finset.orderEmbOfFin (injectionRange p) <| by
    rw [injectionRange, Finset.card_image_of_injective _ hp, Finset.card_univ,
      Fintype.card_fin]

/-- The permutation which sorts an injection increasingly. -/
noncomputable def sortingPermutation {m n : Nat} (p : Fin m → Fin n)
    (hp : Function.Injective p) : Equiv.Perm (Fin m) :=
  (injectionRangeEquiv p hp).trans
    (Finset.orderIsoOfFin (injectionRange p) (by
      rw [injectionRange, Finset.card_image_of_injective _ hp, Finset.card_univ,
        Fintype.card_fin])).symm.toEquiv

@[simp]
theorem sortedInjection_sortingPermutation {m n : Nat} (p : Fin m → Fin n)
    (hp : Function.Injective p) (i : Fin m) :
    sortedInjection p hp (sortingPermutation p hp i) = p i := by
  let hs : (injectionRange p).card = m := by
    rw [injectionRange, Finset.card_image_of_injective _ hp, Finset.card_univ,
      Fintype.card_fin]
  change ((Finset.orderIsoOfFin (injectionRange p) hs)
      ((Finset.orderIsoOfFin (injectionRange p) hs).symm
        (injectionRangeEquiv p hp i)) : Fin n) = p i
  simp [injectionRangeEquiv]

set_option maxHeartbeats 800000 in
/-- Every injection of finite ordinals is uniquely an increasing injection
followed by a permutation. -/
noncomputable def injectionEquivSortedPerm (m n : Nat) :
    {p : Fin m → Fin n // Function.Injective p} ≃
      (Fin m ↪o Fin n) × Equiv.Perm (Fin m) :=
  (Equiv.ofBijective
    (fun p : (Fin m ↪o Fin n) × Equiv.Perm (Fin m) ↦
      ⟨fun i ↦ p.1 (p.2 i), p.1.injective.comp p.2.injective⟩) <| by
      constructor
      · rintro ⟨e, τ⟩ ⟨e', τ'⟩ h
        have hrange : Set.range e = Set.range e' := by
          ext u
          constructor
          · rintro ⟨i, rfl⟩
            refine ⟨τ' (τ.symm i), ?_⟩
            have hi := congr_fun (congr_arg Subtype.val h) (τ.symm i)
            simpa using hi.symm
          · rintro ⟨i, rfl⟩
            refine ⟨τ (τ'.symm i), ?_⟩
            have hi := congr_fun (congr_arg Subtype.val h) (τ'.symm i)
            simpa using hi
        have hfun : (e : Fin m → Fin n) = e' :=
          (e.strictMono.range_inj e'.strictMono).mp hrange
        have he : e = e' := DFunLike.ext e e' (congr_fun hfun)
        subst e'
        apply Prod.ext
        · rfl
        · apply Equiv.ext
          intro i
          apply e.injective
          exact congr_fun (congr_arg Subtype.val h) i
      · intro p
        refine ⟨⟨sortedInjection (p : Fin m → Fin n) p.2,
          sortingPermutation (p : Fin m → Fin n) p.2⟩, ?_⟩
        apply Subtype.ext
        funext i
        exact sortedInjection_sortingPermutation
          (p := (p : Fin m → Fin n)) (hp := p.property) i).symm

/-- The cancellation used in the determinant expansion when the chosen
intermediate-index map repeats a value. -/
theorem rectangular_det_mul_aux {m n : Nat} (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) {p : Fin m → Fin n}
    (hp : ¬Function.Injective p) :
    (∑ σ : Equiv.Perm (Fin m), Equiv.Perm.sign σ *
      ∏ i, A (σ i) (p i) * B (p i) i) = 0 := by
  obtain ⟨i, j, hpij, hij⟩ : ∃ i j, p i = p j ∧ i ≠ j := by
    rw [Function.Injective] at hp
    push Not at hp
    exact hp
  exact
    Finset.sum_involution (fun σ _ ↦ σ * Equiv.swap i j)
      (fun σ _ ↦ by
        have hprod : (∏ x, A (σ x) (p x)) =
            ∏ x, A ((σ * Equiv.swap i j) x) (p x) :=
          Fintype.prod_equiv (Equiv.swap i j) _ _ (by simp [Equiv.apply_swap_eq_self hpij])
        simp [hprod, Equiv.Perm.sign_swap hij, -Equiv.Perm.sign_swap',
          Finset.prod_mul_distrib])
      (fun σ _ _ ↦ (not_congr Equiv.mul_swap_eq_iff).mpr hij)
      (fun _ _ ↦ Finset.mem_univ _) fun σ _ ↦ Equiv.mul_swap_involutive i j σ

/-- The contribution of all reorderings of one fixed increasing subset is
the product of the corresponding two minors. -/
theorem cauchyBinet_fixed_embedding {m n : Nat}
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (e : Fin m ↪o Fin n) :
    (∑ τ : Equiv.Perm (Fin m), ∑ σ : Equiv.Perm (Fin m),
      Equiv.Perm.sign σ * ∏ i, A (σ i) (e (τ i)) * B (e (τ i)) i) =
      (A.submatrix id e).det * (B.submatrix e id).det := by
  calc
    _ = ∑ τ : Equiv.Perm (Fin m),
        (∏ i, B (e (τ i)) i) *
          (A.submatrix id (fun i ↦ e (τ i))).det := by
      apply Finset.sum_congr rfl
      intro τ hτ
      rw [Matrix.det_apply']
      simp only [Matrix.submatrix_apply, id_eq, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [Finset.prod_mul_distrib]
      ring
    _ = ∑ τ : Equiv.Perm (Fin m),
        (∏ i, B (e (τ i)) i) *
          (Equiv.Perm.sign τ * (A.submatrix id e).det) := by
      apply Finset.sum_congr rfl
      intro τ hτ
      rw [← Matrix.det_permute' τ (A.submatrix id e)]
      rfl
    _ = (A.submatrix id e).det *
        (∑ τ : Equiv.Perm (Fin m), Equiv.Perm.sign τ *
          ∏ i, B (e (τ i)) i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro τ hτ
      ring
    _ = (A.submatrix id e).det * (B.submatrix e id).det := by
      congr 1
      rw [Matrix.det_apply']
      simp

/-- Cauchy--Binet for the finite rectangular matrices needed here, indexed by
increasing embeddings of finite ordinals. -/
theorem rectangular_det_mul {m n : Nat} (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) :
    (A * B).det = ∑ e : Fin m ↪o Fin n,
      (A.submatrix id e).det * (B.submatrix e id).det := by
  calc
    (A * B).det = ∑ p : Fin m → Fin n, ∑ σ : Equiv.Perm (Fin m),
        Equiv.Perm.sign σ * ∏ i, A (σ i) (p i) * B (p i) i := by
      simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum,
        Finset.mul_sum, Fintype.piFinset_univ]
      rw [Finset.sum_comm]
    _ = ∑ p : Fin m → Fin n with Function.Injective p,
        ∑ σ : Equiv.Perm (Fin m), Equiv.Perm.sign σ *
          ∏ i, A (σ i) (p i) * B (p i) i := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) fun p hp hpinj ↦ ?_).symm
      apply rectangular_det_mul_aux A B
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hpinj
    _ = ∑ p : {p : Fin m → Fin n // Function.Injective p},
        ∑ σ : Equiv.Perm (Fin m), Equiv.Perm.sign σ *
          ∏ i, A (σ i) ((p : Fin m → Fin n) i) *
            B ((p : Fin m → Fin n) i) i := by
      apply Finset.sum_subtype
      intro p
      simp
    _ = ∑ p : (Fin m ↪o Fin n) × Equiv.Perm (Fin m),
        ∑ σ : Equiv.Perm (Fin m), Equiv.Perm.sign σ *
          ∏ i, A (σ i) (p.1 (p.2 i)) * B (p.1 (p.2 i)) i := by
      symm
      apply Fintype.sum_equiv (injectionEquivSortedPerm m n).symm
      intro p
      rfl
    _ = ∑ e : Fin m ↪o Fin n,
        (A.submatrix id e).det * (B.submatrix e id).det := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro e he
      exact cauchyBinet_fixed_embedding A B e

/-! ## Positivity of the shifted factorisation -/

/-- After the row reversal, every maximal minor of the left shifted factor
has positive signed determinant. -/
theorem shiftedLeft_minor_signed_pos {m r : Nat} {c : ℝ} {y : Fin m → ℝ}
    (hy : StrictMono y) (hypos : ∀ i, 0 < c - y i) (e : Fin m ↪o Fin (r + 1)) :
    0 < ((Fin.revPerm (n := m)).sign : ℝ) *
      ((shiftedLeft m r c y).submatrix id e).det := by
  let x : Fin m → ℝ := fun i ↦ c - y i
  let xr : Fin m → ℝ := fun i ↦ x i.rev
  let ex : Fin m → Nat := fun k ↦ (e k : Nat)
  have hxrpos : ∀ i, 0 < xr i := fun i ↦ hypos i.rev
  have hxr : StrictMono xr := by
    intro i j hij
    have hrev : j.rev < i.rev := by
      rw [Fin.rev_lt_rev]
      exact hij
    dsimp [xr, x]
    linarith [hy hrev]
  have hex : StrictMono ex := by
    intro i j hij
    exact e.strictMono hij
  have hG : 0 < (generalizedVandermonde m xr ex).det :=
    generalizedVandermonde_det_pos hxrpos hxr hex
  let coeff : Fin m → ℝ := fun k ↦ r.choose (e k : Nat)
  have hcoeff : ∀ k, 0 < coeff k := by
    intro k
    change 0 < (r.choose (e k : Nat) : ℝ)
    exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ (e k).isLt)
  have hcoeffprod : 0 < ∏ k, coeff k :=
    Finset.prod_pos fun k hk ↦ hcoeff k
  let L : Matrix (Fin m) (Fin m) ℝ := (shiftedLeft m r c y).submatrix id e
  have hmatrix : L.submatrix Fin.revPerm id =
      Matrix.of fun i k ↦ coeff k * generalizedVandermonde m xr ex i k := by
    ext i k
    rfl
  have hdet : (L.submatrix Fin.revPerm id).det =
      (∏ k, coeff k) * (generalizedVandermonde m xr ex).det := by
    rw [hmatrix, Matrix.det_mul_row]
  have hprod : 0 < (∏ k, coeff k) * (generalizedVandermonde m xr ex).det :=
    mul_pos hcoeffprod hG
  rw [← hdet, Matrix.det_permute] at hprod
  exact hprod

/-- Every maximal minor of the right shifted factor has the same positive
signed determinant after reversing its exponent rows. -/
theorem shiftedRight_minor_signed_pos {m r : Nat} {c : ℝ} {z : Fin m → ℝ}
    (hz : StrictMono z) (hzpos : ∀ j, 0 < z j - c) (e : Fin m ↪o Fin (r + 1)) :
    0 < ((Fin.revPerm (n := m)).sign : ℝ) *
      ((shiftedRight m r c z).submatrix e id).det := by
  let t : Fin m → ℝ := fun j ↦ z j - c
  let ex : Fin m → Nat := fun k ↦ r - (e k.rev : Nat)
  have htpos : ∀ j, 0 < t j := hzpos
  have ht : StrictMono t := by
    intro i j hij
    dsimp [t]
    linarith [hz hij]
  have hex : StrictMono ex := by
    intro i j hij
    have hrev : j.rev < i.rev := by
      rw [Fin.rev_lt_rev]
      exact hij
    have heij : (e j.rev : Nat) < (e i.rev : Nat) := e.strictMono hrev
    have hei : (e i.rev : Nat) ≤ r := Nat.le_of_lt_succ (e i.rev).isLt
    have hej : (e j.rev : Nat) ≤ r := Nat.le_of_lt_succ (e j.rev).isLt
    dsimp [ex]
    omega
  have hG : 0 < (generalizedVandermonde m t ex).det :=
    generalizedVandermonde_det_pos htpos ht hex
  let R : Matrix (Fin m) (Fin m) ℝ := (shiftedRight m r c z).submatrix e id
  have hmatrix : R.transpose.submatrix id Fin.revPerm = generalizedVandermonde m t ex := by
    ext i k
    rfl
  rw [← hmatrix, Matrix.det_permute', Matrix.det_transpose] at hG
  exact hG

/-- Every Cauchy--Binet summand in the shifted factorisation is strictly
positive. -/
theorem shifted_minors_product_pos {m r : Nat} {c : ℝ} {y z : Fin m → ℝ}
    (hy : StrictMono y) (hz : StrictMono z) (hypos : ∀ i, 0 < c - y i)
    (hzpos : ∀ j, 0 < z j - c) (e : Fin m ↪o Fin (r + 1)) :
    0 < ((shiftedLeft m r c y).submatrix id e).det *
      ((shiftedRight m r c z).submatrix e id).det := by
  have hL := shiftedLeft_minor_signed_pos hy hypos e
  have hR := shiftedRight_minor_signed_pos hz hzpos e
  have hprod := mul_pos hL hR
  rcases Int.units_eq_one_or (Fin.revPerm (n := m)).sign with hs | hs
  · simpa [hs] using hprod
  · simp [hs] at hprod
    nlinarith

/-- Strict positivity of the separated-powers determinant in a strict gap. -/
theorem separatedPowerMatrix_det_pos {m r : Nat} {y z : Fin m → ℝ}
    (hy : StrictMono y) (hz : StrictMono z) (hyz : ∀ i j, y i < z j)
    (hmr : m - 1 ≤ r) : 0 < (separatedPowerMatrix m r y z).det := by
  cases m with
  | zero => simp
  | succ n =>
      let c : ℝ := (y (Fin.last n) + z 0) / 2
      have hyc : ∀ i, y i < c := by
        intro i
        have hiy : y i ≤ y (Fin.last n) := hy.monotone (Fin.le_last i)
        have hgap : y (Fin.last n) < z 0 := hyz (Fin.last n) 0
        dsimp [c]
        linarith
      have hcz : ∀ j, c < z j := by
        intro j
        have hzj : z 0 ≤ z j := hz.monotone (Fin.zero_le j)
        have hgap : y (Fin.last n) < z 0 := hyz (Fin.last n) 0
        dsimp [c]
        linarith
      obtain ⟨hypos, hzpos⟩ := shifted_coordinates_pos hyc hcz
      have hmn : n + 1 ≤ r + 1 := by omega
      rw [separatedPowerMatrix_eq_shifted_mul, rectangular_det_mul]
      apply Finset.sum_pos
      · intro e he
        exact shifted_minors_product_pos hy hz hypos hzpos e
      · exact ⟨Fin.castLEOrderEmb hmn, Finset.mem_univ _⟩

/-- The raw-matrix formulation of `separatedPowerMatrix_det_pos`. -/
theorem separatedPowers_det_pos {m r : Nat} {y z : Fin m → ℝ}
    (hy : StrictMono y) (hz : StrictMono z) (hyz : ∀ i j, y i < z j)
    (hmr : m - 1 ≤ r) :
    0 < (Matrix.of fun i j ↦ (z j - y i) ^ r : Matrix (Fin m) (Fin m) ℝ).det := by
  exact separatedPowerMatrix_det_pos hy hz hyz hmr

/-- The transposed/right-factor separated-powers determinant has the same
strict positivity. -/
theorem transposedSeparatedPowerMatrix_det_pos {m r : Nat} {y z : Fin m → ℝ}
    (hy : StrictMono y) (hz : StrictMono z) (hyz : ∀ i j, y i < z j)
    (hmr : m - 1 ≤ r) :
    0 < (Matrix.of fun i j ↦ (z i - y j) ^ r : Matrix (Fin m) (Fin m) ℝ).det := by
  have h := separatedPowerMatrix_det_pos hy hz hyz hmr
  have hmatrix : (Matrix.of fun i j ↦ (z i - y j) ^ r :
      Matrix (Fin m) (Fin m) ℝ) = (separatedPowerMatrix m r y z)ᵀ := by
    rfl
  rw [hmatrix, Matrix.det_transpose]
  exact h

/-- The form used for the right block: the upper points index rows and the
lower points index columns. -/
theorem rightSeparatedPowers_det_pos {m r : Nat} {z w : Fin m → ℝ}
    (hz : StrictMono z) (hw : StrictMono w) (hzw : ∀ i j, z i < w j)
    (hmr : m - 1 ≤ r) :
    0 < (Matrix.of fun i j ↦ (w i - z j) ^ r : Matrix (Fin m) (Fin m) ℝ).det := by
  exact transposedSeparatedPowerMatrix_det_pos hz hw hzw hmr

end

end ColomboGeneralK2.OddSeparatedPowers
