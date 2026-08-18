import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Order.Interval.Finset.Fin
import ColomboGeneralK2.OddFiniteBSpline
import ColomboGeneralK2.OddStaircaseSupport

open scoped BigOperators

namespace ColomboGeneralK2.Odd

noncomputable section

def insertPos {n : Nat} [NeZero n] (K : Fin n → ℝ) (τ : ℝ) : Nat :=
  (Finset.univ.filter (fun i : Fin n ↦ K i < τ)).card

theorem insertPos_le {n : Nat} [NeZero n] (K : Fin n → ℝ) (τ : ℝ) :
    insertPos K τ ≤ n := by
  unfold insertPos
  have h : (Finset.univ.filter (fun i : Fin n ↦ K i < τ)).card ≤
      (Finset.univ : Finset (Fin n)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  simpa [Finset.card_univ, Fintype.card_fin] using h

def insertKnot {n : Nat} [NeZero n] (K : Fin n → ℝ) (τ : ℝ) : Fin (n + 1) → ℝ :=
  fun i ↦
    if h1 : (i : Nat) < insertPos K τ then
      K ⟨(i : Nat), lt_of_lt_of_le h1 (insertPos_le K τ)⟩
    else if h2 : (i : Nat) = insertPos K τ then τ
    else K ⟨(i : Nat) - 1, by
      have hi : (i : Nat) < n + 1 := i.2
      have hnlt : ¬ (i : Nat) < insertPos K τ := h1
      have hneq : (i : Nat) ≠ insertPos K τ := h2
      omega⟩

/-- The cardinality of the set of `Fin n` elements below a bound. -/
lemma card_fin_below (n k : Nat) (hk : k ≤ n) :
    (Finset.univ.filter (fun j : Fin n ↦ (j : Nat) < k)).card = k := by
  let e : Fin k ↪ Fin n :=
    ⟨fun i ↦ ⟨i.1, lt_of_lt_of_le i.2 hk⟩, by
      intro a b h
      exact Fin.ext (by simpa using congrArg Fin.val h)⟩
  have hE : Finset.univ.filter (fun j : Fin n ↦ (j : Nat) < k) = Finset.univ.map e := by
    ext j
    constructor
    · intro hj
      rw [Finset.mem_map]
      refine ⟨⟨j.1, by simpa using (Finset.mem_filter.mp hj).2⟩, Finset.mem_univ _, ?_⟩
      ext
      rfl
    · intro hj
      rw [Finset.mem_map] at hj
      rcases hj with ⟨i, _, hi⟩
      rw [Finset.mem_filter]
      constructor
      · exact Finset.mem_univ _
      · rw [← hi]
        exact i.2
  rw [hE, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- The knots strictly below `τ` form a downward-closed set. -/
lemma insertPos_dclosed {n : Nat} [NeZero n] {K : Fin n → ℝ} (hK : Monotone K)
    {i j : Fin n} (hj : K j < τ) (hij : i ≤ j) : K i < τ :=
  lt_of_le_of_lt (hK hij) hj

/-- For a monotone knot vector the knots below `τ` are exactly the initial
segment `{0, ..., insertPos K τ - 1}`. -/
theorem insertPos_lt_iff {n : Nat} [NeZero n] {K : Fin n → ℝ} (hK : Monotone K)
    (τ : ℝ) (i : Fin n) :
    K i < τ ↔ (i : Nat) < insertPos K τ := by
  let S : Finset (Fin n) := Finset.univ.filter (fun i : Fin n ↦ K i < τ)
  have hdown : ∀ ⦃i j : Fin n⦄, j ∈ S → i ≤ j → i ∈ S := by
    intro i j hj hij
    rw [Finset.mem_filter] at hj ⊢
    exact ⟨Finset.mem_univ _, insertPos_dclosed hK hj.2 hij⟩
  have hcard_lt : ∀ i : Fin n,
      (Finset.univ.filter (fun j : Fin n ↦ (j : Nat) < (i : Nat))).card = (i : Nat) := by
    intro i
    exact card_fin_below n (i : Nat) (le_of_lt i.2)
  have hS : S = Finset.univ.filter (fun i : Fin n ↦ (i : Nat) < S.card) := by
    ext i
    constructor
    · intro hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_contra hnot
      have hsub : Finset.univ.filter (fun j : Fin n ↦ (j : Nat) ≤ (i : Nat)) ⊆ S := by
        intro j hj
        have hjle : (j : Nat) ≤ (i : Nat) := (Finset.mem_filter.mp hj).2
        have hij : j ≤ i := Fin.le_iff_val_le_val.mpr hjle
        exact hdown hi hij
      have hcard : (Finset.univ.filter (fun j : Fin n ↦ (j : Nat) ≤ (i : Nat))).card =
          (i : Nat) + 1 := by
        have hE : (Finset.univ.filter (fun j : Fin n ↦ (j : Nat) ≤ (i : Nat))) =
            Finset.univ.filter (fun j : Fin n ↦ (j : Nat) < (i : Nat) + 1) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          omega
        rw [hE, card_fin_below n ((i : Nat) + 1) (by omega)]
      have hge : (i : Nat) + 1 ≤ S.card := by
        rw [← hcard]
        exact Finset.card_le_card hsub
      omega
    · intro hi
      rw [Finset.mem_filter] at hi
      by_contra hnot
      have hsub : S ⊆ Finset.univ.filter (fun j : Fin n ↦ (j : Nat) < (i : Nat)) := by
        intro j hj
        by_contra hnotj
        have hlt_not : ¬ (j : Nat) < (i : Nat) := by
          intro hlt
          exact hnotj (by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hlt⟩)
        have hij : i ≤ j := Fin.le_iff_val_le_val.mpr (not_lt.mp hlt_not)
        exact hnot (hdown hj hij)
      have hcard : (Finset.univ.filter (fun j : Fin n ↦ (j : Nat) < (i : Nat))).card = (i : Nat) :=
        card_fin_below n (i : Nat) (le_of_lt i.2)
      have hle : S.card ≤ (i : Nat) := by
        rw [← hcard]
        exact Finset.card_le_card hsub
      omega
  unfold insertPos
  constructor
  · intro hi
    have hmem : i ∈ S := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hi⟩
    rw [hS] at hmem
    exact (Finset.mem_filter.mp hmem).2
  · intro hi
    have hmem : i ∈ Finset.univ.filter (fun i : Fin n ↦ (i : Nat) < S.card) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by simpa [S] using hi⟩
    rw [← hS] at hmem
    exact (Finset.mem_filter.mp hmem).2

/-- Knots at positions `≥ insertPos` are `≥ τ`. -/
theorem insertPos_ge_of_le {n : Nat} [NeZero n] {K : Fin n → ℝ} (hK : Monotone K)
    (τ : ℝ) {i : Fin n} (hi : insertPos K τ ≤ (i : Nat)) : τ ≤ K i := by
  by_contra hnot
  have hlt : K i < τ := lt_of_not_ge hnot
  have hii := (insertPos_lt_iff hK τ i).mp hlt
  omega

/-- Knots at positions `< insertPos` are `< τ`. -/
theorem insertPos_lt_of_lt {n : Nat} [NeZero n] {K : Fin n → ℝ} (hK : Monotone K)
    (τ : ℝ) {i : Fin n} (hi : (i : Nat) < insertPos K τ) : K i < τ :=
  (insertPos_lt_iff hK τ i).mpr hi

/-- Accessing the refined vector below the insertion position. -/
theorem knotAt_insertKnot_lt {n : Nat} [NeZero n] (K : Fin n → ℝ) (τ : ℝ) {j : Nat}
    (hj : j < insertPos K τ) :
    knotAt (insertKnot K τ) j = knotAt K j := by
  have hjn : j < n := lt_of_lt_of_le hj (insertPos_le K τ)
  unfold knotAt
  have hjn1 : j < n + 1 := by omega
  simp [hjn, hjn1, insertKnot, hj]

/-- The refined vector carries `τ` at the insertion position. -/
theorem knotAt_insertKnot_eq {n : Nat} [NeZero n] (K : Fin n → ℝ) (τ : ℝ) :
    knotAt (insertKnot K τ) (insertPos K τ) = τ := by
  have hp : insertPos K τ < n + 1 := Nat.lt_succ_of_le (insertPos_le K τ)
  unfold knotAt
  simp [hp, insertKnot]

/-- Accessing the refined vector above the insertion position. -/
theorem knotAt_insertKnot_gt {n : Nat} [NeZero n] (K : Fin n → ℝ) (τ : ℝ) {j : Nat}
    (hj : insertPos K τ < j) (hjle : j ≤ n) :
    knotAt (insertKnot K τ) j = knotAt K (j - 1) := by
  have hjn1 : j < n + 1 := by omega
  have hj1 : j - 1 < n := by omega
  unfold knotAt
  have hjlt : ¬ (j < insertPos K τ) := by omega
  have hjne : ¬ (j = insertPos K τ) := by omega
  simp [hjn1, hj1, insertKnot, hjlt, hjne]

/-- The refined vector agrees with `knotAt` on its own index type. -/
theorem insertKnot_eq_knotAt {n : Nat} [NeZero n] (K : Fin n → ℝ) (τ : ℝ)
    (i : Fin (n + 1)) :
    insertKnot K τ i = knotAt (insertKnot K τ) (i : Nat) := by
  unfold knotAt
  have hi : (i : Nat) < n + 1 := i.2
  simp [hi]

/-- Knots of the refined vector strictly below the insertion position stay below `τ`. -/
lemma knotAt_insertKnot_lt_tau {n : Nat} [NeZero n] {K : Fin n → ℝ} (hK : Monotone K)
    (τ : ℝ) {j : Nat} (hj : j < insertPos K τ) :
    knotAt (insertKnot K τ) j < τ := by
  rw [knotAt_insertKnot_lt K τ hj]
  have hjn : j < n := lt_of_lt_of_le hj (insertPos_le K τ)
  rw [knotAt_lt K j hjn]
  exact insertPos_lt_of_lt hK τ (i := ⟨j, hjn⟩) hj

/-- Knots of the refined vector at or above the insertion position are `≥ τ`. -/
lemma knotAt_insertKnot_ge_tau {n : Nat} [NeZero n] {K : Fin n → ℝ} (hK : Monotone K)
    (τ : ℝ) {j : Nat} (hj : insertPos K τ ≤ j) (hjle : j ≤ n) :
    τ ≤ knotAt (insertKnot K τ) j := by
  by_cases hje : j = insertPos K τ
  · rw [hje, knotAt_insertKnot_eq]
  · have hjgt : insertPos K τ < j := by omega
    rw [knotAt_insertKnot_gt K τ hjgt hjle]
    have hj1 : j - 1 < n := by omega
    rw [knotAt_lt K (j - 1) hj1]
    have : insertPos K τ ≤ j - 1 := by omega
    exact insertPos_ge_of_le hK τ (i := ⟨j - 1, hj1⟩) this

/-- The refined knot vector is monotone whenever the original is. -/
theorem insertKnot_mono {n : Nat} [NeZero n] {K : Fin n → ℝ} (hK : Monotone K) (τ : ℝ) :
    Monotone (insertKnot K τ) := by
  intro a b hab
  have habv : (a : Nat) ≤ (b : Nat) := Fin.le_iff_val_le_val.mp hab
  rw [insertKnot_eq_knotAt K τ a, insertKnot_eq_knotAt K τ b]
  have hav : (a : Nat) ≤ n := by omega
  have bv : (b : Nat) ≤ n := by omega
  by_cases hb : (b : Nat) < insertPos K τ
  · have ha : (a : Nat) < insertPos K τ := by omega
    rw [knotAt_insertKnot_lt K τ ha, knotAt_insertKnot_lt K τ hb]
    exact knotAt_mono hK (Fin.le_iff_val_le_val.mp hab)
  · have hbp : insertPos K τ ≤ (b : Nat) := le_of_not_gt hb
    by_cases ha : (a : Nat) < insertPos K τ
    · have hlt : knotAt (insertKnot K τ) (a : Nat) < τ := knotAt_insertKnot_lt_tau hK τ ha
      have hge : τ ≤ knotAt (insertKnot K τ) (b : Nat) := knotAt_insertKnot_ge_tau hK τ hbp bv
      exact le_trans hlt.le hge
    · have hap : insertPos K τ ≤ (a : Nat) := le_of_not_gt ha
      by_cases hae : (a : Nat) = insertPos K τ
      · rw [hae, knotAt_insertKnot_eq]
        exact knotAt_insertKnot_ge_tau hK τ hbp bv
      · have hagt : insertPos K τ < (a : Nat) := by omega
        rw [knotAt_insertKnot_gt K τ hagt hav]
        have hbgt : insertPos K τ < (b : Nat) := lt_of_lt_of_le hagt (Fin.le_iff_val_le_val.mp hab)
        rw [knotAt_insertKnot_gt K τ hbgt bv]
        have ham : (a : Nat) - 1 < n := by omega
        have hbm : (b : Nat) - 1 < n := by omega
        rw [knotAt_lt K ((a : Nat) - 1) ham, knotAt_lt K ((b : Nat) - 1) hbm]
        have hle : (⟨(a : Nat) - 1, ham⟩ : Fin n) ≤ ⟨(b : Nat) - 1, hbm⟩ := by
          apply Fin.le_iff_val_le_val.mpr
          simpa using (Nat.sub_le_sub_right habv 1)
        exact hK hle

/-- The left Boehm insertion coefficient `a_i^k`.  The identity region
is written as `i + k + 1 < p` (rather than `i ≤ p - k - 2`) so that the
saturating natural subtraction cannot swallow small insertion positions.  The
zero-denominator convention is built into Lean's division, since `x / 0 = 0`. -/
def aCoeff {n : Nat} [NeZero n] (K : Fin n → ℝ) (τ : ℝ) (i k : Nat) : ℝ :=
  let p := insertPos K τ
  if i + k + 1 < p then 1
  else if p ≤ i then 0
  else (τ - knotAt K i) / (knotAt (insertKnot K τ) (i + k + 1) - knotAt K i)

/-- The right Boehm insertion coefficient `b_i^k`. -/
def bCoeff {n : Nat} [NeZero n] (K : Fin n → ℝ) (τ : ℝ) (i k : Nat) : ℝ :=
  let p := insertPos K τ
  if i + k + 1 < p then 0
  else if p ≤ i then 1
  else (knotAt (insertKnot K τ) (i + k + 2) - τ) /
    (knotAt (insertKnot K τ) (i + k + 2) - knotAt (insertKnot K τ) (i + 1))

/-- The one-step refinement matrix: `Fin (n-k-1) → Fin (n-k)` upper bidiagonal. -/
def refineMatrix {n : Nat} [NeZero n] (K : Fin n → ℝ) (τ : ℝ) (k : Nat) :
    Matrix (Fin (n - k - 1)) (Fin (n - k)) ℝ :=
  fun i j ↦ if (j : Nat) = (i : Nat) then aCoeff K τ (i : Nat) k
    else if (j : Nat) = (i : Nat) + 1 then bCoeff K τ (i : Nat) k
    else 0

/-- Splitting a half-open interval at an inserted knot, with the degenerate
collapses on either side handled by the zero-divisor convention. -/
lemma indicator_insert_split (a b τ y : ℝ) (haτ : a < τ) (hτb : τ ≤ b) :
    (if a ≤ y ∧ y < b then (1 : ℝ) else 0) =
      1 * (if a ≤ y ∧ y < τ then 1 else 0)
      + (if b = τ then 0 else 1) * (if τ ≤ y ∧ y < b then 1 else 0) := by
  by_cases h2 : b = τ
  · simp [h2]
  · have hτb' : τ < b := lt_of_le_of_ne hτb (by intro h; exact h2 h.symm)
    simp [h2]
    exact (indicator_split haτ.le hτb'.le).symm

/-- Boehm identity, degree zero. -/
theorem boehm_zero {n : Nat} [NeZero n] {K : Fin n → ℝ} (hK : Monotone K)
    (τ : ℝ) (i : Nat) (x : ℝ) (hbound : i + 2 ≤ n) :
    splineOn K i 0 x = aCoeff K τ i 0 * splineOn (insertKnot K τ) i 0 x
      + bCoeff K τ i 0 * splineOn (insertKnot K τ) (i + 1) 0 x := by
  by_cases hle : i + 1 ≤ insertPos K τ
  · by_cases hsplit : i + 1 = insertPos K τ
    · -- split region: i + 1 = p
      have hin : i < n := by omega
      have hipn : i + 1 < n := by omega
      have hilt : i < insertPos K τ := by
        rw [← hsplit]
        exact Nat.lt_succ_self i
      have hKpre : knotAt K i < τ := by
        rw [knotAt_lt K i hin]
        exact insertPos_lt_of_lt hK τ (i := ⟨i, hin⟩) hilt
      have hKp : τ ≤ knotAt K (i + 1) := by
        rw [knotAt_lt K (i + 1) hipn]
        exact insertPos_ge_of_le hK τ (i := ⟨i + 1, hipn⟩) (le_of_eq hsplit.symm)
      have hKi1 : knotAt (insertKnot K τ) (i + 1) = τ := by
        rw [hsplit, knotAt_insertKnot_eq]
      have hKi2 : knotAt (insertKnot K τ) (i + 2) = knotAt K (i + 1) := by
        have hpg : insertPos K τ < i + 2 := by rw [← hsplit]; omega
        simpa using (knotAt_insertKnot_gt K τ hpg hbound)
      have ha : aCoeff K τ i 0 = 1 := by
        have h1 : ¬ i + 1 < insertPos K τ := by omega
        have h2 : ¬ insertPos K τ ≤ i := by omega
        simp [aCoeff, h1, h2]
        rw [hKi1]
        have hden : τ - knotAt K i ≠ 0 := sub_ne_zero.mpr (ne_of_gt hKpre)
        simp [hden]
      have hb : bCoeff K τ i 0 = if knotAt K (i + 1) = τ then 0 else 1 := by
        have h1 : ¬ i + 1 < insertPos K τ := by omega
        have h2 : ¬ insertPos K τ ≤ i := by omega
        simp [bCoeff, h1, h2]
        rw [hKi2, hKi1]
        by_cases heq : knotAt K (i + 1) = τ
        · simp [heq]
        · have hden : knotAt K (i + 1) - τ ≠ 0 := sub_ne_zero.mpr heq
          simp [heq, hden]
      rw [ha, hb]
      rw [splineOn_zero, splineOn_zero, splineOn_zero]
      have hKi : knotAt (insertKnot K τ) i = knotAt K i := by
        exact knotAt_insertKnot_lt K τ (by omega)
      rw [hKi, hKi1, hKi2]
      exact indicator_insert_split (knotAt K i) (knotAt K (i + 1)) τ x hKpre hKp
    · -- identity region: i + 1 < p
      have hlt : i + 1 < insertPos K τ := lt_of_le_of_ne hle hsplit
      have ha : aCoeff K τ i 0 = 1 := by simp [aCoeff, hlt]
      have hb : bCoeff K τ i 0 = 0 := by simp [bCoeff, hlt]
      rw [ha, hb, one_mul, zero_mul, add_zero]
      rw [splineOn_zero, splineOn_zero]
      have hip : i < insertPos K τ := by omega
      rw [knotAt_insertKnot_lt K τ hip, knotAt_insertKnot_lt K τ hlt]
  · -- shift region: p ≤ i
    have hge : insertPos K τ ≤ i := by omega
    have hnotle : ¬ i + 1 < insertPos K τ := by omega
    have ha : aCoeff K τ i 0 = 0 := by simp [aCoeff, hnotle, hge]
    have hb : bCoeff K τ i 0 = 1 := by simp [bCoeff, hnotle, hge]
    rw [ha, hb, zero_mul, one_mul, zero_add]
    rw [splineOn_zero, splineOn_zero]
    have hip : insertPos K τ < i + 1 := by omega
    have hile : i + 1 ≤ n := by omega
    have hip2 : insertPos K τ < i + 2 := by omega
    have hile2 : i + 2 ≤ n := hbound
    have h1 : knotAt (insertKnot K τ) (i + 1) = knotAt K i := by
      simpa using (knotAt_insertKnot_gt K τ hip hile)
    have h2 : knotAt (insertKnot K τ) (i + 2) = knotAt K (i + 1) := by
      simpa using (knotAt_insertKnot_gt K τ hip2 hile2)
    rw [h1, h2]

/-- `aCoeff` in the identity region. -/
lemma aCoeff_of_lt {n : Nat} [NeZero n] (K : Fin n → ℝ) (τ : ℝ) (i k : Nat)
    (h : i + k + 1 < insertPos K τ) : aCoeff K τ i k = 1 := by
  simp [aCoeff, h]

/-- `aCoeff` in the shift region. -/
lemma aCoeff_of_ge {n : Nat} [NeZero n] (K : Fin n → ℝ) (τ : ℝ) (i k : Nat)
    (h : insertPos K τ ≤ i) : aCoeff K τ i k = 0 := by
  have hnot : ¬ i + k + 1 < insertPos K τ := by omega
  simp [aCoeff, hnot, h]

/-- `bCoeff` in the identity region. -/
lemma bCoeff_of_lt {n : Nat} [NeZero n] (K : Fin n → ℝ) (τ : ℝ) (i k : Nat)
    (h : i + k + 1 < insertPos K τ) : bCoeff K τ i k = 0 := by
  simp [bCoeff, h]

/-- `bCoeff` in the shift region. -/
lemma bCoeff_of_ge {n : Nat} [NeZero n] (K : Fin n → ℝ) (τ : ℝ) (i k : Nat)
    (h : insertPos K τ ≤ i) : bCoeff K τ i k = 1 := by
  have hnot : ¬ i + k + 1 < insertPos K τ := by omega
  simp [bCoeff, hnot, h]

/-- `aCoeff` in the band region, expanded to its ratio. -/
lemma aCoeff_of_band {n : Nat} [NeZero n] (K : Fin n → ℝ) (τ : ℝ) (i k : Nat)
    (hnot : ¬ i + k + 1 < insertPos K τ) (hlt : i < insertPos K τ) :
    aCoeff K τ i k =
      (τ - knotAt K i) / (knotAt (insertKnot K τ) (i + k + 1) - knotAt K i) := by
  simp [aCoeff, hnot, not_le_of_gt hlt]

/-- `bCoeff` in the band region, expanded to its ratio. -/
lemma bCoeff_of_band {n : Nat} [NeZero n] (K : Fin n → ℝ) (τ : ℝ) (i k : Nat)
    (hnot : ¬ i + k + 1 < insertPos K τ) (hlt : i < insertPos K τ) :
    bCoeff K τ i k =
      (knotAt (insertKnot K τ) (i + k + 2) - τ) /
        (knotAt (insertKnot K τ) (i + k + 2) - knotAt (insertKnot K τ) (i + 1)) := by
  simp [bCoeff, hnot, not_le_of_gt hlt]

/-- Left weight is unchanged by insertion in the identity region. -/
lemma wLK_insertKnot_id {n : Nat} [NeZero n] (K : Fin n → ℝ) (τ : ℝ) {i k : Nat}
    (x : ℝ) (h : i + k + 1 < insertPos K τ) :
    wLK K i k x = wLK (insertKnot K τ) i k x := by
  unfold wLK
  have h1 : knotAt (insertKnot K τ) i = knotAt K i := knotAt_insertKnot_lt K τ (by omega)
  have h2 : knotAt (insertKnot K τ) (i + k + 1) = knotAt K (i + k + 1) := knotAt_insertKnot_lt K τ h
  simp [h1, h2]

/-- Right weight is unchanged by insertion in the identity region. -/
lemma wRK_insertKnot_id {n : Nat} [NeZero n] (K : Fin n → ℝ) (τ : ℝ) {i k : Nat}
    (x : ℝ) (h : i + k + 2 < insertPos K τ) :
    wRK K i k x = wRK (insertKnot K τ) i k x := by
  unfold wRK
  have h1 : knotAt (insertKnot K τ) (i + 1) = knotAt K (i + 1) := knotAt_insertKnot_lt K τ (by omega)
  have h2 : knotAt (insertKnot K τ) (i + k + 2) = knotAt K (i + k + 2) := knotAt_insertKnot_lt K τ h
  simp [h1, h2]

/-- Left weight shifts by insertion in the shift region. -/
lemma wLK_insertKnot_shift {n : Nat} [NeZero n] (K : Fin n → ℝ) (τ : ℝ) {i k : Nat}
    (x : ℝ) (h : insertPos K τ ≤ i) (hbound : i + k + 2 ≤ n) :
    wLK K i k x = wLK (insertKnot K τ) (i + 1) k x := by
  unfold wLK
  have h1 : knotAt (insertKnot K τ) (i + 1) = knotAt K i := by
    have hg : insertPos K τ < i + 1 := by omega
    have hgt := knotAt_insertKnot_gt K τ hg (by omega)
    simpa using hgt
  have h2 : knotAt (insertKnot K τ) (i + 1 + k + 1) = knotAt K (i + k + 1) := by
    have hg : insertPos K τ < i + 1 + k + 1 := by omega
    have hgt := knotAt_insertKnot_gt K τ hg (by omega)
    have hidx : (i + 1 + k + 1) - 1 = i + k + 1 := by omega
    rw [hidx] at hgt
    exact hgt
  simp [h1, h2]

/-- Right weight shifts by insertion in the shift region. -/
lemma wRK_insertKnot_shift {n : Nat} [NeZero n] (K : Fin n → ℝ) (τ : ℝ) {i k : Nat}
    (x : ℝ) (h : insertPos K τ ≤ i) (hbound : i + k + 3 ≤ n) :
    wRK K i k x = wRK (insertKnot K τ) (i + 1) k x := by
  unfold wRK
  have h1 : knotAt (insertKnot K τ) (i + 1 + 1) = knotAt K (i + 1) := by
    have hg : insertPos K τ < i + 1 + 1 := by omega
    have hgt := knotAt_insertKnot_gt K τ hg (by omega)
    simpa using hgt
  have h2 : knotAt (insertKnot K τ) (i + 1 + k + 2) = knotAt K (i + k + 2) := by
    have hg : insertPos K τ < i + 1 + k + 2 := by omega
    have hgt := knotAt_insertKnot_gt K τ hg (by omega)
    have hidx : (i + 1 + k + 2) - 1 = i + k + 2 := by omega
    rw [hidx] at hgt
    exact hgt
  simp [h1, h2]

/-- The left weight as a bare ratio (zero-denominator is zero). -/
lemma wLK_eq_ratio {n : Nat} [NeZero n] (K : Fin n → ℝ) (i k : Nat) (x : ℝ) :
    wLK K i k x = (x - knotAt K i) / (knotAt K (i + k + 1) - knotAt K i) := by
  unfold wLK
  by_cases h : knotAt K (i + k + 1) - knotAt K i = 0 <;> simp [h]

/-- The right weight as a bare ratio (zero-denominator is zero). -/
lemma wRK_eq_ratio {n : Nat} [NeZero n] (K : Fin n → ℝ) (i k : Nat) (x : ℝ) :
    wRK K i k x =
      (knotAt K (i + k + 2) - x) / (knotAt K (i + k + 2) - knotAt K (i + 1)) := by
  unfold wRK
  by_cases h : knotAt K (i + k + 2) - knotAt K (i + 1) = 0 <;> simp [h]

/-- The left-coefficient identity `E1`. -/
lemma boehm_E1 {n : Nat} [NeZero n] {K : Fin n → ℝ} (hK : Monotone K) (τ : ℝ)
    (i k : Nat) (x : ℝ) (hbound : i + k + 2 ≤ n) :
    wLK K i k x * aCoeff K τ i k =
      aCoeff K τ i (k + 1) * wLK (insertKnot K τ) i k x := by
  by_cases h_id : i + k + 2 < insertPos K τ
  · have ha : aCoeff K τ i k = 1 := aCoeff_of_lt K τ i k (by omega)
    have ha1 : aCoeff K τ i (k + 1) = 1 := aCoeff_of_lt K τ i (k + 1) h_id
    rw [ha, ha1, mul_one, one_mul]
    exact wLK_insertKnot_id K τ x (by omega)
  · by_cases h_sh : insertPos K τ ≤ i
    · have ha : aCoeff K τ i k = 0 := aCoeff_of_ge K τ i k h_sh
      have ha1 : aCoeff K τ i (k + 1) = 0 := aCoeff_of_ge K τ i (k + 1) h_sh
      rw [ha, ha1, mul_zero, zero_mul]
    · have hlt : i < insertPos K τ := by omega
      by_cases h_ak : i + k + 1 < insertPos K τ
      · have ha : aCoeff K τ i k = 1 := aCoeff_of_lt K τ i k h_ak
        have hidx : i + k + 2 = insertPos K τ := by omega
        have ha1 : aCoeff K τ i (k + 1) = 1 := by
          have hnot : ¬ i + k + 2 < insertPos K τ := by omega
          rw [aCoeff_of_band K τ i (k + 1) hnot hlt]
          rw [show i + (k + 1) + 1 = insertPos K τ by omega, knotAt_insertKnot_eq]
          have hin : i < n := by omega
          have hKi_lt : knotAt K i < τ := by
            rw [knotAt_lt K i hin]
            exact insertPos_lt_of_lt hK τ (i := ⟨i, hin⟩) hlt
          exact div_self (sub_ne_zero.mpr (ne_of_gt hKi_lt))
        rw [ha, ha1, mul_one, one_mul]
        exact wLK_insertKnot_id K τ x h_ak
      · have hnot1 : ¬ i + k + 1 < insertPos K τ := by omega
        have hnot2 : ¬ i + k + 2 < insertPos K τ := by omega
        rw [wLK_eq_ratio K i k x, wLK_eq_ratio (insertKnot K τ) i k x,
          aCoeff_of_band K τ i k hnot1 hlt, aCoeff_of_band K τ i (k + 1) hnot2 hlt]
        rw [knotAt_insertKnot_lt K τ hlt]
        rw [show i + (k + 1) + 1 = i + k + 2 by omega]
        have hg : insertPos K τ < i + k + 2 := by omega
        have hgt := knotAt_insertKnot_gt K τ hg (by omega)
        have hidx2 : (i + k + 2) - 1 = i + k + 1 := by omega
        rw [hidx2] at hgt
        rw [hgt]
        have hin : i < n := by omega
        have hKi_lt : knotAt K i < τ := by
          rw [knotAt_lt K i hin]
          exact insertPos_lt_of_lt hK τ (i := ⟨i, hin⟩) hlt
        have hik1n : i + k + 1 < n := by omega
        have htau_le_K : τ ≤ knotAt K (i + k + 1) := by
          rw [knotAt_lt K (i + k + 1) hik1n]
          exact insertPos_ge_of_le hK τ (i := ⟨i + k + 1, hik1n⟩) (le_of_not_gt hnot1)
        have hden1 : knotAt K (i + k + 1) - knotAt K i ≠ 0 :=
          ne_of_gt (sub_pos.mpr (lt_of_lt_of_le hKi_lt htau_le_K))
        have hden2 : knotAt (insertKnot K τ) (i + k + 1) - knotAt K i ≠ 0 :=
          ne_of_gt (sub_pos.mpr (lt_of_lt_of_le hKi_lt
            (knotAt_insertKnot_ge_tau hK τ (le_of_not_gt hnot1) (by omega))))
        field_simp [hden1, hden2]

/-- The right-coefficient identity `E3`. -/
lemma boehm_E3 {n : Nat} [NeZero n] {K : Fin n → ℝ} (hK : Monotone K) (τ : ℝ)
    (i k : Nat) (x : ℝ) (hbound : i + k + 3 ≤ n) :
    wRK K i k x * bCoeff K τ (i + 1) k =
      bCoeff K τ i (k + 1) * wRK (insertKnot K τ) (i + 1) k x := by
  by_cases h_id : i + k + 2 < insertPos K τ
  · have hb : bCoeff K τ (i + 1) k = 0 := bCoeff_of_lt K τ (i + 1) k (by omega)
    have hb1 : bCoeff K τ i (k + 1) = 0 := bCoeff_of_lt K τ i (k + 1) h_id
    rw [hb, hb1, mul_zero, zero_mul]
  · by_cases h_sh : insertPos K τ ≤ i
    · have hb : bCoeff K τ (i + 1) k = 1 := bCoeff_of_ge K τ (i + 1) k (by omega)
      have hb1 : bCoeff K τ i (k + 1) = 1 := bCoeff_of_ge K τ i (k + 1) h_sh
      rw [hb, hb1, mul_one, one_mul]
      exact wRK_insertKnot_shift K τ x h_sh hbound
    · have hlt : i < insertPos K τ := by omega
      by_cases h_ip : i + 1 < insertPos K τ
      · have hnot1 : ¬ i + k + 2 < insertPos K τ := by omega
        have hnot2 : ¬ i + 1 + k + 1 < insertPos K τ := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h_id
        rw [wRK_eq_ratio K i k x, wRK_eq_ratio (insertKnot K τ) (i + 1) k x,
          bCoeff_of_band K τ (i + 1) k hnot2 h_ip,
          bCoeff_of_band K τ i (k + 1) hnot1 hlt]
        rw [show i + (k + 1) + 2 = i + k + 3 by omega,
          show (i + 1) + k + 2 = i + k + 3 by omega]
        have hg : insertPos K τ < i + k + 3 := by omega
        have hgt := knotAt_insertKnot_gt K τ hg (by omega)
        have hidx : (i + k + 3) - 1 = i + k + 2 := by omega
        rw [hidx] at hgt
        rw [hgt]
        rw [knotAt_insertKnot_lt K τ h_ip]
        ring
      · have hip : i + 1 = insertPos K τ := by omega
        have hKi1p : knotAt (insertKnot K τ) (i + 1) = τ := by
          rw [hip, knotAt_insertKnot_eq]
        by_cases hz : knotAt K (i + k + 2) = τ
        · have hKi1 : knotAt K (i + 1) = τ := by
            have hle : knotAt K (i + 1) ≤ τ := by
              have hmono := knotAt_mono hK (show i + 1 ≤ i + k + 2 by omega)
              simpa [hz] using hmono
            have hge : τ ≤ knotAt K (i + 1) := by
              have hin : i + 1 < n := by omega
              rw [knotAt_lt K (i + 1) hin]
              exact insertPos_ge_of_le hK τ (i := ⟨i + 1, hin⟩) (le_of_eq hip.symm)
            exact le_antisymm hle hge
          have hw : wRK K i k x = 0 := by
            rw [wRK_eq_ratio]
            rw [hz, hKi1]
            simp
          have hb : bCoeff K τ (i + 1) k = 1 := bCoeff_of_ge K τ (i + 1) k (by omega)
          have hb1 : bCoeff K τ i (k + 1) = 0 := by
            rw [bCoeff_of_band K τ i (k + 1) (by omega) hlt]
            rw [show i + (k + 1) + 2 = i + k + 3 by omega]
            have hg : insertPos K τ < i + k + 3 := by rw [← hip]; omega
            have hgt := knotAt_insertKnot_gt K τ hg (by omega)
            have hidx : (i + k + 3) - 1 = i + k + 2 := by omega
            rw [hidx] at hgt
            rw [hgt, hKi1p, hz]
            simp
          rw [hw, hb, hb1, zero_mul, zero_mul]
        · have hden : knotAt K (i + k + 2) - τ ≠ 0 := sub_ne_zero.mpr hz
          have hb : bCoeff K τ (i + 1) k = 1 := bCoeff_of_ge K τ (i + 1) k (by omega)
          rw [hb, mul_one]
          rw [bCoeff_of_band K τ i (k + 1) (by omega) hlt]
          rw [show i + (k + 1) + 2 = i + k + 3 by omega]
          have hg : insertPos K τ < i + k + 3 := by rw [← hip]; omega
          have hgt := knotAt_insertKnot_gt K τ hg (by omega)
          have hidx : (i + k + 3) - 1 = i + k + 2 := by omega
          rw [hidx] at hgt
          rw [hgt, hKi1p]
          have hw : wRK K i k x = wRK (insertKnot K τ) (i + 1) k x := by
            unfold wRK
            have h1 : knotAt (insertKnot K τ) (i + 1 + k + 2) = knotAt K (i + k + 2) := by
              have hg1 : insertPos K τ < i + 1 + k + 2 := by rw [← hip]; omega
              have hgt1 := knotAt_insertKnot_gt K τ hg1 (by omega)
              have hidx1 : (i + 1 + k + 2) - 1 = i + k + 2 := by omega
              rw [hidx1] at hgt1
              exact hgt1
            have h2 : knotAt (insertKnot K τ) (i + 1 + 1) = knotAt K (i + 1) := by
              have hg2 : insertPos K τ < i + 1 + 1 := by rw [← hip]; omega
              have hgt2 := knotAt_insertKnot_gt K τ hg2 (by omega)
              have hidx2 : (i + 1 + 1) - 1 = i + 1 := by omega
              rw [hidx2] at hgt2
              exact hgt2
            simp [h1, h2]
          rw [hw]
          rw [div_self hden, one_mul]

/-- Field identity for Boehm `E2`, band A. -/
lemma boehm_E2_algA (b c τ x : ℝ) (hbc : b - c ≠ 0) (hτc : τ - c ≠ 0) :
    (b - x) / (b - c) = (τ - x) / (τ - c) + (b - τ) / (b - c) * ((x - c) / (τ - c)) := by
  field_simp [hbc, hτc]
  ring

/-- Field identity for Boehm `E2`, band B. -/
lemma boehm_E2_algB (A B C D τ x : ℝ) (hCA : C - A ≠ 0) (hCB : C - B ≠ 0) (hDB : D - B ≠ 0) :
    (x - A) / (C - A) * ((C - τ) / (C - B)) + (D - x) / (D - B) * ((τ - B) / (C - B)) =
      (τ - A) / (C - A) * ((C - x) / (C - B)) + (D - τ) / (D - B) * ((x - B) / (C - B)) := by
  field_simp [hCA, hCB, hDB]
  ring

/-- Field identity for Boehm `E2`, band C. -/
lemma boehm_E2_algC (A C τ x : ℝ) (hCA : C - A ≠ 0) (hCτ : C - τ ≠ 0) :
    (x - A) / (C - A) = (τ - A) / (C - A) * ((C - x) / (C - τ)) + (x - τ) / (C - τ) := by
  field_simp [hCA, hCτ]
  ring

/-- The cross-coefficient identity `E2`. -/
lemma boehm_E2 {n : Nat} [NeZero n] {K : Fin n → ℝ} (hK : Monotone K) (τ : ℝ)
    (i k : Nat) (x : ℝ) (hbound : i + k + 3 ≤ n) :
    wLK K i k x * bCoeff K τ i k + wRK K i k x * aCoeff K τ (i + 1) k =
      aCoeff K τ i (k + 1) * wRK (insertKnot K τ) i k x +
        bCoeff K τ i (k + 1) * wLK (insertKnot K τ) (i + 1) k x := by
  by_cases h_id : i + k + 2 < insertPos K τ
  · have hb : bCoeff K τ i k = 0 := bCoeff_of_lt K τ i k (by omega)
    have ha : aCoeff K τ (i + 1) k = 1 := aCoeff_of_lt K τ (i + 1) k (by omega)
    have ha1 : aCoeff K τ i (k + 1) = 1 := aCoeff_of_lt K τ i (k + 1) h_id
    have hb1 : bCoeff K τ i (k + 1) = 0 := bCoeff_of_lt K τ i (k + 1) h_id
    rw [hb, ha, ha1, hb1]
    ring
    exact wRK_insertKnot_id K τ x h_id
  · by_cases h_sh : insertPos K τ ≤ i
    · have hb : bCoeff K τ i k = 1 := bCoeff_of_ge K τ i k h_sh
      have ha : aCoeff K τ (i + 1) k = 0 := aCoeff_of_ge K τ (i + 1) k (by omega)
      have ha1 : aCoeff K τ i (k + 1) = 0 := aCoeff_of_ge K τ i (k + 1) h_sh
      have hb1 : bCoeff K τ i (k + 1) = 1 := bCoeff_of_ge K τ i (k + 1) h_sh
      rw [hb, ha, ha1, hb1, mul_one, mul_zero, zero_mul, one_mul, add_zero, zero_add]
      exact wLK_insertKnot_shift K τ x h_sh (le_trans (by omega : i + k + 2 ≤ i + k + 3) hbound)
    · have hlt : i < insertPos K τ := by omega
      by_cases hA : i + k + 1 < insertPos K τ
      · -- band A: i = p - k - 2
        have hidx : i + k + 2 = insertPos K τ := by omega
        have hb : bCoeff K τ i k = 0 := bCoeff_of_lt K τ i k hA
        have ha : aCoeff K τ (i + 1) k = 1 := by
          have hnot : ¬ (i + 1) + k + 1 < insertPos K τ := by omega
          have hlt1 : i + 1 < insertPos K τ := by omega
          rw [aCoeff_of_band K τ (i + 1) k hnot hlt1]
          rw [show (i + 1) + k + 1 = insertPos K τ by omega, knotAt_insertKnot_eq]
          have hin : i + 1 < n := by omega
          have hKi1_lt : knotAt K (i + 1) < τ := by
            rw [knotAt_lt K (i + 1) hin]
            exact insertPos_lt_of_lt hK τ (i := ⟨i + 1, hin⟩) (by omega)
          exact div_self (sub_ne_zero.mpr (ne_of_gt hKi1_lt))
        have ha1 : aCoeff K τ i (k + 1) = 1 := by
          have hnot : ¬ i + k + 2 < insertPos K τ := by omega
          rw [aCoeff_of_band K τ i (k + 1) hnot hlt]
          rw [show i + (k + 1) + 1 = insertPos K τ by omega, knotAt_insertKnot_eq]
          have hin : i < n := by omega
          have hKi_lt : knotAt K i < τ := by
            rw [knotAt_lt K i hin]
            exact insertPos_lt_of_lt hK τ (i := ⟨i, hin⟩) hlt
          exact div_self (sub_ne_zero.mpr (ne_of_gt hKi_lt))
        rw [hb, ha, ha1, mul_zero, mul_one, one_mul, zero_add]
        have hnot1 : ¬ i + k + 2 < insertPos K τ := by omega
        rw [bCoeff_of_band K τ i (k + 1) hnot1 hlt]
        rw [show i + (k + 1) + 2 = i + k + 3 by omega]
        have hg : insertPos K τ < i + k + 3 := by omega
        have hgt := knotAt_insertKnot_gt K τ hg (by omega)
        have hidx3 : (i + k + 3) - 1 = i + k + 2 := by omega
        rw [hidx3] at hgt
        rw [hgt]
        rw [wRK_eq_ratio K i k x, wRK_eq_ratio (insertKnot K τ) i k x, wLK_eq_ratio (insertKnot K τ) (i + 1) k x]
        rw [knotAt_insertKnot_lt K τ (by omega : i + 1 < insertPos K τ)]
        rw [show (i + 1) + k + 1 = i + k + 2 by omega]
        have hKp2 : knotAt (insertKnot K τ) (i + k + 2) = τ := by rw [hidx, knotAt_insertKnot_eq]
        rw [hKp2]
        have hin1 : i + 1 < n := by omega
        have hKi1_lt : knotAt K (i + 1) < τ := by
          rw [knotAt_lt K (i + 1) hin1]
          exact insertPos_lt_of_lt hK τ (i := ⟨i + 1, hin1⟩) (lt_of_le_of_lt (by omega : i + 1 ≤ i + k + 1) hA)
        have hin2 : i + k + 2 < n := by omega
        have htau_le2 : τ ≤ knotAt K (i + k + 2) := by
          rw [knotAt_lt K (i + k + 2) hin2]
          exact insertPos_ge_of_le hK τ (i := ⟨i + k + 2, hin2⟩) (le_of_eq hidx.symm)
        have d1 : knotAt K (i + k + 2) - knotAt K (i + 1) ≠ 0 :=
          ne_of_gt (sub_pos.mpr (lt_of_lt_of_le hKi1_lt htau_le2))
        have d2 : τ - knotAt K (i + 1) ≠ 0 := sub_ne_zero.mpr (ne_of_gt hKi1_lt)
        exact boehm_E2_algA (knotAt K (i + k + 2)) (knotAt K (i + 1)) τ x d1 d2
      · by_cases hC : insertPos K τ ≤ i + 1
        · -- band C: i = p - 1
          have hip : i + 1 = insertPos K τ := by omega
          have hnotA : ¬ i + k + 1 < insertPos K τ := by omega
          have hnot1 : ¬ i + k + 2 < insertPos K τ := by omega
          have ha : aCoeff K τ (i + 1) k = 0 := aCoeff_of_ge K τ (i + 1) k (by omega)
          have hKi1p : knotAt (insertKnot K τ) (i + 1) = τ := by rw [hip, knotAt_insertKnot_eq]
          by_cases hz : knotAt K (i + k + 1) = τ
          · -- degenerate
            have hKi1 : knotAt K (i + 1) = τ := by
              have hle : knotAt K (i + 1) ≤ τ := by
                have hmono := knotAt_mono hK (show i + 1 ≤ i + k + 1 by omega)
                simpa [hz] using hmono
              have hge : τ ≤ knotAt K (i + 1) := by
                have hin : i + 1 < n := by omega
                rw [knotAt_lt K (i + 1) hin]
                exact insertPos_ge_of_le hK τ (i := ⟨i + 1, hin⟩) (le_of_eq hip.symm)
              exact le_antisymm hle hge
            have hb : bCoeff K τ i k = 0 := by
              rw [bCoeff_of_band K τ i k hnotA hlt]
              have hg : insertPos K τ < i + k + 2 := by omega
              have hgt := knotAt_insertKnot_gt K τ hg (by omega)
              have hidx : (i + k + 2) - 1 = i + k + 1 := by omega
              rw [hidx] at hgt
              rw [hgt, hKi1p, hz]
              simp
            have ha1 : aCoeff K τ i (k + 1) = 1 := by
              rw [aCoeff_of_band K τ i (k + 1) hnot1 hlt]
              rw [show i + (k + 1) + 1 = i + k + 2 by omega]
              have hg : insertPos K τ < i + k + 2 := by omega
              have hgt := knotAt_insertKnot_gt K τ hg (by omega)
              have hidx : (i + k + 2) - 1 = i + k + 1 := by omega
              rw [hidx] at hgt
              rw [hgt, hz]
              have hin : i < n := by omega
              have hKi_lt : knotAt K i < τ := by
                rw [knotAt_lt K i hin]
                exact insertPos_lt_of_lt hK τ (i := ⟨i, hin⟩) hlt
              exact div_self (sub_ne_zero.mpr (ne_of_gt hKi_lt))
            have hwRK' : wRK (insertKnot K τ) i k x = 0 := by
              rw [wRK_eq_ratio]
              have hg : insertPos K τ < i + k + 2 := by omega
              have hgt := knotAt_insertKnot_gt K τ hg (by omega)
              have hidx : (i + k + 2) - 1 = i + k + 1 := by omega
              rw [hidx] at hgt
              rw [hgt, hKi1p, hz]
              simp
            have hwLK' : wLK (insertKnot K τ) (i + 1) k x = 0 := by
              rw [wLK_eq_ratio]
              rw [hKi1p]
              rw [show (i + 1) + k + 1 = i + k + 2 by omega]
              have hg : insertPos K τ < i + k + 2 := by omega
              have hgt := knotAt_insertKnot_gt K τ hg (by omega)
              have hidx : (i + k + 2) - 1 = i + k + 1 := by omega
              rw [hidx] at hgt
              rw [hgt, hz]
              simp
            rw [ha, hb, ha1, hwRK', hwLK']
            ring
          · -- nondegenerate
            rw [ha, mul_zero, add_zero]
            rw [wLK_eq_ratio K i k x, bCoeff_of_band K τ i k hnotA hlt,
              aCoeff_of_band K τ i (k + 1) hnot1 hlt, bCoeff_of_band K τ i (k + 1) hnot1 hlt,
              wRK_eq_ratio (insertKnot K τ) i k x, wLK_eq_ratio (insertKnot K τ) (i + 1) k x]
            rw [show i + (k + 1) + 1 = i + k + 2 by omega,
              show i + (k + 1) + 2 = i + k + 3 by omega,
              show (i + 1) + k + 1 = i + k + 2 by omega]
            rw [hKi1p]
            have hg2 : insertPos K τ < i + k + 2 := by omega
            have hgt2 := knotAt_insertKnot_gt K τ hg2 (by omega)
            have hidx2 : (i + k + 2) - 1 = i + k + 1 := by omega
            rw [hidx2] at hgt2
            have hg3 : insertPos K τ < i + k + 3 := by omega
            have hgt3 := knotAt_insertKnot_gt K τ hg3 (by omega)
            have hidx3 : (i + k + 3) - 1 = i + k + 2 := by omega
            rw [hidx3] at hgt3
            rw [hgt2, hgt3]
            have hin : i < n := by omega
            have hKi_lt : knotAt K i < τ := by
              rw [knotAt_lt K i hin]
              exact insertPos_lt_of_lt hK τ (i := ⟨i, hin⟩) hlt
            have hik1n : i + k + 1 < n := by omega
            have htau_le1 : τ ≤ knotAt K (i + k + 1) := by
              rw [knotAt_lt K (i + k + 1) hik1n]
              exact insertPos_ge_of_le hK τ (i := ⟨i + k + 1, hik1n⟩) (le_of_not_gt hnotA)
            have htau_lt1 : τ < knotAt K (i + k + 1) :=
              lt_of_le_of_ne htau_le1 (by intro h; exact hz h.symm)
            have htau_lt2 : τ < knotAt K (i + k + 2) :=
              lt_of_lt_of_le htau_lt1 (knotAt_mono hK (show i + k + 1 ≤ i + k + 2 by omega))
            have d1 : knotAt K (i + k + 1) - knotAt K i ≠ 0 :=
              ne_of_gt (sub_pos.mpr (lt_of_lt_of_le hKi_lt htau_le1))
            have d2 : knotAt K (i + k + 1) - τ ≠ 0 := sub_ne_zero.mpr (ne_of_gt htau_lt1)
            rw [div_self (sub_ne_zero.mpr (ne_of_gt htau_lt1)), div_self (sub_ne_zero.mpr (ne_of_gt htau_lt2)), mul_one, one_mul]
            exact boehm_E2_algC (knotAt K i) (knotAt K (i + k + 1)) τ x d1 d2
        · -- band B: p ≤ i + k + 1, i + 1 < p
          have h_ip : i + 1 < insertPos K τ := by omega
          have hnotA : ¬ i + k + 1 < insertPos K τ := by omega
          have hnot1 : ¬ i + k + 2 < insertPos K τ := by omega
          have hnotip : ¬ (i + 1) + k + 1 < insertPos K τ := by omega
          rw [wLK_eq_ratio K i k x, wRK_eq_ratio K i k x,
            bCoeff_of_band K τ i k hnotA hlt, aCoeff_of_band K τ (i + 1) k hnotip h_ip,
            aCoeff_of_band K τ i (k + 1) hnot1 hlt, bCoeff_of_band K τ i (k + 1) hnot1 hlt,
            wRK_eq_ratio (insertKnot K τ) i k x, wLK_eq_ratio (insertKnot K τ) (i + 1) k x]
          rw [show i + (k + 1) + 1 = i + k + 2 by omega,
            show i + (k + 1) + 2 = i + k + 3 by omega,
            show (i + 1) + k + 1 = i + k + 2 by omega]
          rw [knotAt_insertKnot_lt K τ h_ip]
          have hg2 : insertPos K τ < i + k + 2 := by omega
          have hgt2 := knotAt_insertKnot_gt K τ hg2 (by omega)
          have hidx2 : (i + k + 2) - 1 = i + k + 1 := by omega
          rw [hidx2] at hgt2
          have hg3 : insertPos K τ < i + k + 3 := by omega
          have hgt3 := knotAt_insertKnot_gt K τ hg3 (by omega)
          have hidx3 : (i + k + 3) - 1 = i + k + 2 := by omega
          rw [hidx3] at hgt3
          rw [hgt2, hgt3]
          have hin : i < n := by omega
          have hKi_lt : knotAt K i < τ := by
            rw [knotAt_lt K i hin]
            exact insertPos_lt_of_lt hK τ (i := ⟨i, hin⟩) hlt
          have hin1 : i + 1 < n := by omega
          have hKi1_lt : knotAt K (i + 1) < τ := by
            rw [knotAt_lt K (i + 1) hin1]
            exact insertPos_lt_of_lt hK τ (i := ⟨i + 1, hin1⟩) h_ip
          have hik1n : i + k + 1 < n := by omega
          have htau_le1 : τ ≤ knotAt K (i + k + 1) := by
            rw [knotAt_lt K (i + k + 1) hik1n]
            exact insertPos_ge_of_le hK τ (i := ⟨i + k + 1, hik1n⟩) (le_of_not_gt hnotA)
          have hik2n : i + k + 2 < n := by omega
          have htau_le2 : τ ≤ knotAt K (i + k + 2) := by
            rw [knotAt_lt K (i + k + 2) hik2n]
            exact insertPos_ge_of_le hK τ (i := ⟨i + k + 2, hik2n⟩) (le_of_not_gt hnot1)
          have d1 : knotAt K (i + k + 1) - knotAt K i ≠ 0 :=
            ne_of_gt (sub_pos.mpr (lt_of_lt_of_le hKi_lt htau_le1))
          have d2 : knotAt K (i + k + 1) - knotAt K (i + 1) ≠ 0 :=
            ne_of_gt (sub_pos.mpr (lt_of_lt_of_le hKi1_lt htau_le1))
          have d3 : knotAt K (i + k + 2) - knotAt K (i + 1) ≠ 0 :=
            ne_of_gt (sub_pos.mpr (lt_of_lt_of_le hKi1_lt htau_le2))
          exact boehm_E2_algB (knotAt K i) (knotAt K (i + 1)) (knotAt K (i + k + 1))
            (knotAt K (i + k + 2)) τ x d1 d2 d3

/-- Boehm's knot-insertion identity: every degree-`k` spline on `K` is a
convex combination of two degree-`k` splines on `insertKnot K τ`. -/
theorem boehmIdentity {n : Nat} [NeZero n] {K : Fin n → ℝ} (hK : Monotone K) (τ : ℝ)
    (i k : Nat) (x : ℝ) (hbound : i + k + 2 ≤ n) :
    splineOn K i k x = aCoeff K τ i k * splineOn (insertKnot K τ) i k x
      + bCoeff K τ i k * splineOn (insertKnot K τ) (i + 1) k x := by
  induction k generalizing i x with
  | zero => exact boehm_zero hK τ i x hbound
  | succ k ih =>
      rw [splineOn_succ]
      have hi_bound : i + k + 2 ≤ n := by omega
      have hi1_bound : i + 1 + k + 2 ≤ n := by omega
      rw [ih i x hi_bound, ih (i + 1) x hi1_bound]
      rw [splineOn_succ, splineOn_succ]
      have hE1 := boehm_E1 hK τ i k x (by omega)
      have hE2 := boehm_E2 hK τ i k x hbound
      have hE3 := boehm_E3 hK τ i k x hbound
      rw [mul_add, mul_add, mul_add, mul_add]
      simp only [← mul_assoc]
      have hE1' := congrArg (fun z => z * splineOn (insertKnot K τ) i k x) hE1
      have hE3' := congrArg (fun z => z * splineOn (insertKnot K τ) (i + 1 + 1) k x) hE3
      have hN1 : (wLK K i k x * bCoeff K τ i k) * splineOn (insertKnot K τ) (i + 1) k x
          + (wRK K i k x * aCoeff K τ (i + 1) k) * splineOn (insertKnot K τ) (i + 1) k x
          = (aCoeff K τ i (k + 1) * wRK (insertKnot K τ) i k x) * splineOn (insertKnot K τ) (i + 1) k x
          + (bCoeff K τ i (k + 1) * wLK (insertKnot K τ) (i + 1) k x) * splineOn (insertKnot K τ) (i + 1) k x := by
            rw [← add_mul, ← add_mul]
            exact congrArg (fun z => z * splineOn (insertKnot K τ) (i + 1) k x) hE2
      nlinarith [hE1', hN1, hE3']

/-- The left coefficient is nonnegative in the refinement range. -/
lemma aCoeff_nonneg {n : Nat} [NeZero n] {K : Fin n → ℝ} (hK : Monotone K) (τ : ℝ)
    (i k : Nat) (hbound : i + k + 2 ≤ n) : 0 ≤ aCoeff K τ i k := by
  by_cases h1 : i + k + 1 < insertPos K τ
  · simp [aCoeff, h1]
  · by_cases h2 : insertPos K τ ≤ i
    · simp [aCoeff, h1, h2]
    · have hlt : i < insertPos K τ := by omega
      simp [aCoeff, h1, h2]
      have hin : i < n := by omega
      have hKi_lt : knotAt K i < τ := by
        rw [knotAt_lt K i hin]
        exact insertPos_lt_of_lt hK τ (i := ⟨i, hin⟩) hlt
      have hge : τ ≤ knotAt (insertKnot K τ) (i + k + 1) :=
        knotAt_insertKnot_ge_tau hK τ (le_of_not_gt h1) (by omega)
      exact div_nonneg (sub_nonneg.mpr hKi_lt.le) (sub_nonneg.mpr (le_trans hKi_lt.le hge))

/-- The right coefficient is nonnegative in the refinement range. -/
lemma bCoeff_nonneg {n : Nat} [NeZero n] {K : Fin n → ℝ} (hK : Monotone K) (τ : ℝ)
    (i k : Nat) (hbound : i + k + 2 ≤ n) : 0 ≤ bCoeff K τ i k := by
  by_cases h1 : i + k + 1 < insertPos K τ
  · simp [bCoeff, h1]
  · by_cases h2 : insertPos K τ ≤ i
    · simp [bCoeff, h1, h2]
    · have hlt : i < insertPos K τ := by omega
      simp [bCoeff, h1, h2]
      have hmono' : Monotone (knotAt (insertKnot K τ)) := knotAt_mono (insertKnot_mono hK τ)
      have hnum : 0 ≤ knotAt (insertKnot K τ) (i + k + 2) - τ :=
        sub_nonneg.mpr (knotAt_insertKnot_ge_tau hK τ (by omega) (by omega))
      have hden : 0 ≤ knotAt (insertKnot K τ) (i + k + 2) - knotAt (insertKnot K τ) (i + 1) :=
        sub_nonneg.mpr (hmono' (by omega : i + 1 ≤ i + k + 2))
      exact div_nonneg hnum hden

/-- A strictly increasing self-map of `Fin k` lies below the identity. -/
private lemma strictMono_self_le_id {k : Nat} {f : Fin k → Fin k} (hmono : StrictMono f) :
    ∀ t : Fin k, (t : Nat) ≤ (f t : Nat) := by
  intro t
  let S := Finset.univ.filter (fun s : Fin k => (s : Nat) < (t : Nat))
  have hcardS : S.card = (t : Nat) := card_fin_below k (t : Nat) (le_of_lt t.2)
  have himg : (S.image f).card = (t : Nat) := by
    rw [Finset.card_image_of_injective S hmono.injective, hcardS]
  have himgsub : S.image f ⊆ Finset.univ.filter (fun v : Fin k => (v : Nat) < (f t : Nat)) := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨s, hsS, hsv⟩
    rw [Finset.mem_filter]
    constructor
    · exact Finset.mem_univ _
    · rw [← hsv]
      have hslt : (s : Nat) < (t : Nat) := (Finset.mem_filter.mp hsS).2
      exact Fin.lt_iff_val_lt_val.mp (hmono (Fin.lt_iff_val_lt_val.mpr hslt))
  have hle : (t : Nat) ≤ (Finset.univ.filter (fun v : Fin k => (v : Nat) < (f t : Nat))).card := by
    rw [← himg]
    exact Finset.card_le_card himgsub
  have hcard2 : (Finset.univ.filter (fun v : Fin k => (v : Nat) < (f t : Nat))).card = (f t : Nat) :=
    card_fin_below k (f t : Nat) (le_of_lt (f t).2)
  rw [hcard2] at hle
  exact hle

/-- Consecutive strict monotonicity on `Fin k` yields strict monotonicity. -/
lemma strictMono_fin_of_succ {k : Nat} {f : Fin k → Fin k}
    (h : ∀ a b : Fin k, (b : Nat) = (a : Nat) + 1 → f a < f b) : StrictMono f := by
  intro a b hab
  have habv : (a : Nat) < (b : Nat) := Fin.lt_iff_val_lt_val.mp hab
  have hchain : ∀ n : Nat, (hn : n < k) → (a : Nat) < n → n ≤ (b : Nat) →
      (f a : Nat) < (f ⟨n, hn⟩ : Nat) := by
    have hbase : ∀ (hn : (a : Nat) + 1 < k), (a : Nat) < (a : Nat) + 1 → (a : Nat) + 1 ≤ (b : Nat) →
        (f a : Nat) < (f ⟨(a : Nat) + 1, hn⟩ : Nat) := by
      intro hn _ _
      have hstep := h a ⟨(a : Nat) + 1, hn⟩ (by rfl)
      exact Fin.lt_iff_val_lt_val.mp hstep
    have hstep' : ∀ n : Nat, (a : Nat) + 1 ≤ n →
        (∀ (hn : n < k), (a : Nat) < n → n ≤ (b : Nat) → (f a : Nat) < (f ⟨n, hn⟩ : Nat)) →
        (∀ (hn : n + 1 < k), (a : Nat) < n + 1 → n + 1 ≤ (b : Nat) → (f a : Nat) < (f ⟨n + 1, hn⟩ : Nat)) := by
      intro n hle ih hn ha_n1 hn1_le
      have hn_lt : n < k := by omega
      have hprev := ih hn_lt (by omega) (by omega)
      have hnext := h ⟨n, hn_lt⟩ ⟨n + 1, hn⟩ (by rfl)
      have hnext' : (f ⟨n, hn_lt⟩ : Nat) < (f ⟨n + 1, hn⟩ : Nat) := Fin.lt_iff_val_lt_val.mp hnext
      have hprev' : (f a : Nat) < (f ⟨n, hn_lt⟩ : Nat) := by simpa using hprev
      exact lt_trans hprev' hnext'
    intro n hn ha_n hn_le
    exact Nat.le_induction hbase hstep' n (by omega) hn ha_n hn_le
  have hres := hchain (b : Nat) b.isLt habv (by rfl)
  simpa using hres

/-- A strictly increasing permutation of `Fin k` is the identity. -/
lemma perm_strictMono_eq_one {k : Nat} (σ : Equiv.Perm (Fin k)) :
    StrictMono (σ : Fin k → Fin k) → σ = 1 := by
  intro hmono
  have hinvmono : StrictMono ((σ.symm : Equiv.Perm (Fin k)) : Fin k → Fin k) := by
    intro a b hab
    by_contra hnot
    have hle : σ.symm b ≤ σ.symm a := le_of_not_gt hnot
    have hb_le_a : b ≤ a := by
      simpa using hmono.monotone hle
    exact (not_le_of_gt hab) hb_le_a
  have hge := strictMono_self_le_id hmono
  have hge_inv := strictMono_self_le_id hinvmono
  ext t
  apply le_antisymm
  · simpa using hge_inv (σ t)
  · exact hge t
/-- An upper bidiagonal matrix with nonnegative entries is totally nonnegative. -/
theorem bidiagonal_isTotallyNonnegative {r c : Nat} (A : Matrix (Fin r) (Fin c) ℝ)
    (hbidiag : ∀ i j, A i j ≠ 0 → (j : Nat) = (i : Nat) ∨ (j : Nat) = (i : Nat) + 1)
    (hnonneg : ∀ i j, 0 ≤ A i j) : IsTotallyNonnegative A := by
  intro k rows cols
  unfold matrixMinor
  rw [Matrix.det_apply']
  have hsum : (∑ σ : Equiv.Perm (Fin k),
      Equiv.Perm.sign σ * ∏ t : Fin k, (A.submatrix rows cols) (σ t) t) =
      ∏ t : Fin k, (A.submatrix rows cols) t t := by
    rw [Finset.sum_eq_single 1]
    · simp
    · intro σ hσ hσ1
      have hprod : ∏ t : Fin k, (A.submatrix rows cols) (σ t) t = 0 := by
        by_contra hnot
        have hne : ∀ t : Fin k, (A.submatrix rows cols) (σ t) t ≠ 0 := by
          intro t
          exact (Finset.prod_ne_zero_iff.mp hnot) t (Finset.mem_univ t)
        have hmono : StrictMono (σ : Fin k → Fin k) := by
          apply strictMono_fin_of_succ
          intro a b hb1
          have hca : A (rows (σ a)) (cols a) ≠ 0 := by
            simpa [Matrix.submatrix_apply] using hne a
          have hcb : A (rows (σ b)) (cols b) ≠ 0 := by
            simpa [Matrix.submatrix_apply] using hne b
          have hb1d := hbidiag (rows (σ a)) (cols a) hca
          have hb2d := hbidiag (rows (σ b)) (cols b) hcb
          have hle1 : (rows (σ a) : Nat) ≤ (cols a : Nat) := by
            rcases hb1d with h | h <;> omega
          have hle2 : (cols b : Nat) ≤ (rows (σ b) : Nat) + 1 := by
            rcases hb2d with h | h <;> omega
          have hcols_lt : cols a < cols b := cols.strictMono (Fin.lt_iff_val_lt_val.mpr (by omega))
          have hle_rows : (rows (σ a) : Nat) ≤ (rows (σ b) : Nat) := by omega
          have hne_rows : rows (σ a) ≠ rows (σ b) := by
            intro h
            have h1 := rows.injective h
            have h2 := σ.injective h1
            have hne_ab : a ≠ b := by
              intro hab
              have := congrArg Fin.val hab
              omega
            exact hne_ab h2
          have hlt_rows : rows (σ a) < rows (σ b) := lt_of_le_of_ne hle_rows hne_rows
          exact (rows.lt_iff_lt).mp hlt_rows
        have hσ_eq := perm_strictMono_eq_one σ hmono
        exact hσ1 hσ_eq
      rw [hprod, mul_zero]
    · intro h
      exact False.elim (h (Finset.mem_univ 1))
  rw [hsum]
  simp only [Matrix.submatrix_apply]
  exact Finset.prod_nonneg (fun t _ => hnonneg (rows t) (cols t))

/-- The one-step refinement matrix is totally nonnegative. -/
theorem refineMatrix_isTotallyNonnegative {n : Nat} [NeZero n] {K : Fin n → ℝ}
    (hK : Monotone K) (τ : ℝ) (k : Nat) :
    IsTotallyNonnegative (refineMatrix K τ k) := by
  apply bidiagonal_isTotallyNonnegative
  · intro i j hne
    unfold refineMatrix at hne
    by_cases h1 : (j : Nat) = (i : Nat)
    · exact Or.inl h1
    · by_cases h2 : (j : Nat) = (i : Nat) + 1
      · exact Or.inr h2
      · simp [h1, h2] at hne
  · intro i j
    unfold refineMatrix
    by_cases h1 : (j : Nat) = (i : Nat)
    · simp [h1]
      exact aCoeff_nonneg hK τ (i : Nat) k (by
        have hi := i.isLt
        omega)
    · by_cases h2 : (j : Nat) = (i : Nat) + 1
      · simp [h1, h2]
        exact bCoeff_nonneg hK τ (i : Nat) k (by
          have hi := i.isLt
          omega)
      · simp [h1, h2]

end

end ColomboGeneralK2.Odd
