import ColomboGeneralK2.OddMVP1Signatures

/-!
# The degree-zero paired boundary

This file proves the exceptional critical case `m = 2`, where the strict
degree-zero truncated powers are step functions.  The proof keeps the strict
inequality convention throughout, so sampled points on knots and coincidences
between the two knot families are included.
-/

namespace ColomboGeneralK2.Odd

noncomputable section

/-- The integral step matrix underlying the degree-zero `4 × 4` split matrix. -/
private def degreeZeroStepMatrix (a b c d : Fin 4 → Bool) :
    Matrix (Fin 4) (Fin 4) ℤ :=
  fun i j ↦
    match (groupedColumnEquiv 2).symm j with
    | Sum.inl q => if q = 0 then (if a i then 1 else 0) else (if b i then 1 else 0)
    | Sum.inr q => if q = 0 then (if c i then 1 else 0) else (if d i then 1 else 0)

/-- The finite order constraints forced by two increasing, strictly paired
knot lists and an increasing sample list. -/
private def DegreeZeroAdmissible (a b c d : Fin 4 → Bool) : Prop :=
  (∀ i j, i < j → a j = true → a i = true) ∧
  (∀ i j, i < j → b j = true → b i = true) ∧
  (∀ i j, i < j → c i = true → c j = true) ∧
  (∀ i j, i < j → d i = true → d j = true) ∧
  (∀ i, a i = true → b i = true) ∧
  (∀ i, d i = true → c i = true) ∧
  (∀ i, a i = true → c i = false) ∧
  (∀ i, b i = true → d i = false)

/-- An initial segment of four rows, encoded by its length `k ∈ {0,…,4}`. -/
private def initialStep (k : Fin 5) (i : Fin 4) : Bool :=
  decide ((i : Nat) < (k : Nat))

/-- A terminal segment of four rows, encoded by its first occupied row. -/
private def terminalStep (k : Fin 5) (i : Fin 4) : Bool :=
  decide ((k : Nat) ≤ (i : Nat))

/-- Every decreasing Boolean step column on four ordered rows is an initial
segment. -/
private theorem exists_initialStep (a : Fin 4 → Bool)
    (ha : ∀ i j, i < j → a j = true → a i = true) :
    ∃ k : Fin 5, a = initialStep k := by
  by_cases h3 : a 3 = true
  · have h0 : a 0 = true := ha 0 3 (by decide) h3
    have h1 : a 1 = true := ha 1 3 (by decide) h3
    have h2 : a 2 = true := ha 2 3 (by decide) h3
    refine ⟨4, ?_⟩
    funext i
    fin_cases i <;> simp [initialStep, h0, h1, h2, h3]
  · have h3f : a 3 = false := Bool.eq_false_iff.mpr h3
    by_cases h2 : a 2 = true
    · have h0 : a 0 = true := ha 0 2 (by decide) h2
      have h1 : a 1 = true := ha 1 2 (by decide) h2
      refine ⟨3, ?_⟩
      funext i
      fin_cases i <;> simp [initialStep, h0, h1, h2, h3f]
    · have h2f : a 2 = false := Bool.eq_false_iff.mpr h2
      by_cases h1 : a 1 = true
      · have h0 : a 0 = true := ha 0 1 (by decide) h1
        refine ⟨2, ?_⟩
        funext i
        fin_cases i <;> simp [initialStep, h0, h1, h2f, h3f]
      · have h1f : a 1 = false := Bool.eq_false_iff.mpr h1
        by_cases h0 : a 0 = true
        · refine ⟨1, ?_⟩
          funext i
          fin_cases i <;> simp [initialStep, h0, h1f, h2f, h3f]
        · have h0f : a 0 = false := Bool.eq_false_iff.mpr h0
          refine ⟨0, ?_⟩
          funext i
          fin_cases i <;> simp [initialStep, h0f, h1f, h2f, h3f]

/-- Every increasing Boolean step column on four ordered rows is a terminal
segment. -/
private theorem exists_terminalStep (a : Fin 4 → Bool)
    (ha : ∀ i j, i < j → a i = true → a j = true) :
    ∃ k : Fin 5, a = terminalStep k := by
  by_cases h0 : a 0 = true
  · have h1 : a 1 = true := ha 0 1 (by decide) h0
    have h2 : a 2 = true := ha 0 2 (by decide) h0
    have h3 : a 3 = true := ha 0 3 (by decide) h0
    refine ⟨0, ?_⟩
    funext i
    fin_cases i <;> simp [terminalStep, h0, h1, h2, h3]
  · have h0f : a 0 = false := Bool.eq_false_iff.mpr h0
    by_cases h1 : a 1 = true
    · have h2 : a 2 = true := ha 1 2 (by decide) h1
      have h3 : a 3 = true := ha 1 3 (by decide) h1
      refine ⟨1, ?_⟩
      funext i
      fin_cases i <;> simp [terminalStep, h0f, h1, h2, h3]
    · have h1f : a 1 = false := Bool.eq_false_iff.mpr h1
      by_cases h2 : a 2 = true
      · have h3 : a 3 = true := ha 2 3 (by decide) h2
        refine ⟨2, ?_⟩
        funext i
        fin_cases i <;> simp [terminalStep, h0f, h1f, h2, h3]
      · have h2f : a 2 = false := Bool.eq_false_iff.mpr h2
        by_cases h3 : a 3 = true
        · refine ⟨3, ?_⟩
          funext i
          fin_cases i <;> simp [terminalStep, h0f, h1f, h2f, h3]
        · have h3f : a 3 = false := Bool.eq_false_iff.mpr h3
          refine ⟨4, ?_⟩
          funext i
          fin_cases i <;> simp [terminalStep, h0f, h1f, h2f, h3f]

/-- Finite core of the boundary argument.  There are only five possible cuts
for each column; incompatible cuts short-circuit before the determinant is
evaluated. -/
private theorem degreeZeroCutMatrix_det_nonneg :
    ∀ A B C D : Fin 5,
      DegreeZeroAdmissible (initialStep A) (initialStep B)
          (terminalStep C) (terminalStep D) →
        0 ≤ (degreeZeroStepMatrix (initialStep A) (initialStep B)
          (terminalStep C) (terminalStep D)).det := by
  unfold DegreeZeroAdmissible
  decide

/-- The critical paired split determinant is nonnegative in the exceptional
degree-zero case `m = 2`. -/
theorem criticalSplitDet_two_zero_nonneg {x : Fin (2 * 2) → ℝ}
    (hx : StrictMono x) {s u : Fin 2 → ℝ}
    (hs : StrictMono s) (hu : StrictMono u) (hp : Paired s u) :
    0 ≤ splitDet 0 x s u := by
  let a : Fin 4 → Bool := fun i ↦ decide (x i < s 0)
  let b : Fin 4 → Bool := fun i ↦ decide (x i < s 1)
  let c : Fin 4 → Bool := fun i ↦ decide (u 0 < x i)
  let d : Fin 4 → Bool := fun i ↦ decide (u 1 < x i)
  have hs01 : s 0 < s 1 := hs (by decide)
  have hu01 : u 0 < u 1 := hu (by decide)
  have hp0 : s 0 < u 0 := hp 0
  have hp1 : s 1 < u 1 := hp 1
  have hadm : DegreeZeroAdmissible a b c d := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j hij hj
      change decide (x j < s 0) = true at hj
      change decide (x i < s 0) = true
      exact decide_eq_true (lt_trans (hx hij) (of_decide_eq_true hj))
    · intro i j hij hj
      change decide (x j < s 1) = true at hj
      change decide (x i < s 1) = true
      exact decide_eq_true (lt_trans (hx hij) (of_decide_eq_true hj))
    · intro i j hij hi
      change decide (u 0 < x i) = true at hi
      change decide (u 0 < x j) = true
      exact decide_eq_true (lt_trans (of_decide_eq_true hi) (hx hij))
    · intro i j hij hi
      change decide (u 1 < x i) = true at hi
      change decide (u 1 < x j) = true
      exact decide_eq_true (lt_trans (of_decide_eq_true hi) (hx hij))
    · intro i hi
      change decide (x i < s 0) = true at hi
      change decide (x i < s 1) = true
      exact decide_eq_true (lt_trans (of_decide_eq_true hi) hs01)
    · intro i hi
      change decide (u 1 < x i) = true at hi
      change decide (u 0 < x i) = true
      exact decide_eq_true (lt_trans hu01 (of_decide_eq_true hi))
    · intro i hi
      change decide (x i < s 0) = true at hi
      change decide (u 0 < x i) = false
      exact decide_eq_false (not_lt_of_ge (le_of_lt
        (lt_trans (of_decide_eq_true hi) hp0)))
    · intro i hi
      change decide (x i < s 1) = true at hi
      change decide (u 1 < x i) = false
      exact decide_eq_false (not_lt_of_ge (le_of_lt
        (lt_trans (of_decide_eq_true hi) hp1)))
  rcases exists_initialStep a hadm.1 with ⟨A, hA⟩
  rcases exists_initialStep b hadm.2.1 with ⟨B, hB⟩
  rcases exists_terminalStep c hadm.2.2.1 with ⟨C, hC⟩
  rcases exists_terminalStep d hadm.2.2.2.1 with ⟨D, hD⟩
  have hadmCuts : DegreeZeroAdmissible (initialStep A) (initialStep B)
      (terminalStep C) (terminalStep D) := by
    simpa only [← hA, ← hB, ← hC, ← hD] using hadm
  have hdet : 0 ≤ (degreeZeroStepMatrix a b c d).det := by
    rw [hA, hB, hC, hD]
    exact degreeZeroCutMatrix_det_nonneg A B C D hadmCuts
  have hmatrix :
      splitMatrix 0 x s u =
        (degreeZeroStepMatrix a b c d).map (Int.castRingHom ℝ) := by
    ext i j
    cases hside : (groupedColumnEquiv 2).symm j with
    | inl q =>
        fin_cases q <;>
          simp [splitMatrix, degreeZeroStepMatrix, hside,
            a, b, leftKernel, truncPow, sub_pos]
    | inr q =>
        fin_cases q <;>
          simp [splitMatrix, degreeZeroStepMatrix, hside,
            c, d, rightKernel, truncPow, sub_pos]
  unfold splitDet
  rw [hmatrix]
  have hcast :
      (((degreeZeroStepMatrix a b c d).det : ℤ) : ℝ) =
        ((degreeZeroStepMatrix a b c d).map (Int.castRingHom ℝ)).det :=
    (Int.castRingHom ℝ).map_det (degreeZeroStepMatrix a b c d)
  rw [← hcast]
  exact_mod_cast hdet

/-- Public `PairedSplitNonnegative` wrapper for the degree-zero critical base. -/
theorem pairedSplitNonnegative_two_zero (x : Fin (2 * 2) → ℝ)
    (hx : StrictMono x) : PairedSplitNonnegative (m := 2) 0 x := by
  intro s u hs hu hp
  exact criticalSplitDet_two_zero_nonneg hx hs hu hp

end

end ColomboGeneralK2.Odd
