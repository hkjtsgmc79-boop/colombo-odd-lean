import ColomboGeneralK2.OddMVP1Signatures

/-!
# Closing paired split determinants onto the diagonal

The paired hypothesis concerns genuinely separated left and right knots.  This
file records the one-sided limiting argument which also gives the diagonal
split determinant its nonnegative sign.  Shifting only the right knots is
important at exponent zero: it has the correct one-sided value even though an
individual strict truncated power need not be continuous there.
-/

namespace ColomboGeneralK2.Odd

open Filter
open scoped BigOperators Topology

noncomputable section

/-- Positive-exponent strict truncated powers are continuous. -/
theorem truncPow_succ_continuous (r : Nat) :
    Continuous (fun y : Real => truncPow (r + 1) y) := by
  have h : (fun y : Real => truncPow (r + 1) y) =
      fun y => (max y 0) ^ (r + 1) := by
    funext y
    rcases lt_or_ge 0 y with hy | hy
    · simp [truncPow, hy, max_eq_left hy.le]
    · simp [truncPow, hy]
  rw [h]
  fun_prop

/-- At exponent zero, shifting the right knots outwards converges to the
diagonal split matrix from the right. -/
theorem splitDet_zero_tendsto_diagonal {m : Nat} (x : Fin (2 * m) → Real)
    (t : Fin m → Real) :
    Tendsto
      (fun ε : Real => splitDet 0 x t (fun q => t q + ε))
      (𝓝[>] 0) (𝓝 (splitDet 0 x t t)) := by
  have hright (i : Fin (2 * m)) (q : Fin m) :
      ∀ᶠ ε : Real in 𝓝[>] 0,
        rightKernel 0 x (t q + ε) i = rightKernel 0 x (t q) i := by
    rcases lt_or_ge (t q) (x i) with htx | hxt
    · have hmem : Set.Iio (x i - t q) ∈ 𝓝[>] (0 : Real) :=
        Filter.Eventually.filter_mono
          (show 𝓝[>] (0 : Real) ≤ 𝓝 0 from nhdsWithin_le_nhds)
          (Iio_mem_nhds (sub_pos.mpr htx))
      filter_upwards [hmem] with ε hε
      change ε < x i - t q at hε
      simp only [rightKernel]
      rw [truncPow_of_pos (by linarith), truncPow_of_pos (by linarith)]
      simp
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      change 0 < ε at hε
      simp only [rightKernel]
      rw [truncPow_of_nonpos (by linarith),
        truncPow_of_nonpos (by linarith)]
  have hall : ∀ᶠ ε : Real in 𝓝[>] 0,
      ∀ i : Fin (2 * m), ∀ q : Fin m,
        rightKernel 0 x (t q + ε) i = rightKernel 0 x (t q) i := by
    simpa using
      ((Filter.eventually_all_finset (l := 𝓝[>] (0 : Real))
        (p := fun z ε =>
          rightKernel 0 x (t z.2 + ε) z.1 = rightKernel 0 x (t z.2) z.1)
        (Finset.univ : Finset (Fin (2 * m) × Fin m))).mpr
        (by rintro ⟨i, q⟩ _; exact hright i q))
  have hmat : ∀ᶠ ε : Real in 𝓝[>] 0,
      splitMatrix 0 x t (fun q => t q + ε) =
        splitMatrix 0 x t t := by
    filter_upwards [hall] with ε hε
    ext i col
    cases hcol : (groupedColumnEquiv m).symm col with
    | inl q =>
        simp [splitMatrix, hcol]
    | inr q =>
        simpa [splitMatrix, hcol] using hε i q
  have hdet : ∀ᶠ ε : Real in 𝓝[>] 0,
      splitDet 0 x t (fun q => t q + ε) = splitDet 0 x t t := by
    filter_upwards [hmat] with ε hε
    simpa [splitDet] using congrArg Matrix.det hε
  exact Filter.Tendsto.congr'
    (by
      filter_upwards [hdet] with ε hε
      exact hε.symm)
    tendsto_const_nhds

/-- For positive exponents the same right shift is an ordinary continuous
specialization of the split determinant. -/
theorem splitDet_succ_tendsto_diagonal {m r : Nat} (x : Fin (2 * m) → Real)
    (t : Fin m → Real) :
    Tendsto
      (fun ε : Real =>
        splitDet (r + 1) x t (fun q => t q + ε))
      (𝓝[>] 0) (𝓝 (splitDet (r + 1) x t t)) := by
  have hcont : Continuous (fun ε : Real =>
      splitDet (r + 1) x t (fun q => t q + ε)) := by
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

/-- Every diagonal grouped split determinant is nonnegative under the paired
split hypothesis. -/
theorem PairedSplitNonnegative.groupedSplitMatrix_det_nonnegative
    {m : Nat} {r : Nat} {x : Fin (2 * m) → Real} {t : Fin m → Real}
    (hSplit : PairedSplitNonnegative r x) (ht : StrictMono t) :
    0 ≤ (groupedSplitMatrix r x t).det := by
  have hordered_right (ε : Real) : StrictMono (fun q => t q + ε) := by
    intro a b hab
    dsimp
    linarith [ht hab]
  have hpaired (ε : Real) (hε : 0 < ε) :
      Paired t (fun q => t q + ε) := by
    intro q
    dsimp
    linarith
  have hnonneg : ∀ᶠ ε : Real in 𝓝[>] 0,
      0 ≤ splitDet r x t (fun q => t q + ε) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hSplit _ _ ht (hordered_right ε) (hpaired ε hε)
  have hlim : Tendsto
      (fun ε : Real => splitDet r x t (fun q => t q + ε))
      (𝓝[>] 0) (𝓝 (splitDet r x t t)) := by
    cases r with
    | zero => simpa using splitDet_zero_tendsto_diagonal x t
    | succ r => simpa [Nat.succ_eq_add_one] using splitDet_succ_tendsto_diagonal (r := r) x t
  have hclosed : splitDet r x t t ∈ Set.Ici (0 : Real) :=
    isClosed_Ici.mem_of_tendsto hlim hnonneg
  simpa using hclosed

/-- The diagonal form of the paired-split closure lemma. -/
theorem pairedSplitNonnegative_diagonal
    {m : Nat} {r : Nat} {x : Fin (2 * m) → Real} {t : Fin m → Real}
    (hSplit : PairedSplitNonnegative r x) (ht : StrictMono t) :
    0 ≤ splitDet r x t t := by
  simpa using hSplit.groupedSplitMatrix_det_nonnegative ht

end

end ColomboGeneralK2.Odd
