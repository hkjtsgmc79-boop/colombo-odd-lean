import ColomboGeneralK2.OddOrderedChamber
import ColomboGeneralK2.OddPairedSplitLimit
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace ColomboGeneralK2.Odd

open MeasureTheory
open scoped BigOperators Pointwise

noncomputable section

/-- The strict Heaviside step used in the paper's Volterra determinants. -/
def strictStep (a s : Real) : Real :=
  if a < s then 1 else 0

@[simp]
theorem strictStep_of_lt {a s : Real} (h : a < s) : strictStep a s = 1 := by
  simp [strictStep, h]

@[simp]
theorem strictStep_of_le {a s : Real} (h : s ≤ a) : strictStep a s = 0 := by
  simp [strictStep, not_lt.mpr h]

private theorem leftVolterraKernel_as_indicator (q : Nat) (x s a : Real) :
    truncPow q (a - x) * strictStep a s =
      Set.indicator (Set.Ioo x s) (fun y : Real ↦ (y - x) ^ q) a := by
  by_cases hax : x < a
  · by_cases has : a < s
    · rw [Set.indicator_of_mem (show a ∈ Set.Ioo x s from ⟨hax, has⟩),
        truncPow_of_pos (sub_pos.mpr hax),
        strictStep_of_lt has, mul_one]
    · have hsa : s ≤ a := le_of_not_gt has
      rw [Set.indicator_of_notMem (fun h ↦ has h.2), strictStep_of_le hsa, mul_zero]
  · have hxa : a ≤ x := le_of_not_gt hax
    rw [Set.indicator_of_notMem (fun h ↦ hax h.1),
      truncPow_of_nonpos (sub_nonpos.mpr hxa), zero_mul]

private theorem rightVolterraKernel_as_indicator (q : Nat) (u x b : Real) :
    truncPow q (x - b) * strictStep u b =
      Set.indicator (Set.Ioo u x) (fun y : Real ↦ (x - y) ^ q) b := by
  by_cases hub : u < b
  · by_cases hbx : b < x
    · rw [Set.indicator_of_mem (show b ∈ Set.Ioo u x from ⟨hub, hbx⟩),
        truncPow_of_pos (sub_pos.mpr hbx),
        strictStep_of_lt hub, mul_one]
    · have hxb : x ≤ b := le_of_not_gt hbx
      rw [Set.indicator_of_notMem (fun h ↦ hbx h.2),
        truncPow_of_nonpos (sub_nonpos.mpr hxb), zero_mul]
  · have hbu : b ≤ u := le_of_not_gt hub
    rw [Set.indicator_of_notMem (fun h ↦ hub h.1), strictStep_of_le hbu, mul_zero]

/-- Every scalar left Volterra column is integrable on the labelled line. -/
theorem leftVolterraKernel_integrable (q : Nat) (x s : Real) :
    Integrable (fun a : Real ↦ truncPow q (a - x) * strictStep a s) := by
  rw [show (fun a : Real ↦ truncPow q (a - x) * strictStep a s) =
      Set.indicator (Set.Ioo x s) (fun a : Real ↦ (a - x) ^ q) by
    funext a
    exact leftVolterraKernel_as_indicator q x s a]
  exact (((continuous_id.sub continuous_const).pow q).integrableOn_Icc.mono_set
    Set.Ioo_subset_Icc_self).integrable_indicator measurableSet_Ioo

/-- Every scalar right Volterra column is integrable on the labelled line. -/
theorem rightVolterraKernel_integrable (q : Nat) (u x : Real) :
    Integrable (fun b : Real ↦ truncPow q (x - b) * strictStep u b) := by
  rw [show (fun b : Real ↦ truncPow q (x - b) * strictStep u b) =
      Set.indicator (Set.Ioo u x) (fun b : Real ↦ (x - b) ^ q) by
    funext b
    exact rightVolterraKernel_as_indicator q u x b]
  exact (((continuous_const.sub continuous_id).pow q).integrableOn_Icc.mono_set
    Set.Ioo_subset_Icc_self).integrable_indicator measurableSet_Ioo

/-- Scalar left Volterra identity, with the paper's exact factor `q+1`. -/
theorem truncPow_succ_left_volterra (q : Nat) (x s : Real) :
    truncPow (q + 1) (s - x) =
      (q + 1 : Real) *
        ∫ a : Real, truncPow q (a - x) * strictStep a s := by
  by_cases hxs : x < s
  · rw [truncPow_of_pos (sub_pos.mpr hxs)]
    rw [show (fun a : Real ↦ truncPow q (a - x) * strictStep a s) =
        Set.indicator (Set.Ioo x s) (fun a : Real ↦ (a - x) ^ q) by
      funext a
      exact leftVolterraKernel_as_indicator q x s a]
    rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hxs.le]
    have hshift :
        (∫ a : Real in x..s, (a - x) ^ q) =
          ∫ y : Real in 0..s - x, y ^ q := by
      simpa using
        (intervalIntegral.integral_comp_sub_right (fun y : Real ↦ y ^ q) x
          (a := x) (b := s))
    rw [hshift, integral_pow]
    norm_num
    field_simp
  · have hsx : s ≤ x := le_of_not_gt hxs
    rw [truncPow_of_nonpos (sub_nonpos.mpr hsx)]
    have hzero : (fun a : Real ↦ truncPow q (a - x) * strictStep a s) = fun _ ↦ 0 := by
      funext a
      by_cases hax : x < a
      · rw [strictStep_of_le (hsx.trans hax.le), mul_zero]
      · rw [truncPow_of_nonpos (sub_nonpos.mpr (le_of_not_gt hax)), zero_mul]
    rw [hzero, integral_zero, mul_zero]

/-- Scalar right Volterra identity, with the paper's exact factor `q+1`. -/
theorem truncPow_succ_right_volterra (q : Nat) (x u : Real) :
    truncPow (q + 1) (x - u) =
      (q + 1 : Real) *
        ∫ b : Real, truncPow q (x - b) * strictStep u b := by
  by_cases hux : u < x
  · rw [truncPow_of_pos (sub_pos.mpr hux)]
    rw [show (fun b : Real ↦ truncPow q (x - b) * strictStep u b) =
        Set.indicator (Set.Ioo u x) (fun b : Real ↦ (x - b) ^ q) by
      funext b
      exact rightVolterraKernel_as_indicator q u x b]
    rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hux.le]
    have hshift :
        (∫ b : Real in u..x, (x - b) ^ q) =
          ∫ y : Real in 0..x - u, y ^ q := by
      simpa using
        (intervalIntegral.integral_comp_sub_left (fun y : Real ↦ y ^ q) x
          (a := u) (b := x))
    rw [hshift, integral_pow]
    norm_num
    field_simp
  · have hxu : x ≤ u := le_of_not_gt hux
    rw [truncPow_of_nonpos (sub_nonpos.mpr hxu)]
    have hzero : (fun b : Real ↦ truncPow q (x - b) * strictStep u b) = fun _ ↦ 0 := by
      funext b
      by_cases hub : u < b
      · rw [truncPow_of_nonpos (sub_nonpos.mpr (hxu.trans hub.le)), zero_mul]
      · rw [strictStep_of_le (le_of_not_gt hub), mul_zero]
    rw [hzero, integral_zero, mul_zero]

/-! ## Integrating independent determinant columns -/

/-- A determinant whose labelled columns are independently integrable is
itself integrable on the finite product. -/
theorem det_columns_integrable {n : Type*} [Fintype n] [DecidableEq n]
    (f : n → n → Real → Real)
    (hf : ∀ i j, Integrable (f i j)) :
    Integrable
      (fun z : n → Real ↦ Matrix.det (fun i j ↦ f i j (z j)))
      (Measure.pi fun _ : n ↦ (volume : Measure Real)) := by
  classical
  simp only [Matrix.det_apply']
  apply integrable_finsetSum Finset.univ
  intro σ hσ
  exact (Integrable.fintype_prod (fun j ↦ hf (σ j) j)).const_mul
    ((σ.sign : Int) : Real)

/-- Columnwise Fubini for a square determinant.  Expanding by Leibniz and
using finite-product Fubini leaves the determinant of the scalar integrals. -/
theorem integral_det_columns {n : Type*} [Fintype n] [DecidableEq n]
    (f : n → n → Real → Real)
    (hf : ∀ i j, Integrable (f i j)) :
    (∫ z : n → Real,
        Matrix.det (fun i j ↦ f i j (z j))
        ∂(Measure.pi fun _ : n ↦ (volume : Measure Real))) =
      Matrix.det (fun i j ↦ ∫ t : Real, f i j t) := by
  classical
  calc
    (∫ z : n → Real,
        Matrix.det (fun i j ↦ f i j (z j))
        ∂(Measure.pi fun _ : n ↦ (volume : Measure Real))) =
        ∫ z : n → Real,
          ∑ σ : Equiv.Perm n,
            ((σ.sign : Int) : Real) * ∏ j, f (σ j) j (z j)
          ∂(Measure.pi fun _ : n ↦ (volume : Measure Real)) := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact Matrix.det_apply' _
    _ = ∑ σ : Equiv.Perm n,
        ∫ z : n → Real,
          ((σ.sign : Int) : Real) * ∏ j, f (σ j) j (z j)
          ∂(Measure.pi fun _ : n ↦ (volume : Measure Real)) := by
      rw [integral_finsetSum Finset.univ]
      intro σ hσ
      exact (Integrable.fintype_prod (fun j ↦ hf (σ j) j)).const_mul
        ((σ.sign : Int) : Real)
    _ = ∑ σ : Equiv.Perm n,
        ((σ.sign : Int) : Real) * ∏ j, ∫ t : Real, f (σ j) j t := by
      apply Fintype.sum_congr
      intro σ
      rw [integral_const_mul, integral_fintype_prod_eq_prod]
    _ = Matrix.det (fun i j ↦ ∫ t : Real, f i j t) := by
      rw [Matrix.det_apply']

/-! ## The two paper-facing step determinants -/

/-- Left step matrix `[1_{a_i<s_j}]`. -/
def leftStepMatrix {m : Nat} (a s : Fin m → Real) : Matrix (Fin m) (Fin m) Real :=
  fun i j ↦ strictStep (a i) (s j)

/-- Right step matrix `[1_{u_j<b_i}]`.  It is the transpose of the same
Ferrers matrix with knot lists `u,b`. -/
def rightStepMatrix {m : Nat} (u b : Fin m → Real) : Matrix (Fin m) (Fin m) Real :=
  (leftStepMatrix u b).transpose

/-- The paper's left step determinant. -/
def leftStepDet {m : Nat} (a s : Fin m → Real) : Real :=
  (leftStepMatrix a s).det

/-- The paper's right step determinant. -/
def rightStepDet {m : Nat} (u b : Fin m → Real) : Real :=
  (rightStepMatrix u b).det

@[simp]
theorem rightStepDet_eq_leftStepDet {m : Nat} (u b : Fin m → Real) :
    rightStepDet u b = leftStepDet u b := by
  simp [rightStepDet, rightStepMatrix, leftStepDet]

private theorem leftStepDet_zero_or_one_and_support : ∀ {m : Nat}
    (a s : Fin m → Real), StrictMono a → StrictMono s →
      leftStepDet a s = 0 ∨
        (leftStepDet a s = 1 ∧ ∀ i, a i < s i) := by
  intro m
  induction m with
  | zero =>
      intro a s ha hs
      right
      constructor
      · simp [leftStepDet]
      · intro i
        exact Fin.elim0 i
  | succ n ih =>
      intro a s ha hs
      by_cases h00 : a 0 < s 0
      · by_cases hother : ∃ i : Fin (n + 1), i ≠ 0 ∧ a i < s 0
        · rcases hother with ⟨i, hi0, his⟩
          left
          apply Matrix.det_zero_of_row_eq (M := leftStepMatrix a s) hi0.symm
          funext j
          have h0i : (0 : Fin (n + 1)) < i := Fin.pos_iff_ne_zero.mpr hi0
          have hai : a 0 < a i := ha h0i
          have hs0j : s 0 ≤ s j := hs.monotone (Fin.zero_le j)
          simp [leftStepMatrix, strictStep, hai.trans (his.trans_le hs0j),
            his.trans_le hs0j]
        · let a' : Fin n → Real := fun i ↦ a i.succ
          let s' : Fin n → Real := fun i ↦ s i.succ
          have ha' : StrictMono a' := ha.comp Fin.strictMono_succ
          have hs' : StrictMono s' := hs.comp Fin.strictMono_succ
          have hcol : ∀ i : Fin (n + 1), i ≠ 0 →
              leftStepMatrix a s i 0 = 0 := by
            intro i hi
            have hnlt : ¬ a i < s 0 := fun h ↦ hother ⟨i, hi, h⟩
            simp [leftStepMatrix, strictStep, hnlt]
          have hminor :
              (leftStepMatrix a s).submatrix (Fin.succ : Fin n → Fin (n + 1))
                  (Fin.succ : Fin n → Fin (n + 1)) =
                leftStepMatrix a' s' := by
            ext i j
            rfl
          have hdet : leftStepDet a s = leftStepDet a' s' := by
            rw [leftStepDet, Matrix.det_succ_column_zero,
              Finset.sum_eq_single 0]
            · simp [leftStepMatrix, h00, hminor, leftStepDet]
            · intro i hi hi0
              rw [hcol i hi0]
              simp
            · simp
          rcases ih a' s' ha' hs' with hzero | ⟨hone, hsupp⟩
          · exact Or.inl (hdet.trans hzero)
          · right
            constructor
            · exact hdet.trans hone
            · intro i
              refine Fin.cases h00 (fun k ↦ ?_) i
              exact hsupp k
      · left
        have hs0a0 : s 0 ≤ a 0 := le_of_not_gt h00
        rw [leftStepDet, Matrix.det_succ_column_zero]
        apply Finset.sum_eq_zero
        intro i hi
        have ha0i : a 0 ≤ a i := ha.monotone (Fin.zero_le i)
        have hsi : s 0 ≤ a i := hs0a0.trans ha0i
        rw [show leftStepMatrix a s i 0 = 0 by
          simp [leftStepMatrix, strictStep, not_lt.mpr hsi]]
        simp

/-- On strictly ordered lists, the left step determinant is exactly `0` or
`1`; in particular it is nonnegative. -/
theorem leftStepDet_eq_zero_or_one {m : Nat} {a s : Fin m → Real}
    (ha : StrictMono a) (hs : StrictMono s) :
    leftStepDet a s = 0 ∨ leftStepDet a s = 1 := by
  rcases leftStepDet_zero_or_one_and_support a s ha hs with h | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr h

theorem leftStepDet_nonnegative {m : Nat} {a s : Fin m → Real}
    (ha : StrictMono a) (hs : StrictMono s) : 0 ≤ leftStepDet a s := by
  rcases leftStepDet_eq_zero_or_one ha hs with h | h
  · rw [h]
  · rw [h]
    norm_num

/-- Nonzero left step determinant support forces the coordinatewise left
inequalities `a_i<s_i`. -/
theorem leftStepDet_support {m : Nat} {a s : Fin m → Real}
    (ha : StrictMono a) (hs : StrictMono s) (hdet : leftStepDet a s ≠ 0) :
    ∀ i, a i < s i := by
  rcases leftStepDet_zero_or_one_and_support a s ha hs with h | ⟨_, hsupp⟩
  · exact (hdet h).elim
  · exact hsupp

theorem rightStepDet_eq_zero_or_one {m : Nat} {u b : Fin m → Real}
    (hu : StrictMono u) (hb : StrictMono b) :
    rightStepDet u b = 0 ∨ rightStepDet u b = 1 := by
  simpa only [rightStepDet_eq_leftStepDet] using leftStepDet_eq_zero_or_one hu hb

theorem rightStepDet_nonnegative {m : Nat} {u b : Fin m → Real}
    (hu : StrictMono u) (hb : StrictMono b) : 0 ≤ rightStepDet u b := by
  rw [rightStepDet_eq_leftStepDet]
  exact leftStepDet_nonnegative hu hb

/-- Nonzero right step determinant support forces `u_i<b_i`. -/
theorem rightStepDet_support {m : Nat} {u b : Fin m → Real}
    (hu : StrictMono u) (hb : StrictMono b) (hdet : rightStepDet u b ≠ 0) :
    ∀ i, u i < b i := by
  apply leftStepDet_support hu hb
  simpa only [rightStepDet_eq_leftStepDet] using hdet

private theorem integral_leftVolterraKernel (q : Nat) (x s : Real) :
    (∫ a : Real, truncPow q (a - x) * strictStep a s) =
      (q + 1 : Real)⁻¹ * truncPow (q + 1) (s - x) := by
  have h := truncPow_succ_left_volterra q x s
  have hc : (q + 1 : Real) ≠ 0 := by positivity
  calc
    (∫ a : Real, truncPow q (a - x) * strictStep a s) =
        (q + 1 : Real)⁻¹ *
          ((q + 1 : Real) * ∫ a : Real,
            truncPow q (a - x) * strictStep a s) := by
      field_simp
    _ = (q + 1 : Real)⁻¹ * truncPow (q + 1) (s - x) := by rw [← h]

private theorem integral_rightVolterraKernel (q : Nat) (x u : Real) :
    (∫ b : Real, truncPow q (x - b) * strictStep u b) =
      (q + 1 : Real)⁻¹ * truncPow (q + 1) (x - u) := by
  have h := truncPow_succ_right_volterra q x u
  have hc : (q + 1 : Real) ≠ 0 := by positivity
  calc
    (∫ b : Real, truncPow q (x - b) * strictStep u b) =
        (q + 1 : Real)⁻¹ *
          ((q + 1 : Real) * ∫ b : Real,
            truncPow q (x - b) * strictStep u b) := by
      field_simp
    _ = (q + 1 : Real)⁻¹ * truncPow (q + 1) (x - u) := by rw [← h]

/-! ## Labelled column integral before antisymmetrization -/

/-- The independently labelled scalar columns on `Fin m ⊕ Fin m`.
The first summand labels left columns and the second labels right columns. -/
def volterraColumnKernel {m : Nat} (q : Nat) (x : Fin (2 * m) → Real)
    (s u : Fin m → Real) :
    (Fin m ⊕ Fin m) → (Fin m ⊕ Fin m) → Real → Real :=
  fun row col t ↦
    match col with
    | Sum.inl j =>
        truncPow q (t - x (groupedColumnEquiv m row)) * strictStep t (s j)
    | Sum.inr j =>
        truncPow q (x (groupedColumnEquiv m row) - t) * strictStep (u j) t

theorem volterraColumnKernel_integrable {m : Nat} (q : Nat)
    (x : Fin (2 * m) → Real) (s u : Fin m → Real) :
    ∀ row col, Integrable (volterraColumnKernel q x s u row col) := by
  intro row col
  cases col with
  | inl j => exact leftVolterraKernel_integrable q _ _
  | inr j => exact rightVolterraKernel_integrable q _ _

/-- The labelled determinant is integrable before either family of labels is
ordered. -/
theorem volterraLabelledDet_integrable {m : Nat} (q : Nat)
    (x : Fin (2 * m) → Real) (s u : Fin m → Real) :
    Integrable
      (fun z : (Fin m ⊕ Fin m) → Real ↦
        Matrix.det (fun i j ↦ volterraColumnKernel q x s u i j (z j)))
      (Measure.pi fun _ : Fin m ⊕ Fin m ↦ (volume : Measure Real)) :=
  det_columns_integrable _ (volterraColumnKernel_integrable q x s u)

private theorem integral_volterraColumnKernel_matrix {m : Nat} (q : Nat)
    (x : Fin (2 * m) → Real) (s u : Fin m → Real) :
    (fun i j ↦ ∫ t : Real, volterraColumnKernel q x s u i j t) =
      (q + 1 : Real)⁻¹ •
        (splitMatrix (q + 1) x s u).submatrix
          (groupedColumnEquiv m) (groupedColumnEquiv m) := by
  ext i j
  cases j with
  | inl j =>
      simp only [volterraColumnKernel, Matrix.smul_apply, Matrix.submatrix_apply]
      rw [integral_leftVolterraKernel]
      simp [splitMatrix, leftKernel]
  | inr j =>
      simp only [volterraColumnKernel, Matrix.smul_apply, Matrix.submatrix_apply]
      rw [integral_rightVolterraKernel]
      simp [splitMatrix, rightKernel]

/-- Full labelled column integration.  Each of the `2m` columns contributes
one factor `(q+1)⁻¹`. -/
theorem integral_volterraLabelledDet {m : Nat} (q : Nat)
    (x : Fin (2 * m) → Real) (s u : Fin m → Real) :
    (∫ z : (Fin m ⊕ Fin m) → Real,
        Matrix.det (fun i j ↦ volterraColumnKernel q x s u i j (z j))
        ∂(Measure.pi fun _ : Fin m ⊕ Fin m ↦ (volume : Measure Real))) =
      ((q + 1 : Real)⁻¹) ^ (2 * m) * splitDet (q + 1) x s u := by
  rw [integral_det_columns _ (volterraColumnKernel_integrable q x s u),
    integral_volterraColumnKernel_matrix, Matrix.det_smul,
    Matrix.det_submatrix_equiv_self]
  simp only [Fintype.card_sum, Fintype.card_fin, splitDet]
  ring

/-- The same labelled matrix after splitting the sum-indexed tuple into its
left and right labelled families. -/
def labelledVolterraMatrix {m : Nat} (q : Nat)
    (x : Fin (2 * m) → Real) (s u a b : Fin m → Real) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) Real :=
  fun row col ↦
    match col with
    | Sum.inl j =>
        truncPow q (a j - x (groupedColumnEquiv m row)) * strictStep (a j) (s j)
    | Sum.inr j =>
        truncPow q (x (groupedColumnEquiv m row) - b j) * strictStep (u j) (b j)

/-- Raw labelled determinant.  It is not pointwise nonnegative. -/
def labelledVolterraDet {m : Nat} (q : Nat)
    (x : Fin (2 * m) → Real) (s u a b : Fin m → Real) : Real :=
  (labelledVolterraMatrix q x s u a b).det

private theorem volterraColumnKernel_sumPi {m : Nat} (q : Nat)
    (x : Fin (2 * m) → Real) (s u : Fin m → Real)
    (z : (Fin m ⊕ Fin m) → Real) :
    Matrix.det (fun i j ↦ volterraColumnKernel q x s u i j (z j)) =
      labelledVolterraDet q x s u
        (Equiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin m ↦ Real) z).1
        (Equiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin m ↦ Real) z).2 := by
  apply congrArg Matrix.det
  ext i j
  cases j <;>
    simp [volterraColumnKernel, labelledVolterraMatrix,
      Equiv.sumPiEquivProdPi_apply]

/-- Full labelled Fubini identity on the product of the two labelled tuple
spaces. -/
theorem integral_labelledVolterraDet {m : Nat} (q : Nat)
    (x : Fin (2 * m) → Real) (s u : Fin m → Real) :
    (∫ z : (Fin m → Real) × (Fin m → Real),
        labelledVolterraDet q x s u z.1 z.2
        ∂((tupleVolume m).prod (tupleVolume m))) =
      ((q + 1 : Real)⁻¹) ^ (2 * m) * splitDet (q + 1) x s u := by
  let e := MeasurableEquiv.sumPiEquivProdPi
    (fun _ : Fin m ⊕ Fin m ↦ Real)
  have hmap := (measurePreserving_sumPiEquivProdPi
      (fun _ : Fin m ⊕ Fin m ↦ (volume : Measure Real))).integral_comp'
    (fun z : (Fin m → Real) × (Fin m → Real) ↦
      labelledVolterraDet q x s u z.1 z.2)
  calc
    (∫ z : (Fin m → Real) × (Fin m → Real),
        labelledVolterraDet q x s u z.1 z.2
        ∂((tupleVolume m).prod (tupleVolume m))) =
        ∫ z : (Fin m ⊕ Fin m) → Real,
          Matrix.det (fun i j ↦ volterraColumnKernel q x s u i j (z j))
          ∂(Measure.pi fun _ : Fin m ⊕ Fin m ↦ (volume : Measure Real)) := by
      rw [← hmap]
      apply integral_congr_ae
      filter_upwards [] with z
      exact (volterraColumnKernel_sumPi q x s u z).symm
    _ = _ := integral_volterraLabelledDet q x s u

/-- Before antisymmetrization, the determinant is the lower-degree split
determinant times the two products of labelled scalar steps. -/
theorem labelledVolterraDet_eq {m : Nat} (q : Nat)
    (x : Fin (2 * m) → Real) (s u a b : Fin m → Real) :
    labelledVolterraDet q x s u a b =
      splitDet q x a b *
        (∏ j, strictStep (a j) (s j)) *
        ∏ j, strictStep (u j) (b j) := by
  let w : Fin m ⊕ Fin m → Real := fun col ↦
    match col with
    | Sum.inl j => strictStep (a j) (s j)
    | Sum.inr j => strictStep (u j) (b j)
  let B : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) Real :=
    (splitMatrix q x a b).submatrix (groupedColumnEquiv m) (groupedColumnEquiv m)
  have hmatrix : labelledVolterraMatrix q x s u a b =
      Matrix.of (fun i j ↦ w j * B i j) := by
    ext i j
    cases j <;> simp [labelledVolterraMatrix, w, B, splitMatrix,
      leftKernel, rightKernel, mul_comm]
  rw [labelledVolterraDet, hmatrix, Matrix.det_mul_row, Fintype.prod_sum_type]
  change
    ((∏ j, strictStep (a j) (s j)) * ∏ j, strictStep (u j) (b j)) *
        B.det = _
  have hB : B.det = splitDet q x a b := by
    simp [B, splitDet, Matrix.det_submatrix_equiv_self]
  rw [hB]
  ring

/-! ## The independent left/right permutation chamber -/

/-- Independent coordinate permutations act on the two labelled knot
families. -/
instance pairTuplePermSMul (m : Nat) :
    SMul (Equiv.Perm (Fin m) × Equiv.Perm (Fin m))
      ((Fin m → Real) × (Fin m → Real)) :=
  ⟨fun g z ↦ (g.1 • z.1, g.2 • z.2)⟩

instance pairTuplePermMulAction (m : Nat) :
    MulAction (Equiv.Perm (Fin m) × Equiv.Perm (Fin m))
      ((Fin m → Real) × (Fin m → Real)) where
  one_smul z := by
    change (((1 : Equiv.Perm (Fin m)) • z.1),
      ((1 : Equiv.Perm (Fin m)) • z.2)) = z
    simp
  mul_smul g h z := by
    change (((g.1 * h.1) • z.1), ((g.2 * h.2) • z.2)) =
      (g.1 • (h.1 • z.1), g.2 • (h.2 • z.2))
    rw [mul_smul, mul_smul]

@[simp]
theorem pairTuplePerm_smul_fst {m : Nat}
    (g : Equiv.Perm (Fin m) × Equiv.Perm (Fin m))
    (z : (Fin m → Real) × (Fin m → Real)) :
    (g • z).1 = g.1 • z.1 := rfl

@[simp]
theorem pairTuplePerm_smul_snd {m : Nat}
    (g : Equiv.Perm (Fin m) × Equiv.Perm (Fin m))
    (z : (Fin m → Real) × (Fin m → Real)) :
    (g • z).2 = g.2 • z.2 := rfl

/-- Independent coordinate permutations preserve the product of the two
tuple-volume measures. -/
theorem pairTuplePerm_measurePreserving {m : Nat}
    (g : Equiv.Perm (Fin m) × Equiv.Perm (Fin m)) :
    MeasurePreserving
      (fun z : (Fin m → Real) × (Fin m → Real) ↦ g • z)
      ((tupleVolume m).prod (tupleVolume m))
      ((tupleVolume m).prod (tupleVolume m)) := by
  simpa only [pairTuplePerm_smul_fst, pairTuplePerm_smul_snd] using
    (tuplePerm_measurePreserving g.1).prod (tuplePerm_measurePreserving g.2)

instance pairTuplePermMeasurableConstSMul (m : Nat) :
    MeasurableConstSMul (Equiv.Perm (Fin m) × Equiv.Perm (Fin m))
      ((Fin m → Real) × (Fin m → Real)) :=
  ⟨fun g ↦ (pairTuplePerm_measurePreserving g).measurable⟩

instance pairTuplePermInvariantMeasure (m : Nat) :
    SMulInvariantMeasure
      (Equiv.Perm (Fin m) × Equiv.Perm (Fin m))
      ((Fin m → Real) × (Fin m → Real))
      ((tupleVolume m).prod (tupleVolume m)) :=
  ⟨fun g s hs ↦ by
    let h := pairTuplePerm_measurePreserving g
    calc
      ((tupleVolume m).prod (tupleVolume m))
          ((fun z : (Fin m → Real) × (Fin m → Real) ↦ g • z) ⁻¹' s) =
          Measure.map
            (fun z : (Fin m → Real) × (Fin m → Real) ↦ g • z)
            ((tupleVolume m).prod (tupleVolume m)) s :=
        (Measure.map_apply h.measurable hs).symm
      _ = ((tupleVolume m).prod (tupleVolume m)) s := by rw [h.map_eq]⟩

private theorem measurableSet_tupleInjective (m : Nat) :
    MeasurableSet {t : Fin m → Real | Function.Injective t} := by
  have hset : {t : Fin m → Real | Function.Injective t} =
      ⋂ i : Fin m, ⋂ j : Fin m,
        {t : Fin m → Real | i = j ∨ t i ≠ t j} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro ht i j
      by_cases hij : i = j
      · exact Or.inl hij
      · exact Or.inr (fun h ↦ hij (ht h))
    · intro ht i j h
      by_contra hij
      exact (ht i j).resolve_left hij h
  rw [hset]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  by_cases hij : i = j
  · simp [hij]
  · have heq : MeasurableSet {t : Fin m → Real | t i = t j} :=
      measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)
    have hsets : {t : Fin m → Real | i = j ∨ t i ≠ t j} =
        {t : Fin m → Real | t i = t j}ᶜ := by
      ext t
      simp [hij]
    rw [hsets]
    exact heq.compl

private theorem pair_smul_prod_set {m : Nat}
    (g : Equiv.Perm (Fin m) × Equiv.Perm (Fin m))
    (A B : Set (Fin m → Real)) :
    g • (A ×ˢ B) = (g.1 • A) ×ˢ (g.2 • B) := by
  ext z
  constructor
  · intro hz
    rw [Set.mem_smul_set_iff_inv_smul_mem] at hz
    change g.1⁻¹ • z.1 ∈ A ∧ g.2⁻¹ • z.2 ∈ B at hz
    constructor
    · rw [Set.mem_smul_set_iff_inv_smul_mem]
      exact hz.1
    · rw [Set.mem_smul_set_iff_inv_smul_mem]
      exact hz.2
  · intro hz
    rcases hz with ⟨hzA, hzB⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem] at hzA hzB
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    change g.1⁻¹ • z.1 ∈ A ∧ g.2⁻¹ • z.2 ∈ B
    exact ⟨hzA, hzB⟩

/-- `a₀<⋯<aₘ₋₁` and `b₀<⋯<bₘ₋₁` form one fundamental domain
for the two independent label permutations. -/
theorem pairedOrderedChamber_isFundamentalDomain (m : Nat) :
    IsFundamentalDomain
      (Equiv.Perm (Fin m) × Equiv.Perm (Fin m))
      (orderedChamber m ×ˢ orderedChamber m)
      ((tupleVolume m).prod (tupleVolume m)) := by
  refine IsFundamentalDomain.mk''
    ((measurableSet_orderedChamber m).prod
      (measurableSet_orderedChamber m)).nullMeasurableSet ?_ ?_ ?_
  · have hae : ∀ᵐ z : (Fin m → Real) × (Fin m → Real)
        ∂((tupleVolume m).prod (tupleVolume m)),
        Function.Injective z.1 ∧ Function.Injective z.2 := by
      change ∀ᵐ z : (Fin m → Real) × (Fin m → Real)
        ∂((tupleVolume m).prod (tupleVolume m)),
        z ∈ ({t : Fin m → Real | Function.Injective t} ×ˢ
          {t : Fin m → Real | Function.Injective t})
      apply (Measure.ae_prod_iff_ae_ae
        ((measurableSet_tupleInjective m).prod (measurableSet_tupleInjective m))).2
      filter_upwards [tupleVolume_ae_injective] with a ha
      filter_upwards [tupleVolume_ae_injective] with b hb
      exact ⟨ha, hb⟩
    filter_upwards [hae] with z hz
    rcases exists_perm_smul_mem_orderedChamber z.1 hz.1 with ⟨σ, hσ⟩
    rcases exists_perm_smul_mem_orderedChamber z.2 hz.2 with ⟨τ, hτ⟩
    exact ⟨(σ, τ), hσ, hτ⟩
  · intro g hg
    rw [pair_smul_prod_set]
    by_cases hσ : g.1 = 1
    · have hτ : g.2 ≠ 1 := by
        intro h
        apply hg
        exact Prod.ext hσ h
      apply Disjoint.aedisjoint
      rw [Set.disjoint_left]
      intro z hz hch
      exact (Set.disjoint_left.mp
        (disjoint_smul_orderedChamber g.2 hτ)) hz.2 hch.2
    · apply Disjoint.aedisjoint
      rw [Set.disjoint_left]
      intro z hz hch
      exact (Set.disjoint_left.mp
        (disjoint_smul_orderedChamber g.1 hσ)) hz.1 hch.1
  · intro g
    exact (pairTuplePerm_measurePreserving g).quasiMeasurePreserving

/-! ## Antisymmetrizing the two label families -/

/-- Relabelling the left and right column blocks contributes their two
permutation signs separately. -/
theorem splitDet_pairPerm {m : Nat} (q : Nat)
    (x : Fin (2 * m) → Real) (a b : Fin m → Real)
    (σ τ : Equiv.Perm (Fin m)) :
    splitDet q x (σ • a) (τ • b) =
      (((σ.sign : Int) : Real) * ((τ.sign : Int) : Real)) *
        splitDet q x a b := by
  let ρ : Equiv.Perm (Fin m ⊕ Fin m) :=
    Equiv.Perm.sumCongr σ.symm τ.symm
  let π : Equiv.Perm (Fin (2 * m)) :=
    (groupedColumnEquiv m).permCongr ρ
  have hmatrix : splitMatrix q x (σ • a) (τ • b) =
      (splitMatrix q x a b).submatrix id π := by
    ext i col
    let side := (groupedColumnEquiv m).symm col
    have hcol : col = groupedColumnEquiv m side :=
      ((groupedColumnEquiv m).apply_symm_apply col).symm
    rw [hcol]
    cases side <;>
      simp [splitMatrix, π, ρ, tuplePerm_smul_apply,
        Equiv.permCongr_apply]
  rw [splitDet, hmatrix, Matrix.det_permute', Equiv.Perm.sign_permCongr,
    Equiv.Perm.sign_sumCongr]
  simp [splitDet]

/-- The left chamber sum is the left step determinant, not a factorial
multiple of it. -/
theorem sum_perm_leftSteps {m : Nat} (a s : Fin m → Real) :
    (∑ σ : Equiv.Perm (Fin m),
        ((σ.sign : Int) : Real) *
          ∏ j, strictStep ((σ • a) j) (s j)) =
      leftStepDet a s := by
  let F : Equiv.Perm (Fin m) → Real := fun σ ↦
    ((σ.sign : Int) : Real) *
      ∏ j, strictStep ((σ • a) j) (s j)
  let G : Equiv.Perm (Fin m) → Real := fun π ↦
    ((π.sign : Int) : Real) *
      ∏ j, strictStep (a (π j)) (s j)
  calc
    (∑ σ : Equiv.Perm (Fin m),
        ((σ.sign : Int) : Real) *
          ∏ j, strictStep ((σ • a) j) (s j)) = ∑ σ, F σ := rfl
    _ = ∑ π, G π := by
      apply Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin m))) F G
      intro σ
      simp [F, G, tuplePerm_smul_apply]
    _ = leftStepDet a s := by
      rw [leftStepDet, Matrix.det_apply']
      rfl

/-- The independent right chamber sum is the right step determinant. -/
theorem sum_perm_rightSteps {m : Nat} (u b : Fin m → Real) :
    (∑ τ : Equiv.Perm (Fin m),
        ((τ.sign : Int) : Real) *
          ∏ j, strictStep (u j) ((τ • b) j)) =
      rightStepDet u b := by
  let F : Equiv.Perm (Fin m) → Real := fun τ ↦
    ((τ.sign : Int) : Real) *
      ∏ j, strictStep (u j) ((τ • b) j)
  let G : Equiv.Perm (Fin m) → Real := fun π ↦
    ((π.sign : Int) : Real) *
      ∏ j, strictStep (u j) (b (π j))
  calc
    (∑ τ : Equiv.Perm (Fin m),
        ((τ.sign : Int) : Real) *
          ∏ j, strictStep (u j) ((τ • b) j)) = ∑ τ, F τ := rfl
    _ = ∑ π, G π := by
      apply Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin m))) F G
      intro τ
      simp [F, G, tuplePerm_smul_apply]
    _ = rightStepDet u b := by
      rw [rightStepDet, Matrix.det_apply']
      rfl

/-- Both label antisymmetrizations, performed independently.  This is the
pointwise algebra behind the ordered Volterra integrand. -/
theorem sum_pairPerm_labelledVolterraDet {m : Nat} (q : Nat)
    (x : Fin (2 * m) → Real) (s u a b : Fin m → Real) :
    (∑ g : Equiv.Perm (Fin m) × Equiv.Perm (Fin m),
        labelledVolterraDet q x s u (g.1 • a) (g.2 • b)) =
      splitDet q x a b * leftStepDet a s * rightStepDet u b := by
  rw [Fintype.sum_prod_type]
  simp_rw [labelledVolterraDet_eq, splitDet_pairPerm]
  calc
    (∑ σ : Equiv.Perm (Fin m),
        ∑ τ : Equiv.Perm (Fin m),
          ((((σ.sign : Int) : Real) * ((τ.sign : Int) : Real)) *
              splitDet q x a b *
              ∏ j, strictStep ((σ • a) j) (s j)) *
            ∏ j, strictStep (u j) ((τ • b) j)) =
        ∑ σ : Equiv.Perm (Fin m),
          (((σ.sign : Int) : Real) * splitDet q x a b *
              ∏ j, strictStep ((σ • a) j) (s j)) *
            (∑ τ : Equiv.Perm (Fin m),
              ((τ.sign : Int) : Real) *
                ∏ j, strictStep (u j) ((τ • b) j)) := by
      apply Fintype.sum_congr
      intro σ
      rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro τ
      ring
    _ = (∑ σ : Equiv.Perm (Fin m),
          ((σ.sign : Int) : Real) * splitDet q x a b *
            ∏ j, strictStep ((σ • a) j) (s j)) *
        (∑ τ : Equiv.Perm (Fin m),
          ((τ.sign : Int) : Real) *
            ∏ j, strictStep (u j) ((τ • b) j)) := by
      rw [Finset.sum_mul]
    _ = splitDet q x a b *
          (∑ σ : Equiv.Perm (Fin m),
            ((σ.sign : Int) : Real) *
              ∏ j, strictStep ((σ • a) j) (s j)) *
        (∑ τ : Equiv.Perm (Fin m),
          ((τ.sign : Int) : Real) *
            ∏ j, strictStep (u j) ((τ • b) j)) := by
      congr 1
      rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro σ
      ring
    _ = _ := by rw [sum_perm_leftSteps, sum_perm_rightSteps]

/-! ## Exact ordered Volterra identity -/

/-- The paper's ordered Volterra integrand on the two ordered chambers. -/
def volterraIntegrand {m : Nat} (q : Nat)
    (x : Fin (2 * m) → Real) (s u : Fin m → Real)
    (z : (Fin m → Real) × (Fin m → Real)) : Real :=
  splitDet q x z.1 z.2 * leftStepDet z.1 s * rightStepDet u z.2

theorem labelledVolterraDet_prod_integrable {m : Nat} (q : Nat)
    (x : Fin (2 * m) → Real) (s u : Fin m → Real) :
    Integrable
      (fun z : (Fin m → Real) × (Fin m → Real) ↦
        labelledVolterraDet q x s u z.1 z.2)
      ((tupleVolume m).prod (tupleVolume m)) := by
  let e := MeasurableEquiv.sumPiEquivProdPi
    (fun _ : Fin m ⊕ Fin m ↦ Real)
  let F : (Fin m → Real) × (Fin m → Real) → Real :=
    fun z ↦ labelledVolterraDet q x s u z.1 z.2
  have hcombined := volterraLabelledDet_integrable q x s u
  have hcomp : Integrable (F ∘ e)
      (Measure.pi fun _ : Fin m ⊕ Fin m ↦ (volume : Measure Real)) := by
    apply hcombined.congr
    filter_upwards [] with z
    exact volterraColumnKernel_sumPi q x s u z
  exact ((measurePreserving_sumPiEquivProdPi
    (fun _ : Fin m ⊕ Fin m ↦ (volume : Measure Real))).integrable_comp_emb
      e.measurableEmbedding).mp hcomp

/-- The full labelled integral equals the ordered double-chamber integral
after the two independent antisymmetrizations.  No factorial occurs. -/
theorem integral_labelled_eq_ordered_volterra {m : Nat} (q : Nat)
    (x : Fin (2 * m) → Real) (s u : Fin m → Real) :
    (∫ z : (Fin m → Real) × (Fin m → Real),
        labelledVolterraDet q x s u z.1 z.2
        ∂((tupleVolume m).prod (tupleVolume m))) =
      ∫ z in orderedChamber m ×ˢ orderedChamber m,
        volterraIntegrand q x s u z
        ∂((tupleVolume m).prod (tupleVolume m)) := by
  let F : (Fin m → Real) × (Fin m → Real) → Real :=
    fun z ↦ labelledVolterraDet q x s u z.1 z.2
  have hF : Integrable F ((tupleVolume m).prod (tupleVolume m)) :=
    labelledVolterraDet_prod_integrable q x s u
  calc
    (∫ z : (Fin m → Real) × (Fin m → Real),
        labelledVolterraDet q x s u z.1 z.2
        ∂((tupleVolume m).prod (tupleVolume m))) =
        ∑' g : Equiv.Perm (Fin m) × Equiv.Perm (Fin m),
          ∫ z in orderedChamber m ×ˢ orderedChamber m,
            F (g • z) ∂((tupleVolume m).prod (tupleVolume m)) :=
      (pairedOrderedChamber_isFundamentalDomain m).integral_eq_tsum'' F hF
    _ = ∑ g : Equiv.Perm (Fin m) × Equiv.Perm (Fin m),
          ∫ z in orderedChamber m ×ˢ orderedChamber m,
            F (g • z) ∂((tupleVolume m).prod (tupleVolume m)) := by
      rw [tsum_fintype]
    _ = ∫ z in orderedChamber m ×ˢ orderedChamber m,
          ∑ g : Equiv.Perm (Fin m) × Equiv.Perm (Fin m), F (g • z)
          ∂((tupleVolume m).prod (tupleVolume m)) := by
      symm
      rw [integral_finsetSum Finset.univ]
      intro g hg
      exact ((pairTuplePerm_measurePreserving g).integrable_comp_of_integrable hF).integrableOn
    _ = ∫ z in orderedChamber m ×ˢ orderedChamber m,
        volterraIntegrand q x s u z
        ∂((tupleVolume m).prod (tupleVolume m)) := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact sum_pairPerm_labelledVolterraDet q x s u z.1 z.2

/-- Exact arbitrary-size Volterra recurrence in successor form.  The
coefficient is exactly `(q+1)^(2m)` and there is no factorial. -/
theorem splitDet_volterra_succ {m : Nat} (q : Nat)
    (x : Fin (2 * m) → Real) (s u : Fin m → Real) :
    splitDet (q + 1) x s u =
      (q + 1 : Real) ^ (2 * m) *
        ∫ z in orderedChamber m ×ˢ orderedChamber m,
          volterraIntegrand q x s u z
          ∂((tupleVolume m).prod (tupleVolume m)) := by
  have hordered := integral_labelled_eq_ordered_volterra q x s u
  have hlabelled := integral_labelledVolterraDet q x s u
  have hI :
      (∫ z in orderedChamber m ×ˢ orderedChamber m,
          volterraIntegrand q x s u z
          ∂((tupleVolume m).prod (tupleVolume m))) =
        ((q + 1 : Real)⁻¹) ^ (2 * m) * splitDet (q + 1) x s u :=
    hordered.symm.trans hlabelled
  rw [hI]
  rw [← mul_assoc, ← mul_pow]
  have hc : (q + 1 : Real) ≠ 0 := by positivity
  rw [mul_inv_cancel₀ hc, one_pow, one_mul]

/-- Paper-indexed exact Volterra recurrence for every `p≥1`. -/
theorem splitDet_volterra {m p : Nat} (hp : 1 ≤ p)
    (x : Fin (2 * m) → Real) (s u : Fin m → Real) :
    splitDet p x s u =
      (p : Real) ^ (2 * m) *
        ∫ z in orderedChamber m ×ˢ orderedChamber m,
          volterraIntegrand (p - 1) x s u z
          ∂((tupleVolume m).prod (tupleVolume m)) := by
  have hp' : p - 1 + 1 = p := Nat.sub_add_cancel hp
  have hpR : ((p - 1 : Nat) : Real) + 1 = (p : Real) := by exact_mod_cast hp'
  rw [← hpR]
  simpa only [hp'] using splitDet_volterra_succ (p - 1) x s u

/-! ## Positivity propagation -/

/-- On the common nonzero support of the two step determinants, the ordered
variables remain paired: `a_i<s_i<u_i<b_i`. -/
theorem volterraIntegrand_nonnegative_of_paired {m q : Nat}
    {x : Fin (2 * m) → Real} {s u a b : Fin m → Real}
    (hSplit : PairedSplitNonnegative q x)
    (hs : StrictMono s) (hu : StrictMono u) (hsu : Paired s u)
    (ha : StrictMono a) (hb : StrictMono b) :
    0 ≤ volterraIntegrand q x s u (a, b) := by
  by_cases hleft : leftStepDet a s = 0
  · rw [volterraIntegrand, hleft, mul_zero, zero_mul]
  by_cases hright : rightStepDet u b = 0
  · rw [volterraIntegrand, hright, mul_zero]
  have has : ∀ i, a i < s i := leftStepDet_support ha hs hleft
  have hub : ∀ i, u i < b i := rightStepDet_support hu hb hright
  have hab : Paired a b := by
    intro i
    exact (has i).trans ((hsu i).trans (hub i))
  have hdet : 0 ≤ splitDet q x a b := hSplit a b ha hb hab
  have hleft_nonneg : 0 ≤ leftStepDet a s := leftStepDet_nonnegative ha hs
  have hright_nonneg : 0 ≤ rightStepDet u b := rightStepDet_nonnegative hu hb
  exact mul_nonneg (mul_nonneg hdet hleft_nonneg) hright_nonneg

/-- One exact Volterra lift propagates paired split nonnegativity from degree
`p` to degree `p+1`. -/
theorem pairedSplitNonnegative_succ {m p : Nat}
    {x : Fin (2 * m) → Real} :
    PairedSplitNonnegative p x → PairedSplitNonnegative (p + 1) x := by
  intro hSplit s u hs hu hsu
  rw [splitDet_volterra_succ]
  apply mul_nonneg (pow_nonneg (by positivity) _)
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem
    ((measurableSet_orderedChamber m).prod (measurableSet_orderedChamber m))] with z hz
  exact volterraIntegrand_nonnegative_of_paired hSplit hs hu hsu hz.1 hz.2

/-- Iterating the exact recurrence propagates any established base degree to
every higher degree. -/
theorem pairedSplitNonnegative_of_base {m base r : Nat}
    {x : Fin (2 * m) → Real}
    (hbase : PairedSplitNonnegative base x) (h : base ≤ r) :
    PairedSplitNonnegative r x := by
  exact Nat.le_induction hbase
    (fun p hp ih ↦ pairedSplitNonnegative_succ (m := m) (p := p) (x := x) ih) r h

end

end ColomboGeneralK2.Odd
