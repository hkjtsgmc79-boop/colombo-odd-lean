import ColomboGeneralK2.OddTwoFanWindows
import ColomboGeneralK2.OddPlucker
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Topology.Instances.Matrix

/-!
# The two-sided Desnanot--Jacobi neighbourhood of a fan window

The five smaller windows below are not extra data: they are the canonical
four one-row/one-column deletions and their common middle deletion.  All
indices are zero based.
-/

namespace ColomboGeneralK2.Odd

noncomputable section

open Matrix Polynomial
open ColomboGeneralK2.OddDesnanotJacobi
open ColomboGeneralK2.OddPlucker

namespace OddDesnanotJacobi

/-- Desnanot--Jacobi for real bordered matrices, with no nonsingularity
assumption on the middle block.  We perturb the middle block by `t I`.  Its
determinant is a nonzero polynomial in `t`, so the explicit injective sequence
`1/(k+1)` avoids its roots eventually; continuity then removes the
perturbation. -/
theorem desnanot_jacobi_border_real {n : Nat}
    (A : Matrix (Fin 2) (Fin 2) ℝ)
    (B : Matrix (Fin 2) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin 2) ℝ)
    (D : Matrix (Fin n) (Fin n) ℝ) :
    (Matrix.fromBlocks A B C D).det * D.det =
      (border (A 0 0) (B 0) (fun i ↦ C i 0) D).det *
          (border (A 1 1) (B 1) (fun i ↦ C i 1) D).det -
        (border (A 0 1) (B 0) (fun i ↦ C i 1) D).det *
          (border (A 1 0) (B 1) (fun i ↦ C i 0) D).det := by
  let P : ℝ[X] :=
    (Polynomial.X : ℝ[X]) • (1 : Matrix (Fin n) (Fin n) ℝ[X]) +
      D.map Polynomial.C |>.det
  have hP : P ≠ 0 := by
    intro hzero
    have hlead := Polynomial.leadingCoeff_det_X_one_add_C D
    change P.leadingCoeff = 1 at hlead
    rw [hzero] at hlead
    simp at hlead
  let ε : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  have hε : Filter.Tendsto ε Filter.atTop (nhds 0) := by
    simpa only [ε] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 1))
          Filter.atTop (nhds 0))
  have hεinj : Function.Injective ε := by
    intro k l hkl
    dsimp only [ε] at hkl
    have hcast : (k : ℝ) = (l : ℝ) := by
      have hden := eq_of_one_div_eq_one_div hkl
      linarith
    exact_mod_cast hcast
  have hnonroot : ∀ᶠ k in Filter.atTop, ¬ P.IsRoot (ε k) := by
    have hcof : ∀ᶠ t : ℝ in Filter.cofinite, ¬ P.IsRoot t :=
      Polynomial.eventually_cofinite_not_isRoot hP
    exact (by
      rw [← Nat.cofinite_eq_atTop]
      exact hεinj.tendsto_cofinite.eventually hcof)
  let Dε : ℕ → Matrix (Fin n) (Fin n) ℝ :=
    fun k ↦ D + ε k • (1 : Matrix (Fin n) (Fin n) ℝ)
  have hdetDε : ∀ᶠ k in Filter.atTop, (Dε k).det ≠ 0 := by
    filter_upwards [hnonroot] with k hk
    intro hdet
    apply hk
    rw [Polynomial.IsRoot.def]
    change (Polynomial.evalRingHom (ε k)) P = 0
    have heval : (Polynomial.evalRingHom (ε k)) P = (Dε k).det := by
      dsimp only [P, Dε]
      change (Polynomial.evalRingHom (ε k))
          ((Polynomial.X : ℝ[X]) • (1 : Matrix (Fin n) (Fin n) ℝ[X]) +
            D.map Polynomial.C |>.det) = _
      rw [RingHom.map_det]
      congr 1
      ext i j
      by_cases hij : i = j
      · subst j
        simp [add_comm]
      · simp [hij]
    exact heval.trans hdet
  let lhs : Matrix (Fin n) (Fin n) ℝ → ℝ := fun E ↦
    (Matrix.fromBlocks A B C E).det * E.det
  let rhs : Matrix (Fin n) (Fin n) ℝ → ℝ := fun E ↦
    (border (A 0 0) (B 0) (fun i ↦ C i 0) E).det *
        (border (A 1 1) (B 1) (fun i ↦ C i 1) E).det -
      (border (A 0 1) (B 0) (fun i ↦ C i 1) E).det *
        (border (A 1 0) (B 1) (fun i ↦ C i 0) E).det
  have heq : ∀ᶠ k in Filter.atTop, lhs (Dε k) = rhs (Dε k) := by
    filter_upwards [hdetDε] with k hk
    exact ColomboGeneralK2.OddDesnanotJacobi.desnanot_jacobi_border_field
      A B C (Dε k) hk
  have hDε : Filter.Tendsto Dε Filter.atTop (nhds D) := by
    change Filter.Tendsto
      (fun k i j ↦ (D + ε k • (1 : Matrix (Fin n) (Fin n) ℝ)) i j)
      Filter.atTop (nhds (fun i j ↦ D i j))
    rw [tendsto_pi_nhds]
    intro i
    rw [tendsto_pi_nhds]
    intro j
    by_cases hij : i = j
    · subst j
      simpa [Matrix.one_apply] using tendsto_const_nhds.add hε
    · simp [hij]
  have hlhs : Filter.Tendsto (fun k ↦ lhs (Dε k)) Filter.atTop (nhds (lhs D)) := by
    apply (show Continuous lhs by
      dsimp only [lhs]
      simp only [Matrix.det_apply]
      fun_prop).continuousAt.tendsto.comp hDε
  have hrhs : Filter.Tendsto (fun k ↦ rhs (Dε k)) Filter.atTop (nhds (rhs D)) := by
    apply (show Continuous rhs by
      dsimp only [rhs, border]
      simp only [Matrix.det_apply]
      fun_prop).continuousAt.tendsto.comp hDε
  have hlhs' : Filter.Tendsto (fun k ↦ rhs (Dε k)) Filter.atTop (nhds (lhs D)) :=
    hlhs.congr' heq
  exact tendsto_nhds_unique hlhs' hrhs

/-- The increasing inclusion which deletes the first index. -/
private def bottomEmb (n : Nat) : Fin (n + 1) ↪o Fin (n + 2) :=
  Fin.succOrderEmb (n + 1)

/-- The bordered-block order with the final boundary index displayed first. -/
private def lastSingleFrameIndex (n : Nat) : Fin 1 ⊕ Fin n → Fin (n + 2) :=
  Sum.elim (fun _ ↦ Fin.last (n + 1)) (middleEmb n)

/-- Reindexing `last, middle` into natural order contributes the cyclic
permutation `qLastSmall`. -/
private theorem lastSingleFrameIndex_equiv (n : Nat) (i : Fin (n + 1)) :
    lastSingleFrameIndex n ((singleSumEquiv n).symm i) =
      bottomEmb n (qLastSmall n i) := by
  rcases h : (singleSumEquiv n).symm i with x | x
  · have hi : i = singleSumEquiv n (Sum.inl x) := by rw [← h]; simp
    subst i
    fin_cases x
    have harg : singleSumEquiv n (Sum.inl ⟨0, by omega⟩) = (0 : Fin (n + 1)) := by
      apply Fin.ext
      simp [singleSumEquiv]
    rw [harg]
    change Fin.last (n + 1) = Fin.succ (frontPerm (Fin.last n) 0)
    rw [frontPerm_zero]
    rfl
  · have hi : i = singleSumEquiv n (Sum.inr x) := by rw [← h]; simp
    subst i
    have harg : singleSumEquiv n (Sum.inr x) = x.succ := by
      apply Fin.ext
      simp [singleSumEquiv]
    rw [harg]
    change middleEmb n x = Fin.succ (frontPerm (Fin.last n) x.succ)
    rw [frontPerm_succ]
    rw [Fin.succAbove_of_castSucc_lt]
    · rfl
    · exact Fin.castSucc_lt_last x

/-- Naturally ordered Desnanot--Jacobi on an arbitrary real `(n+2)` square
matrix.  This is the canonical row/column form used by fan windows. -/
private theorem desnanot_jacobi_fin_real {n : Nat}
    (X : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) :
    X.det * (X.submatrix (middleEmb n) (middleEmb n)).det =
      (X.submatrix (topEmb n) (topEmb n)).det *
          (X.submatrix (bottomEmb n) (bottomEmb n)).det -
        (X.submatrix (topEmb n) (bottomEmb n)).det *
          (X.submatrix (bottomEmb n) (topEmb n)).det := by
  let A : Matrix (Fin 2) (Fin 2) ℝ :=
    X.submatrix (rowSpecial n) (rowSpecial n)
  let B : Matrix (Fin 2) (Fin n) ℝ :=
    X.submatrix (rowSpecial n) (middleEmb n)
  let C : Matrix (Fin n) (Fin 2) ℝ :=
    X.submatrix (middleEmb n) (rowSpecial n)
  let D : Matrix (Fin n) (Fin n) ℝ :=
    X.submatrix (middleEmb n) (middleEmb n)
  have hmain := desnanot_jacobi_border_real A B C D
  have hframe : Matrix.fromBlocks A B C D =
      X.submatrix (pairRowFrameIndex n) (pairRowFrameIndex n) := by
    ext u v
    rcases u with u | u <;> rcases v with v | v
    · fin_cases u <;> fin_cases v <;>
        simp [A, pairRowFrameIndex, rowSpecial]
    · fin_cases u <;>
        simp [B, pairRowFrameIndex, rowSpecial]
    · fin_cases v <;>
        simp [C, pairRowFrameIndex, rowSpecial]
    · simp [D, pairRowFrameIndex]
  have hfullMatrix :
      (Matrix.fromBlocks A B C D).submatrix
          (pairSumEquiv n).symm (pairSumEquiv n).symm =
        X.submatrix (qRow n) (qRow n) := by
    rw [hframe]
    ext i j
    simp only [Matrix.submatrix_apply]
    rw [pairRowFrameIndex_equiv, pairRowFrameIndex_equiv]
  have hfullDet : (Matrix.fromBlocks A B C D).det = X.det := by
    rw [← Matrix.det_submatrix_equiv_self (pairSumEquiv n).symm,
      hfullMatrix, Matrix.det_submatrix_equiv_self]
  have h00frame : border (A 0 0) (B 0) (fun i ↦ C i 0) D =
      X.submatrix (singleRowFrameIndex n) (singleRowFrameIndex n) := by
    ext u v
    rcases u with u | u <;> rcases v with v | v
    · fin_cases u
      fin_cases v
      simp [A, border, singleRowFrameIndex, rowSpecial]
    · fin_cases u
      simp [B, border, singleRowFrameIndex, rowSpecial]
    · fin_cases v
      simp [C, border, singleRowFrameIndex, rowSpecial]
    · simp [D, border, singleRowFrameIndex]
  have h11frame : border (A 1 1) (B 1) (fun i ↦ C i 1) D =
      X.submatrix (lastSingleFrameIndex n) (lastSingleFrameIndex n) := by
    ext u v
    rcases u with u | u <;> rcases v with v | v
    · fin_cases u
      fin_cases v
      simp [A, border, lastSingleFrameIndex, rowSpecial]
    · fin_cases u
      simp [B, border, lastSingleFrameIndex, rowSpecial]
    · fin_cases v
      simp [C, border, lastSingleFrameIndex, rowSpecial]
    · simp [D, border, lastSingleFrameIndex]
  have h01frame : border (A 0 1) (B 0) (fun i ↦ C i 1) D =
      X.submatrix (singleRowFrameIndex n) (lastSingleFrameIndex n) := by
    ext u v
    rcases u with u | u <;> rcases v with v | v
    · fin_cases u
      fin_cases v
      simp [A, border, singleRowFrameIndex, lastSingleFrameIndex, rowSpecial]
    · fin_cases u
      simp [B, border, singleRowFrameIndex, lastSingleFrameIndex, rowSpecial]
    · fin_cases v
      simp [C, border, singleRowFrameIndex, lastSingleFrameIndex, rowSpecial]
    · simp [D, border, singleRowFrameIndex, lastSingleFrameIndex]
  have h10frame : border (A 1 0) (B 1) (fun i ↦ C i 0) D =
      X.submatrix (lastSingleFrameIndex n) (singleRowFrameIndex n) := by
    ext u v
    rcases u with u | u <;> rcases v with v | v
    · fin_cases u
      fin_cases v
      simp [A, border, singleRowFrameIndex, lastSingleFrameIndex, rowSpecial]
    · fin_cases u
      simp [B, border, singleRowFrameIndex, lastSingleFrameIndex, rowSpecial]
    · fin_cases v
      simp [C, border, singleRowFrameIndex, lastSingleFrameIndex, rowSpecial]
    · simp [D, border, singleRowFrameIndex, lastSingleFrameIndex]
  have h00Matrix :
      (border (A 0 0) (B 0) (fun i ↦ C i 0) D).submatrix
          (singleSumEquiv n).symm (singleSumEquiv n).symm =
        X.submatrix (topEmb n) (topEmb n) := by
    rw [h00frame]
    ext i j
    simp only [Matrix.submatrix_apply]
    rw [singleRowFrameIndex_equiv, singleRowFrameIndex_equiv]
  have h11Matrix :
      (border (A 1 1) (B 1) (fun i ↦ C i 1) D).submatrix
          (singleSumEquiv n).symm (singleSumEquiv n).symm =
        (X.submatrix (bottomEmb n) (bottomEmb n)).submatrix
          (qLastSmall n) (qLastSmall n) := by
    rw [h11frame]
    ext i j
    simp only [Matrix.submatrix_apply]
    rw [lastSingleFrameIndex_equiv, lastSingleFrameIndex_equiv]
  have h01Matrix :
      (border (A 0 1) (B 0) (fun i ↦ C i 1) D).submatrix
          (singleSumEquiv n).symm (singleSumEquiv n).symm =
        (X.submatrix (topEmb n) (bottomEmb n)).submatrix id (qLastSmall n) := by
    rw [h01frame]
    ext i j
    simp only [Matrix.submatrix_apply, id_eq]
    rw [singleRowFrameIndex_equiv, lastSingleFrameIndex_equiv]
  have h10Matrix :
      (border (A 1 0) (B 1) (fun i ↦ C i 0) D).submatrix
          (singleSumEquiv n).symm (singleSumEquiv n).symm =
        (X.submatrix (bottomEmb n) (topEmb n)).submatrix (qLastSmall n) id := by
    rw [h10frame]
    ext i j
    simp only [Matrix.submatrix_apply, id_eq]
    rw [lastSingleFrameIndex_equiv, singleRowFrameIndex_equiv]
  have h00Det : (border (A 0 0) (B 0) (fun i ↦ C i 0) D).det =
      (X.submatrix (topEmb n) (topEmb n)).det := by
    rw [← Matrix.det_submatrix_equiv_self (singleSumEquiv n).symm, h00Matrix]
  have h11Det : (border (A 1 1) (B 1) (fun i ↦ C i 1) D).det =
      (X.submatrix (bottomEmb n) (bottomEmb n)).det := by
    rw [← Matrix.det_submatrix_equiv_self (singleSumEquiv n).symm,
      h11Matrix, Matrix.det_submatrix_equiv_self]
  have h01DetRaw : (border (A 0 1) (B 0) (fun i ↦ C i 1) D).det =
      ((qLastSmall n).sign : ℝ) *
        (X.submatrix (topEmb n) (bottomEmb n)).det := by
    rw [← Matrix.det_submatrix_equiv_self (singleSumEquiv n).symm,
      h01Matrix, Matrix.det_permute']
  have h10DetRaw : (border (A 1 0) (B 1) (fun i ↦ C i 0) D).det =
      ((qLastSmall n).sign : ℝ) *
        (X.submatrix (bottomEmb n) (topEmb n)).det := by
    rw [← Matrix.det_submatrix_equiv_self (singleSumEquiv n).symm,
      h10Matrix, Matrix.det_permute]
  let s : ℝ := (-1 : ℝ) ^ n
  have hs : s * s = 1 := by
    dsimp [s]
    rw [← mul_pow]
    norm_num
  have h01Det : (border (A 0 1) (B 0) (fun i ↦ C i 1) D).det =
      s * (X.submatrix (topEmb n) (bottomEmb n)).det := by
    simpa [s, sign_qLastSmall] using h01DetRaw
  have h10Det : (border (A 1 0) (B 1) (fun i ↦ C i 0) D).det =
      s * (X.submatrix (bottomEmb n) (topEmb n)).det := by
    simpa [s, sign_qLastSmall] using h10DetRaw
  rw [hfullDet, h00Det, h11Det, h01Det, h10Det] at hmain
  dsimp only [D] at hmain
  calc
    X.det * (X.submatrix (middleEmb n) (middleEmb n)).det =
        (X.submatrix (topEmb n) (topEmb n)).det *
            (X.submatrix (bottomEmb n) (bottomEmb n)).det -
          (s * (X.submatrix (topEmb n) (bottomEmb n)).det) *
            (s * (X.submatrix (bottomEmb n) (topEmb n)).det) := hmain
    _ = (X.submatrix (topEmb n) (topEmb n)).det *
            (X.submatrix (bottomEmb n) (bottomEmb n)).det -
          (X.submatrix (topEmb n) (bottomEmb n)).det *
            (X.submatrix (bottomEmb n) (topEmb n)).det := by
      rw [show
        (s * (X.submatrix (topEmb n) (bottomEmb n)).det) *
            (s * (X.submatrix (bottomEmb n) (topEmb n)).det) =
          (s * s) *
            ((X.submatrix (topEmb n) (bottomEmb n)).det *
              (X.submatrix (bottomEmb n) (topEmb n)).det) by ring, hs, one_mul]

end OddDesnanotJacobi

namespace FanMinorWindow

variable {m : Nat} {D : TwoFanData m}

/-- A fan window with a nonempty left suffix and nonempty right block. -/
structure IsTwoSided (W : FanMinorWindow D) : Prop where
  ell_pos : 0 < W.ell
  b_pos : 0 < W.b

/-- Delete the bottom row and the final (right) column. -/
def tl (W : FanMinorWindow D) (hb : 0 < W.b) : FanMinorWindow D where
  ell := W.ell
  c := W.c
  b := W.b - 1
  rho := W.rho
  ell_le := W.ell_le
  cb_le := by
    exact le_trans (Nat.add_le_add_left (Nat.sub_le _ _) _) W.cb_le
  rows_le := by
    have h := W.rows_le
    omega

/-- Delete the top row and the initial (left) column. -/
def br (W : FanMinorWindow D) (hell : 0 < W.ell) : FanMinorWindow D where
  ell := W.ell - 1
  c := W.c
  b := W.b
  rho := W.rho + 1
  ell_le := le_trans (Nat.sub_le _ _) W.ell_le
  cb_le := W.cb_le
  rows_le := by
    have h := W.rows_le
    omega

/-- Delete the bottom row and the initial (left) column. -/
def tr (W : FanMinorWindow D) (hell : 0 < W.ell) : FanMinorWindow D where
  ell := W.ell - 1
  c := W.c
  b := W.b
  rho := W.rho
  ell_le := le_trans (Nat.sub_le _ _) W.ell_le
  cb_le := W.cb_le
  rows_le := by
    have h := W.rows_le
    omega

/-- Delete the top row and the final (right) column. -/
def bl (W : FanMinorWindow D) (hb : 0 < W.b) : FanMinorWindow D where
  ell := W.ell
  c := W.c
  b := W.b - 1
  rho := W.rho + 1
  ell_le := W.ell_le
  cb_le := by
    exact le_trans (Nat.add_le_add_left (Nat.sub_le _ _) _) W.cb_le
  rows_le := by
    have h := W.rows_le
    omega

/-- Delete both boundary rows and both boundary columns. -/
def mid (W : FanMinorWindow D) (hell : 0 < W.ell) (hb : 0 < W.b) :
    FanMinorWindow D where
  ell := W.ell - 1
  c := W.c
  b := W.b - 1
  rho := W.rho + 1
  ell_le := le_trans (Nat.sub_le _ _) W.ell_le
  cb_le := by
    exact le_trans (Nat.add_le_add_left (Nat.sub_le _ _) _) W.cb_le
  rows_le := by
    have h := W.rows_le
    omega

@[simp] theorem tl_params (W : FanMinorWindow D) (hb : 0 < W.b) :
    (W.tl hb).ell = W.ell ∧ (W.tl hb).b = W.b - 1 ∧ (W.tl hb).rho = W.rho :=
  ⟨rfl, rfl, rfl⟩

@[simp] theorem br_params (W : FanMinorWindow D) (hell : 0 < W.ell) :
    (W.br hell).ell = W.ell - 1 ∧ (W.br hell).b = W.b ∧
      (W.br hell).rho = W.rho + 1 :=
  ⟨rfl, rfl, rfl⟩

@[simp] theorem tr_params (W : FanMinorWindow D) (hell : 0 < W.ell) :
    (W.tr hell).ell = W.ell - 1 ∧ (W.tr hell).b = W.b ∧ (W.tr hell).rho = W.rho :=
  ⟨rfl, rfl, rfl⟩

@[simp] theorem bl_params (W : FanMinorWindow D) (hb : 0 < W.b) :
    (W.bl hb).ell = W.ell ∧ (W.bl hb).b = W.b - 1 ∧
      (W.bl hb).rho = W.rho + 1 :=
  ⟨rfl, rfl, rfl⟩

@[simp] theorem mid_params (W : FanMinorWindow D) (hell : 0 < W.ell) (hb : 0 < W.b) :
    (W.mid hell hb).ell = W.ell - 1 ∧ (W.mid hell hb).b = W.b - 1 ∧
      (W.mid hell hb).rho = W.rho + 1 :=
  ⟨rfl, rfl, rfl⟩

/-- Desnanot--Jacobi for the canonical five-neighbourhood of every genuine
two-sided fan window.  No nonvanishing, positivity, total-nonnegativity, or
target identity is assumed. -/
theorem fanMinor_desnanotJacobi (W : FanMinorWindow D)
    (hell : 0 < W.ell) (hb : 0 < W.b) :
    W.fanMinor * (W.mid hell hb).fanMinor =
      (W.tl hb).fanMinor * (W.br hell).fanMinor -
        (W.tr hell).fanMinor * (W.bl hb).fanMinor := by
  let n : Nat := (W.mid hell hb).q
  have hfull : n + 2 = W.q := by
    dsimp [n, q, mid]
    omega
  have htl : n + 1 = (W.tl hb).q := by
    dsimp [n, q, mid, tl]
    omega
  have hbr : n + 1 = (W.br hell).q := by
    dsimp [n, q, mid, br]
    omega
  have htr : n + 1 = (W.tr hell).q := by
    dsimp [n, q, mid, tr]
    omega
  have hbl : n + 1 = (W.bl hb).q := by
    dsimp [n, q, mid, bl]
    omega
  let eFull : Fin (n + 2) ≃ Fin W.q := finCongr hfull
  let eTL : Fin (n + 1) ≃ Fin (W.tl hb).q := finCongr htl
  let eBR : Fin (n + 1) ≃ Fin (W.br hell).q := finCongr hbr
  let eTR : Fin (n + 1) ≃ Fin (W.tr hell).q := finCongr htr
  let eBL : Fin (n + 1) ≃ Fin (W.bl hb).q := finCongr hbl
  have eFull_val (i : Fin (n + 2)) : (eFull i : Nat) = (i : Nat) := by
    exact finCongr_apply_coe hfull i
  have eTL_val (i : Fin (n + 1)) : (eTL i : Nat) = (i : Nat) := by
    exact finCongr_apply_coe htl i
  have eBR_val (i : Fin (n + 1)) : (eBR i : Nat) = (i : Nat) := by
    exact finCongr_apply_coe hbr i
  have eTR_val (i : Fin (n + 1)) : (eTR i : Nat) = (i : Nat) := by
    exact finCongr_apply_coe htr i
  have eBL_val (i : Fin (n + 1)) : (eBL i : Nat) = (i : Nat) := by
    exact finCongr_apply_coe hbl i
  let M := twoFanCoefficientMatrix D
  let X : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
    (M.submatrix W.fanRows W.fanCols).submatrix eFull eFull
  have htopRowsTL (i : Fin (n + 1)) :
      W.fanRows (eFull (topEmb n i)) =
        (W.tl hb).fanRows (eTL i) := by
    apply Fin.ext
    change W.rho + (eFull (topEmb n i) : Nat) =
      (W.tl hb).rho + (eTL i : Nat)
    rw [eFull_val, eTL_val]
    rfl
  have htopRowsTR (i : Fin (n + 1)) :
      W.fanRows (eFull (topEmb n i)) =
        (W.tr hell).fanRows (eTR i) := by
    apply Fin.ext
    change W.rho + (eFull (topEmb n i) : Nat) =
      (W.tr hell).rho + (eTR i : Nat)
    rw [eFull_val, eTR_val]
    rfl
  have hbottomRowsBR (i : Fin (n + 1)) :
      W.fanRows (eFull (OddDesnanotJacobi.bottomEmb n i)) =
        (W.br hell).fanRows (eBR i) := by
    apply Fin.ext
    change W.rho + (eFull (OddDesnanotJacobi.bottomEmb n i) : Nat) =
      (W.br hell).rho + (eBR i : Nat)
    rw [eFull_val, eBR_val]
    change W.rho + ((i : Nat) + 1) = W.rho + 1 + (i : Nat)
    omega
  have hbottomRowsBL (i : Fin (n + 1)) :
      W.fanRows (eFull (OddDesnanotJacobi.bottomEmb n i)) =
        (W.bl hb).fanRows (eBL i) := by
    apply Fin.ext
    change W.rho + (eFull (OddDesnanotJacobi.bottomEmb n i) : Nat) =
      (W.bl hb).rho + (eBL i : Nat)
    rw [eFull_val, eBL_val]
    change W.rho + ((i : Nat) + 1) = W.rho + 1 + (i : Nat)
    omega
  have hmiddleRows (i : Fin n) :
      W.fanRows (eFull (middleEmb n i)) =
        (W.mid hell hb).fanRows i := by
    apply Fin.ext
    change W.rho + (eFull (middleEmb n i) : Nat) =
      (W.mid hell hb).rho + (i : Nat)
    rw [eFull_val]
    change W.rho + ((i : Nat) + 1) = W.rho + 1 + (i : Nat)
    omega
  have htopColsTL (j : Fin (n + 1)) :
      W.fanCols (eFull (topEmb n j)) =
        (W.tl hb).fanCols (eTL j) := by
    apply Fin.ext
    change (fanColValue W (eFull (topEmb n j)) : Nat) =
      (fanColValue (W.tl hb) (eTL j) : Nat)
    have hFullVal : (eFull (topEmb n j) : Nat) = (j : Nat) := by
      rw [eFull_val]
      rfl
    have hSmallVal : (eTL j : Nat) = (j : Nat) := eTL_val j
    by_cases hj : (j : Nat) < W.ell
    · have hjFull : (eFull (topEmb n j) : Nat) < W.ell := by simpa [hFullVal]
      have hjSmall : (eTL j : Nat) < (W.tl hb).ell := by simpa [tl, hSmallVal]
      simp only [fanColValue, dif_pos hjFull, dif_pos hjSmall, Fin.val_mk]
      rw [hFullVal, hSmallVal]
      rfl
    · have hjFull : ¬ (eFull (topEmb n j) : Nat) < W.ell := by
        rw [hFullVal]
        omega
      have hjSmall : ¬ (eTL j : Nat) < (W.tl hb).ell := by
        rw [hSmallVal]
        change ¬ (j : Nat) < W.ell
        exact hj
      simp only [fanColValue, dif_neg hjFull, dif_neg hjSmall, Fin.val_mk]
      rw [hFullVal, hSmallVal]
      rfl
  have htopColsBL (j : Fin (n + 1)) :
      W.fanCols (eFull (topEmb n j)) =
        (W.bl hb).fanCols (eBL j) := by
    apply Fin.ext
    change (fanColValue W (eFull (topEmb n j)) : Nat) =
      (fanColValue (W.bl hb) (eBL j) : Nat)
    have hFullVal : (eFull (topEmb n j) : Nat) = (j : Nat) := by
      rw [eFull_val]
      rfl
    have hSmallVal : (eBL j : Nat) = (j : Nat) := eBL_val j
    by_cases hj : (j : Nat) < W.ell
    · have hjFull : (eFull (topEmb n j) : Nat) < W.ell := by simpa [hFullVal]
      have hjSmall : (eBL j : Nat) < (W.bl hb).ell := by simpa [bl, hSmallVal]
      simp only [fanColValue, dif_pos hjFull, dif_pos hjSmall, Fin.val_mk]
      rw [hFullVal, hSmallVal]
      rfl
    · have hjFull : ¬ (eFull (topEmb n j) : Nat) < W.ell := by
        rw [hFullVal]
        omega
      have hjSmall : ¬ (eBL j : Nat) < (W.bl hb).ell := by
        rw [hSmallVal]
        change ¬ (j : Nat) < W.ell
        exact hj
      simp only [fanColValue, dif_neg hjFull, dif_neg hjSmall, Fin.val_mk]
      rw [hFullVal, hSmallVal]
      rfl
  have hbottomColsBR (j : Fin (n + 1)) :
      W.fanCols (eFull (OddDesnanotJacobi.bottomEmb n j)) =
        (W.br hell).fanCols (eBR j) := by
    apply Fin.ext
    change (fanColValue W (eFull (OddDesnanotJacobi.bottomEmb n j)) : Nat) =
      (fanColValue (W.br hell) (eBR j) : Nat)
    have hFullVal : (eFull (OddDesnanotJacobi.bottomEmb n j) : Nat) =
        (j : Nat) + 1 := by
      rw [eFull_val]
      rfl
    have hSmallVal : (eBR j : Nat) = (j : Nat) := eBR_val j
    by_cases hj : (j : Nat) < W.ell - 1
    · have hjFull : (eFull (OddDesnanotJacobi.bottomEmb n j) : Nat) < W.ell := by
        rw [hFullVal]
        omega
      have hjSmall : (eBR j : Nat) < (W.br hell).ell := by
        rw [hSmallVal]
        change (j : Nat) < W.ell - 1
        exact hj
      simp only [fanColValue, dif_pos hjFull, dif_pos hjSmall, Fin.val_mk]
      rw [hFullVal, hSmallVal]
      change m - W.ell + ((j : Nat) + 1) =
        m - (W.ell - 1) + (j : Nat)
      have := W.ell_le
      omega
    · have hjFull : ¬ (eFull (OddDesnanotJacobi.bottomEmb n j) : Nat) < W.ell := by
        rw [hFullVal]
        omega
      have hjSmall : ¬ (eBR j : Nat) < (W.br hell).ell := by
        rw [hSmallVal]
        change ¬ (j : Nat) < W.ell - 1
        exact hj
      simp only [fanColValue, dif_neg hjFull, dif_neg hjSmall, Fin.val_mk]
      rw [hFullVal, hSmallVal]
      change m + W.c + ((j : Nat) + 1 - W.ell) =
        m + W.c + ((j : Nat) - (W.ell - 1))
      omega
  have hbottomColsTR (j : Fin (n + 1)) :
      W.fanCols (eFull (OddDesnanotJacobi.bottomEmb n j)) =
        (W.tr hell).fanCols (eTR j) := by
    apply Fin.ext
    change (fanColValue W (eFull (OddDesnanotJacobi.bottomEmb n j)) : Nat) =
      (fanColValue (W.tr hell) (eTR j) : Nat)
    have hFullVal : (eFull (OddDesnanotJacobi.bottomEmb n j) : Nat) =
        (j : Nat) + 1 := by
      rw [eFull_val]
      rfl
    have hSmallVal : (eTR j : Nat) = (j : Nat) := eTR_val j
    by_cases hj : (j : Nat) < W.ell - 1
    · have hjFull : (eFull (OddDesnanotJacobi.bottomEmb n j) : Nat) < W.ell := by
        rw [hFullVal]
        omega
      have hjSmall : (eTR j : Nat) < (W.tr hell).ell := by
        rw [hSmallVal]
        change (j : Nat) < W.ell - 1
        exact hj
      simp only [fanColValue, dif_pos hjFull, dif_pos hjSmall, Fin.val_mk]
      rw [hFullVal, hSmallVal]
      change m - W.ell + ((j : Nat) + 1) =
        m - (W.ell - 1) + (j : Nat)
      have := W.ell_le
      omega
    · have hjFull : ¬ (eFull (OddDesnanotJacobi.bottomEmb n j) : Nat) < W.ell := by
        rw [hFullVal]
        omega
      have hjSmall : ¬ (eTR j : Nat) < (W.tr hell).ell := by
        rw [hSmallVal]
        change ¬ (j : Nat) < W.ell - 1
        exact hj
      simp only [fanColValue, dif_neg hjFull, dif_neg hjSmall, Fin.val_mk]
      rw [hFullVal, hSmallVal]
      change m + W.c + ((j : Nat) + 1 - W.ell) =
        m + W.c + ((j : Nat) - (W.ell - 1))
      omega
  have hmiddleCols (j : Fin n) :
      W.fanCols (eFull (middleEmb n j)) =
        (W.mid hell hb).fanCols j := by
    apply Fin.ext
    change (fanColValue W (eFull (middleEmb n j)) : Nat) =
      (fanColValue (W.mid hell hb) j : Nat)
    have hFullVal : (eFull (middleEmb n j) : Nat) = (j : Nat) + 1 := by
      rw [eFull_val]
      rfl
    by_cases hj : (j : Nat) < W.ell - 1
    · have hjFull : (eFull (middleEmb n j) : Nat) < W.ell := by
        rw [hFullVal]
        omega
      have hjSmall : (j : Nat) < (W.mid hell hb).ell := by
        change (j : Nat) < W.ell - 1
        exact hj
      simp only [fanColValue, dif_pos hjFull, dif_pos hjSmall, Fin.val_mk]
      rw [hFullVal]
      change m - W.ell + ((j : Nat) + 1) =
        m - (W.ell - 1) + (j : Nat)
      have := W.ell_le
      omega
    · have hjFull : ¬ (eFull (middleEmb n j) : Nat) < W.ell := by
        rw [hFullVal]
        omega
      have hjSmall : ¬ (j : Nat) < (W.mid hell hb).ell := by
        change ¬ (j : Nat) < W.ell - 1
        exact hj
      simp only [fanColValue, dif_neg hjFull, dif_neg hjSmall, Fin.val_mk]
      rw [hFullVal]
      change m + W.c + ((j : Nat) + 1 - W.ell) =
        m + W.c + ((j : Nat) - (W.ell - 1))
      omega
  have hXdet : X.det = W.fanMinor := by
    dsimp only [X, M, fanMinor]
    rw [Matrix.det_submatrix_equiv_self]
    rfl
  have hmidMatrix :
      X.submatrix (middleEmb n) (middleEmb n) =
        M.submatrix (W.mid hell hb).fanRows (W.mid hell hb).fanCols := by
    ext i j
    simp only [X, Matrix.submatrix_apply]
    rw [hmiddleRows, hmiddleCols]
  have htlMatrix :
      X.submatrix (topEmb n) (topEmb n) =
        (M.submatrix (W.tl hb).fanRows (W.tl hb).fanCols).submatrix eTL eTL := by
    ext i j
    simp only [X, Matrix.submatrix_apply]
    rw [htopRowsTL, htopColsTL]
  have hbrMatrix :
      X.submatrix (OddDesnanotJacobi.bottomEmb n)
          (OddDesnanotJacobi.bottomEmb n) =
        (M.submatrix (W.br hell).fanRows (W.br hell).fanCols).submatrix eBR eBR := by
    ext i j
    simp only [X, Matrix.submatrix_apply]
    rw [hbottomRowsBR, hbottomColsBR]
  have htrMatrix :
      X.submatrix (topEmb n)
          (OddDesnanotJacobi.bottomEmb n) =
        (M.submatrix (W.tr hell).fanRows (W.tr hell).fanCols).submatrix eTR eTR := by
    ext i j
    simp only [X, Matrix.submatrix_apply]
    rw [htopRowsTR, hbottomColsTR]
  have hblMatrix :
      X.submatrix (OddDesnanotJacobi.bottomEmb n)
          (topEmb n) =
        (M.submatrix (W.bl hb).fanRows (W.bl hb).fanCols).submatrix eBL eBL := by
    ext i j
    simp only [X, Matrix.submatrix_apply]
    rw [hbottomRowsBL, htopColsBL]
  have hmidDet : (X.submatrix (middleEmb n) (middleEmb n)).det =
      (W.mid hell hb).fanMinor := by
    rw [hmidMatrix]
    rfl
  have htlDet :
      (X.submatrix (topEmb n)
        (topEmb n)).det = (W.tl hb).fanMinor := by
    rw [htlMatrix, Matrix.det_submatrix_equiv_self]
    rfl
  have hbrDet :
      (X.submatrix (OddDesnanotJacobi.bottomEmb n)
        (OddDesnanotJacobi.bottomEmb n)).det = (W.br hell).fanMinor := by
    rw [hbrMatrix, Matrix.det_submatrix_equiv_self]
    rfl
  have htrDet :
      (X.submatrix (topEmb n)
        (OddDesnanotJacobi.bottomEmb n)).det = (W.tr hell).fanMinor := by
    rw [htrMatrix, Matrix.det_submatrix_equiv_self]
    rfl
  have hblDet :
      (X.submatrix (OddDesnanotJacobi.bottomEmb n)
        (topEmb n)).det = (W.bl hb).fanMinor := by
    rw [hblMatrix, Matrix.det_submatrix_equiv_self]
    rfl
  simpa [hXdet, hmidDet, htlDet, hbrDet, htrDet, hblDet] using
    (OddDesnanotJacobi.desnanot_jacobi_fin_real X)

end FanMinorWindow

end

end ColomboGeneralK2.Odd
