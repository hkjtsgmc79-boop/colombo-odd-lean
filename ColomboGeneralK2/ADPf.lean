import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring

/-!
# Anti-diagonal Pfaffian feasibility gate

This file contains the first local identities needed by the Colombo `k = 2`
formalization.  Every theorem here has a checked proof and introduces no new
logical assumptions.
-/

namespace ColomboGeneralK2

variable {R : Type*} [CommRing R]

/--
A small, self-contained recursive Pfaffian.  The natural-number argument is
fuel; `localPf` below supplies a sufficient amount, namely the length of the
index list.  This keeps the recursion independent of any general Pfaffian
library; no minimal-fuel claim is intended.
-/
def localPfAux {I : Type*} (A : I → I → R) : Nat → List I → R
  | _, [] => 1
  | 0, _ :: _ => 0
  | n + 1, i :: is =>
      ∑ k : Fin is.length,
        (-1 : R) ^ (k : Nat) * A i (is.get k) * localPfAux A n (is.eraseIdx k)

/-- The local recursive Pfaffian evaluated with sufficient fuel. -/
def localPf {I : Type*} (A : I → I → R) (is : List I) : R :=
  localPfAux A is.length is

/-- The Pfaffian of a `4 x 4` skew matrix, written in its three-term form. -/
def pfFour (A : Fin 4 → Fin 4 → R) : R :=
  A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2

/-- The recursive definition specializes to the standard four-by-four formula. -/
theorem localPf_four (A : Fin 4 → Fin 4 → R) :
    localPf A [0, 1, 2, 3] = pfFour A := by
  simp [localPf, localPfAux, pfFour, Fin.sum_univ_succ]
  ring

/-- The polarization term in `pfFour (A + B)`. -/
def pfCross (A B : Fin 4 → Fin 4 → R) : R :=
  A 0 1 * B 2 3 + B 0 1 * A 2 3
    - A 0 2 * B 1 3 - B 0 2 * A 1 3
    + A 0 3 * B 1 2 + B 0 3 * A 1 2

theorem pfFour_add (A B : Fin 4 → Fin 4 → R) :
    pfFour (fun i j ↦ A i j + B i j) = pfFour A + pfFour B + pfCross A B := by
  simp only [pfFour, pfCross]
  ring

theorem pfCross_add_right (A B C : Fin 4 → Fin 4 → R) :
    pfCross A (fun i j ↦ B i j + C i j) = pfCross A B + pfCross A C := by
  simp only [pfCross]
  ring

section AntiDiagonal

variable {I : Type*}

/-- The decomposable two-form formed by the two columns belonging to one pair. -/
def wedgeEntry (Z : I → Fin 4 → Fin 2 → R) (t : I) (i j : Fin 4) : R :=
  Z t i 0 * Z t j 1 - Z t i 1 * Z t j 0

theorem wedgeEntry_swap (Z : I → Fin 4 → Fin 2 → R) (t : I) (i j : Fin 4) :
    wedgeEntry Z t j i = -wedgeEntry Z t i j := by
  simp only [wedgeEntry]
  ring

/-- One weighted rank-two skew summand in `Z C_w Zᵀ`. -/
def weightedPairMatrix (Z : I → Fin 4 → Fin 2 → R) (w : I → R) (t : I) :
    Fin 4 → Fin 4 → R :=
  fun i j ↦ w t * wedgeEntry Z t i j

/-- Pull back a finite list of anti-diagonal `2 x 2` blocks. -/
def pullbackList (Z : I → Fin 4 → Fin 2 → R) (w : I → R) :
    List I → (Fin 4 → Fin 4 → R)
  | [] => 0
  | t :: ts => fun i j ↦ weightedPairMatrix Z w t i j + pullbackList Z w ts i j

/--
The `4 x 4` minor using, in order, the two columns in pair `t` and the two
columns in pair `u`.  The displayed expression is the two-form expansion of
that determinant.
-/
def pairMinor (Z : I → Fin 4 → Fin 2 → R) (t u : I) : R :=
  wedgeEntry Z t 0 1 * wedgeEntry Z u 2 3
    + wedgeEntry Z u 0 1 * wedgeEntry Z t 2 3
    - wedgeEntry Z t 0 2 * wedgeEntry Z u 1 3
    - wedgeEntry Z u 0 2 * wedgeEntry Z t 1 3
    + wedgeEntry Z t 0 3 * wedgeEntry Z u 1 2
    + wedgeEntry Z u 0 3 * wedgeEntry Z t 1 2

theorem pairMinor_swap (Z : I → Fin 4 → Fin 2 → R) (t u : I) :
    pairMinor Z u t = pairMinor Z t u := by
  simp only [pairMinor]
  ring

theorem pairMinor_self (Z : I → Fin 4 → Fin 2 → R) (t : I) :
    pairMinor Z t t = 0 := by
  simp only [pairMinor, wedgeEntry]
  ring

/-- Sum of the weighted expanded minors indexed by two positions in a list. -/
def pairMinorSum (Z : I → Fin 4 → Fin 2 → R) (w : I → R) : List I → R
  | [] => 0
  | t :: ts =>
      (ts.map fun u ↦ w t * w u * pairMinor Z t u).sum + pairMinorSum Z w ts

/-- The actual `4 x 4` matrix whose columns are `L_t, R_t, L_u, R_u`. -/
def pairMatrix (Z : I → Fin 4 → Fin 2 → R) (t u : I) : Matrix (Fin 4) (Fin 4) R :=
  ![![Z t 0 0, Z t 0 1, Z u 0 0, Z u 0 1],
    ![Z t 1 0, Z t 1 1, Z u 1 0, Z u 1 1],
    ![Z t 2 0, Z t 2 1, Z u 2 0, Z u 2 1],
    ![Z t 3 0, Z t 3 1, Z u 3 0, Z u 3 1]]

/-- `pairMinor` is the genuine determinant of the selected four columns. -/
theorem pairMinor_eq_det (Z : I → Fin 4 → Fin 2 → R) (t u : I) :
    pairMinor Z t u = (pairMatrix Z t u).det := by
  have h12 : Fin.succAbove (1 : Fin 4) (2 : Fin 3) = (3 : Fin 4) := by decide
  have h22 : Fin.succAbove (2 : Fin 4) (2 : Fin 3) = (3 : Fin 4) := by decide
  have h32 : Fin.succAbove (3 : Fin 4) (2 : Fin 3) = (2 : Fin 4) := by decide
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, pairMatrix, pairMinor, wedgeEntry,
    h12, h22, h32]
  ring

/-- Sum of the actual determinants selected by two positions in a list. -/
def pairDetSum (Z : I → Fin 4 → Fin 2 → R) (w : I → R) : List I → R
  | [] => 0
  | t :: ts =>
      (ts.map fun u ↦ w t * w u * (pairMatrix Z t u).det).sum + pairDetSum Z w ts

theorem pairMinorSum_eq_pairDetSum (Z : I → Fin 4 → Fin 2 → R) (w : I → R)
    (ts : List I) : pairMinorSum Z w ts = pairDetSum Z w ts := by
  induction ts with
  | nil => simp [pairMinorSum, pairDetSum]
  | cons t ts ih =>
      simp [pairMinorSum, pairDetSum, pairMinor_eq_det, ih]

theorem pfFour_weightedPair (Z : I → Fin 4 → Fin 2 → R) (w : I → R) (t : I) :
    pfFour (weightedPairMatrix Z w t) = 0 := by
  simp only [pfFour, weightedPairMatrix, wedgeEntry]
  ring

theorem pfCross_weightedPair (Z : I → Fin 4 → Fin 2 → R) (w : I → R)
    (t u : I) :
    pfCross (weightedPairMatrix Z w t) (weightedPairMatrix Z w u) =
      w t * w u * pairMinor Z t u := by
  simp only [pfCross, weightedPairMatrix, pairMinor]
  ring

theorem pfCross_weighted_pullback (Z : I → Fin 4 → Fin 2 → R) (w : I → R)
    (t : I) (ts : List I) :
    pfCross (weightedPairMatrix Z w t) (pullbackList Z w ts) =
      (ts.map fun u ↦ w t * w u * pairMinor Z t u).sum := by
  induction ts with
  | nil => simp [pullbackList, pfCross]
  | cons u us ih =>
      simp only [pullbackList, List.map_cons, List.sum_cons]
      rw [pfCross_add_right, pfCross_weightedPair, ih]

/--
The `4 x 2s` anti-diagonal minor-summation identity (`AD-MS`), first in a
list-indexed form.  Each two-element set of positions contributes exactly
once, through `pairMinorSum`.
-/
theorem pfFour_pullback_list (Z : I → Fin 4 → Fin 2 → R) (w : I → R)
    (ts : List I) :
    pfFour (pullbackList Z w ts) = pairMinorSum Z w ts := by
  induction ts with
  | nil => simp [pullbackList, pairMinorSum, pfFour]
  | cons t ts ih =>
      simp only [pullbackList, pairMinorSum]
      rw [pfFour_add, pfFour_weightedPair, pfCross_weighted_pullback, ih]
      ring

/-- `AD-MS` with the right-hand side expressed as genuine matrix determinants. -/
theorem pfFour_pullback_det_list (Z : I → Fin 4 → Fin 2 → R) (w : I → R)
    (ts : List I) :
    pfFour (pullbackList Z w ts) = pairDetSum Z w ts := by
  rw [pfFour_pullback_list, pairMinorSum_eq_pairDetSum]

/-- `AD-MS` for an arbitrary number `s` of anti-diagonal column pairs. -/
theorem pfFour_pullback_fin {s : Nat} (Z : Fin s → Fin 4 → Fin 2 → R)
    (w : Fin s → R) :
    pfFour (pullbackList Z w (List.ofFn fun t ↦ t)) =
      pairDetSum Z w (List.ofFn fun t ↦ t) :=
  pfFour_pullback_det_list Z w _

/-- The same `4 x 2s` identity stated for the local recursive Pfaffian. -/
theorem localPf_pullback_fin {s : Nat} (Z : Fin s → Fin 4 → Fin 2 → R)
    (w : Fin s → R) :
    localPf (pullbackList Z w (List.ofFn fun t ↦ t)) [0, 1, 2, 3] =
      pairDetSum Z w (List.ofFn fun t ↦ t) := by
  rw [localPf_four, pfFour_pullback_fin]

end AntiDiagonal

end ColomboGeneralK2
