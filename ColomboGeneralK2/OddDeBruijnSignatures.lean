import ColomboGeneralK2.GeneralADMS
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Odd Colombo Beta--de Bruijn signatures

This module fixes the paper-facing objects and normalization ledger used by
the odd-branch feasibility spike.  It deliberately does not claim the
measure-theoretic de Bruijn identity: that identity remains a frozen target
signature until its Fubini and integrability obligations are proved.

The finite, arbitrary-size de Bruijn algebra is proved separately in
`OddDeBruijnFinite`.
-/

namespace ColomboGeneralK2.Odd

open scoped BigOperators

noncomputable section

/-- Strict truncated powers, including the paper's convention
`y₊^0 = 1` exactly when `0 < y`. -/
def truncPow (p : Nat) (y : Real) : Real :=
  if 0 < y then y ^ p else 0

@[simp]
theorem truncPow_of_pos {p : Nat} {y : Real} (hy : 0 < y) :
    truncPow p y = y ^ p := by
  simp [truncPow, hy]

@[simp]
theorem truncPow_of_nonpos {p : Nat} {y : Real} (hy : y ≤ 0) :
    truncPow p y = 0 := by
  simp [truncPow, not_lt.mpr hy]

/-- The left truncated-power column `L_i(t) = (t - x_i)₊^r`. -/
def leftKernel {m : Nat} (r : Nat) (x : Fin (2 * m) → Real)
    (t : Real) (i : Fin (2 * m)) : Real :=
  truncPow r (t - x i)

/-- The right truncated-power column `R_i(t) = (x_i - t)₊^r`. -/
def rightKernel {m : Nat} (r : Nat) (x : Fin (2 * m) → Real)
    (t : Real) (i : Fin (2 * m)) : Real :=
  truncPow r (x i - t)

/-- One paper-oriented adjacent pair of columns `[L(t), R(t)]`. -/
def betaColumns {m : Nat} (r : Nat) (x : Fin (2 * m) → Real) :
    Real → Fin (2 * m) → Fin 2 → Real :=
  fun t i side ↦ if side = 0 then leftKernel r x t i else rightKernel r x t i

@[simp]
theorem betaColumns_zero {m : Nat} (r : Nat) (x : Fin (2 * m) → Real)
    (t : Real) (i : Fin (2 * m)) :
    betaColumns r x t i 0 = leftKernel r x t i := by
  simp [betaColumns]

@[simp]
theorem betaColumns_one {m : Nat} (r : Nat) (x : Fin (2 * m) → Real)
    (t : Real) (i : Fin (2 * m)) :
    betaColumns r x t i 1 = rightKernel r x t i := by
  simp [betaColumns]

/-- The skew rank-two integrand `L_i R_j - R_i L_j` in the Beta identity. -/
def betaSkewKernel {m : Nat} (r : Nat) (x : Fin (2 * m) → Real)
    (t : Real) (i j : Fin (2 * m)) : Real :=
  leftKernel r x t i * rightKernel r x t j -
    rightKernel r x t i * leftKernel r x t j

@[simp]
theorem pairWedge_betaColumns {m : Nat} (r : Nat) (x : Fin (2 * m) → Real)
    (t : Real) (i j : Fin (2 * m)) :
    pairWedge (betaColumns r x) t i j = betaSkewKernel r x t i j := by
  simp [pairWedge, betaSkewKernel]

/-- The exact Beta normalization `c_r = (2r+1)!/(r!)^2`. -/
def betaConstant (r : Nat) : Real :=
  (Nat.factorial (2 * r + 1) : Real) / (Nat.factorial r : Real) ^ 2

/-- The labelled full-domain coefficient in de Bruijn's formula. -/
def fullDomainCoefficient (m : Nat) : Real :=
  (Nat.factorial m : Real)⁻¹

/-- The sole paper-level grouping sign, from interleaved pairs to all-left/all-right columns. -/
def groupingSign (m : Nat) : Real :=
  (-1 : Real) ^ m.choose 2

/-- The labelled full domain for `m` integration variables. -/
abbrev LabelledDomain (m : Nat) := Fin m → Real

/-- The strict ordered chamber `t₀ < ... < t_(m-1)`. -/
def orderedChamber (m : Nat) : Set (LabelledDomain m) :=
  {t | StrictMono t}

/-- Columns grouped as in the paper: all `L` columns, then all `R` columns. -/
def groupedColumnEquiv (m : Nat) : Fin m ⊕ Fin m ≃ Fin (2 * m) :=
  finSumFinEquiv.trans (finCongr (by omega))

/-- Generic grouped columns `[L_0,...,L_(m-1),R_0,...,R_(m-1)]`. -/
def groupedPairMatrix {I R : Type*} {m : Nat}
    (Z : I → Fin (2 * m) → Fin 2 → R) (t : Fin m → I) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) R :=
  fun i col ↦
    match (groupedColumnEquiv m).symm col with
    | Sum.inl q => Z (t q) i 0
    | Sum.inr q => Z (t q) i 1

/-- The paper's grouped split matrix for a labelled tuple of knots. -/
def groupedSplitMatrix {m : Nat} (r : Nat) (x : Fin (2 * m) → Real)
    (t : LabelledDomain m) : Matrix (Fin (2 * m)) (Fin (2 * m)) Real :=
  groupedPairMatrix (betaColumns r x) t

/-- The same split matrix in the adjacent paired order used by `recursivePf_pullback_fin`. -/
def pairedSplitMatrix {m : Nat} (r : Nat) (x : Fin (2 * m) → Real)
    (t : LabelledDomain m) : Matrix (Fin (2 * m)) (Fin (2 * m)) Real :=
  selectedPairMatrix (betaColumns r x) (List.Vector.ofFn t)

/-- The odd power-difference matrix appearing in Colombo's theorem. -/
def powerDifference {m : Nat} (x : Fin (2 * m) → Real) (D : Nat) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) Real :=
  fun i j ↦ (x j - x i) ^ D

/-! Exact low-rank normalization anchors mirrored by the Python guards. -/

@[simp] theorem betaConstant_zero : betaConstant 0 = 1 := by
  norm_num [betaConstant, Nat.factorial]

@[simp] theorem betaConstant_one : betaConstant 1 = 6 := by
  norm_num [betaConstant, Nat.factorial]

@[simp] theorem betaConstant_two : betaConstant 2 = 30 := by
  norm_num [betaConstant, Nat.factorial]

@[simp] theorem fullDomainCoefficient_one : fullDomainCoefficient 1 = 1 := by
  norm_num [fullDomainCoefficient, Nat.factorial]

@[simp] theorem fullDomainCoefficient_two : fullDomainCoefficient 2 = (2 : Real)⁻¹ := by
  norm_num [fullDomainCoefficient, Nat.factorial]

@[simp] theorem fullDomainCoefficient_three :
    fullDomainCoefficient 3 = (6 : Real)⁻¹ := by
  norm_num [fullDomainCoefficient, Nat.factorial]

@[simp] theorem groupingSign_one : groupingSign 1 = 1 := by
  norm_num [groupingSign, Nat.choose]

@[simp] theorem groupingSign_two : groupingSign 2 = -1 := by
  norm_num [groupingSign, Nat.choose]

@[simp] theorem groupingSign_three : groupingSign 3 = -1 := by
  norm_num [groupingSign, Nat.choose]

end

end ColomboGeneralK2.Odd
