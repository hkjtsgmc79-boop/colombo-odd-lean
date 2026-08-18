import ColomboGeneralK2.OddDeBruijnAnalyticTargets
import ColomboGeneralK2.OddDeBruijnShuffle

/-!
# Odd Colombo MVP-1 signatures

This module fixes the exact conditional boundary of MVP-1.  The critical
paired-split positivity statement is an ordinary proposition supplied by a
caller; it is not an axiom and is not proved in MVP-1.  The remaining modules
must derive the analytic conversion, chamber sign, and strict endgame from
that explicit argument.
-/

namespace ColomboGeneralK2.Odd

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- Coordinatewise strict pairing of two labelled knot lists. -/
def Paired {m : Nat} (s u : Fin m → Real) : Prop :=
  ∀ q, s q < u q

/-- The paper's grouped split matrix with independent left and right knots. -/
def splitMatrix {m : Nat} (r : Nat) (x : Fin (2 * m) → Real)
    (s u : Fin m → Real) : Matrix (Fin (2 * m)) (Fin (2 * m)) Real :=
  fun i col ↦
    match (groupedColumnEquiv m).symm col with
    | Sum.inl q => leftKernel r x (s q) i
    | Sum.inr q => rightKernel r x (u q) i

/-- The paired-split determinant `H_r(X;s,u)`. -/
def splitDet {m : Nat} (r : Nat) (x : Fin (2 * m) → Real)
    (s u : Fin m → Real) : Real :=
  (splitMatrix r x s u).det

@[simp]
theorem splitMatrix_self {m : Nat} (r : Nat) (x : Fin (2 * m) → Real)
    (t : Fin m → Real) :
    splitMatrix r x t t = groupedSplitMatrix r x t := by
  rfl

@[simp]
theorem splitDet_self {m : Nat} (r : Nat) (x : Fin (2 * m) → Real)
    (t : Fin m → Real) :
    splitDet r x t t = (groupedSplitMatrix r x t).det := by
  rfl

/-- The sole unproved mathematical input admitted by the conditional MVP-1
endgame: every strictly ordered, strictly paired split determinant is
nonnegative.  This is a theorem argument, never a project axiom. -/
def PairedSplitNonnegative {m : Nat} (r : Nat)
    (x : Fin (2 * m) → Real) : Prop :=
  ∀ s u : Fin m → Real,
    StrictMono s → StrictMono u → Paired s u → 0 ≤ splitDet r x s u

/-- A coordinate-free version of the open central simplex: every first-half
knot lies below every integration variable, which in turn lies below every
second-half knot, and the variables are strictly ordered. -/
def centralSimplex {m : Nat} (x : Fin (2 * m) → Real) :
    Set (Fin m → Real) :=
  {t | StrictMono t ∧
    ∀ i q : Fin m,
      x (groupedColumnEquiv m (Sum.inl i)) < t q ∧
        t q < x (groupedColumnEquiv m (Sum.inr i))}

/-- Frozen nonnegative ordered-integral conclusion derived from the explicit
paired-split argument. -/
def OrderedSplitIntegralNonnegativeTarget {m : Nat} (r : Nat)
    (x : Fin (2 * m) → Real) : Prop :=
  PairedSplitNonnegative r x →
    0 ≤ ∫ t in orderedChamber m,
      (groupedSplitMatrix r x t).det
      ∂(Measure.pi fun _ : Fin m ↦ (volume : Measure Real))

/-- Frozen shifted-center strictness conclusion. -/
def CentralSplitStrictTarget {m : Nat} (r : Nat)
    (x : Fin (2 * m) → Real) : Prop :=
  ∀ t ∈ centralSimplex x, 0 < (groupedSplitMatrix r x t).det

/-- Exact conditional strict Pfaffian statement promised by MVP-1. -/
def OddPfaffianSignTarget {m : Nat} (r : Nat)
    (x : Fin (2 * m) → Real) : Prop :=
  0 < m → m - 1 ≤ r → StrictMono x → PairedSplitNonnegative r x →
    0 < groupingSign m *
      recursivePf m (powerDifference x (2 * r + 1))

/-- Exact conditional determinant-positivity corollary promised by MVP-1. -/
def OddDeterminantPositiveTarget {m : Nat} (r : Nat)
    (x : Fin (2 * m) → Real) : Prop :=
  0 < m → m - 1 ≤ r → StrictMono x → PairedSplitNonnegative r x →
    0 < (powerDifference x (2 * r + 1)).det

end

end ColomboGeneralK2.Odd
