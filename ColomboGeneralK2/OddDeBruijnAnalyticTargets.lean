import ColomboGeneralK2.OddDeBruijnSignatures
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Frozen analytic targets for the odd Beta--de Bruijn bridge

The definitions in this file are proposition-valued target signatures, not
proved theorems.  They make the L1 boundary executable and reviewable without
introducing an axiom or pretending that the Fubini/chamber layer has closed.
-/

namespace ColomboGeneralK2.Odd

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- Entrywise product integrability sufficient for the recursive-Pfaffian
de Bruijn proof.  Reversing `i,j` supplies the other wedge term. -/
def PairIntegrable {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {m : Nat} (Z : X → Fin (2 * m) → Fin 2 → Real) : Prop :=
  ∀ i j : Fin (2 * m), Integrable (fun t ↦ Z t i 0 * Z t j 1) μ

/-- Frozen arbitrary-`m` labelled full-domain identity.  The coefficient is
exactly `1 / m!`, and the determinant uses adjacent pairs
`[L₀,R₀,...,L_(m-1),R_(m-1)]`. -/
def FullDomainDeBruijnTarget {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] (m : Nat)
    (Z : X → Fin (2 * m) → Fin 2 → Real) : Prop :=
  PairIntegrable μ Z →
    recursivePf m (fun i j ↦ ∫ t, pairWedge Z t i j ∂μ) =
      fullDomainCoefficient m *
        ∫ t : Fin m → X,
          (selectedPairMatrix Z (List.Vector.ofFn t)).det
          ∂(Measure.pi fun _ : Fin m ↦ μ)

/-- Frozen ordered-chamber form.  Moving from adjacent pairs to all-left /
all-right columns contributes exactly `(-1)^(m.choose 2)` on the Pfaffian
side; no factorial remains on the strict chamber. -/
def OrderedChamberDeBruijnTarget (m : Nat)
    (Z : Real → Fin (2 * m) → Fin 2 → Real) : Prop :=
  PairIntegrable volume Z →
    groupingSign m *
        recursivePf m (fun i j ↦ ∫ t, pairWedge Z t i j) =
      ∫ t in orderedChamber m,
        (groupedPairMatrix Z t).det
        ∂(Measure.pi fun _ : Fin m ↦ (volume : Measure Real))

/-- Frozen scalar Beta identity with the exact paper normalization. -/
def BetaEntryIdentityTarget {m : Nat} (r : Nat)
    (x : Fin (2 * m) → Real) : Prop :=
  ∀ i j : Fin (2 * m),
    powerDifference x (2 * r + 1) i j =
      betaConstant r * ∫ t, betaSkewKernel r x t i j

/-- Frozen Colombo specialization of the ordered identity.  This is the
paper's exact `c_r^m`, grouped determinant, and global-sign statement. -/
def ColomboOrderedBetaDeBruijnTarget {m : Nat} (r : Nat)
    (x : Fin (2 * m) → Real) : Prop :=
  PairIntegrable volume (betaColumns r x) →
    groupingSign m * recursivePf m (powerDifference x (2 * r + 1)) =
      betaConstant r ^ m *
        ∫ t in orderedChamber m,
          (groupedSplitMatrix r x t).det
          ∂(Measure.pi fun _ : Fin m ↦ (volume : Measure Real))

end

end ColomboGeneralK2.Odd
