import ColomboGeneralK2.GeneralADMS

/-!
# Literal matrix adapters for anti-diagonal minor summation

The symbolic AD-MS proof uses the entrywise matrix `pullbackFinset`.  This
file identifies it with the literal product `Z * C_w * Z.transpose`.  The
finite ambient column type is the subtype of pair labels belonging to `U`,
times the two sides of a pair.  This avoids introducing zero columns outside
`U` and requires no ambient `Fintype I` assumption.
-/

namespace ColomboGeneralK2

section LiteralPullback

variable {R I : Type*} [CommRing R] [LinearOrder I]

/-- The finite ambient column type: one adjacent two-column block per `t ∈ U`. -/
abbrev ambientPairIndex (U : Finset I) := {t // t ∈ U} × Fin 2

/-- The literal wide matrix restricted to the pair blocks indexed by `U`. -/
def ambientPairMatrix {m : Nat} (Z : I → Fin (2 * m) → Fin 2 → R)
    (U : Finset I) : Matrix (Fin (2 * m)) (ambientPairIndex U) R :=
  fun row col ↦ Z col.1.1 row col.2

/-- The skew `2 × 2` block with upper-right entry `a`. -/
def skewPairBlock (a : R) : Matrix (Fin 2) (Fin 2) R :=
  ![![0, a], ![-a, 0]]

/-- The block-diagonal skew matrix having block `[[0,w t],[-w t,0]]` at `t`. -/
def antiDiagonalBlockMatrix (w : I → R) (U : Finset I) :
    Matrix (ambientPairIndex U) (ambientPairIndex U) R :=
  fun p q ↦ if p.1 = q.1 then skewPairBlock (w p.1.1) p.2 q.2 else 0

@[simp]
theorem antiDiagonalBlockMatrix_same (w : I → R) (U : Finset I)
    (t : {t // t ∈ U}) (a b : Fin 2) :
    antiDiagonalBlockMatrix w U (t, a) (t, b) = skewPairBlock (w t.1) a b := by
  simp [antiDiagonalBlockMatrix]

@[simp]
theorem antiDiagonalBlockMatrix_ne (w : I → R) (U : Finset I)
    (t u : {t // t ∈ U}) (h : t ≠ u) (a b : Fin 2) :
    antiDiagonalBlockMatrix w U (t, a) (u, b) = 0 := by
  simp [antiDiagonalBlockMatrix, h]

theorem ambient_mul_antiDiagonal_apply {m : Nat}
    (Z : I → Fin (2 * m) → Fin 2 → R) (w : I → R) (U : Finset I)
    (row : Fin (2 * m)) (t : {t // t ∈ U}) (side : Fin 2) :
    (ambientPairMatrix Z U * antiDiagonalBlockMatrix w U) row (t, side) =
      ∑ b : Fin 2, Z t.1 row b * skewPairBlock (w t.1) b side := by
  rw [Matrix.mul_apply]
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ b : Fin 2,
        ambientPairMatrix Z U row (t, b) *
          antiDiagonalBlockMatrix w U (t, b) (t, side) := by
      apply Fintype.sum_eq_single t
      intro u hut
      simp [antiDiagonalBlockMatrix, hut]
    _ = _ := by simp [ambientPairMatrix, antiDiagonalBlockMatrix]

/--
The literal chained matrix product is exactly the entrywise finite pullback
used by the general AD-MS theorem.
-/
theorem ambient_mul_antiDiagonal_mul_transpose_apply {m : Nat}
    (Z : I → Fin (2 * m) → Fin 2 → R) (w : I → R) (U : Finset I)
    (i j : Fin (2 * m)) :
    ((ambientPairMatrix Z U * antiDiagonalBlockMatrix w U) *
        (ambientPairMatrix Z U).transpose) i j =
      pullbackFinset Z w U i j := by
  rw [Matrix.mul_apply]
  rw [pullbackFinset]
  rw [← Finset.sum_attach U]
  rw [Finset.attach_eq_univ]
  rw [Fintype.sum_prod_type]
  simp_rw [Fin.sum_univ_two, ambient_mul_antiDiagonal_apply]
  simp only [Matrix.transpose_apply, ambientPairMatrix, skewPairBlock, pairWedge]
  apply Finset.sum_congr rfl
  intro t ht
  simp [Fin.sum_univ_two]
  ring

/-- Matrix-level form of the literal pullback identity. -/
theorem ambient_mul_antiDiagonal_mul_transpose {m : Nat}
    (Z : I → Fin (2 * m) → Fin 2 → R) (w : I → R) (U : Finset I) :
    (ambientPairMatrix Z U * antiDiagonalBlockMatrix w U) *
        (ambientPairMatrix Z U).transpose = pullbackFinset Z w U := by
  ext i j
  exact ambient_mul_antiDiagonal_mul_transpose_apply Z w U i j

end LiteralPullback

section SelectedColumns

variable {R I : Type*} [LinearOrder I]

/--
Canonical selected-column coordinates for a size-`m` finite set.  It is an
equivalence, not merely an injection: sorting labels and adjoining `Fin 2`
enumerates every column of the finite ambient matrix exactly once.
-/
def selectedPairColumnEquiv {m : Nat} (S : Finset I) (hs : S.card = m) :
    Fin (2 * m) ≃ ambientPairIndex S :=
  (pairColumnEquiv m).symm.trans
    ((sortedPairEquiv S hs).prodCongr (Equiv.refl (Fin 2)))

theorem selectedPairColumnEquiv_injective {m : Nat} (S : Finset I)
    (hs : S.card = m) : Function.Injective (selectedPairColumnEquiv S hs) :=
  (selectedPairColumnEquiv S hs).injective

/-- The canonically sorted selected matrix is the literal finite ambient matrix. -/
theorem selectedPairMatrix_eq_ambient_submatrix {m : Nat}
    (Z : I → Fin (2 * m) → Fin 2 → R) (S : Finset I) (hs : S.card = m) :
    selectedPairMatrix Z (sortedPairVectorOfCard S hs) =
      (ambientPairMatrix Z S).submatrix id (selectedPairColumnEquiv S hs) := by
  ext row col
  simp [selectedPairMatrix, ambientPairMatrix, selectedPairColumnEquiv,
    sortedPairEquiv_apply]

end SelectedColumns

end ColomboGeneralK2
