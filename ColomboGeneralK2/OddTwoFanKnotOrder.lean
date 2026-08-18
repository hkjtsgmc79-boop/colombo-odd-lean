import ColomboGeneralK2.OddTwoFanData

/-!
# Order interface for the open two-fan knot vector

The repeated anchors are the only flat pieces of the open vector.  A merged
knot `z q` occurs at the exact open-vector position `m - 1 + q`; every open
entry before that position is strictly smaller and every entry after it is
strictly larger.  These lemmas are the mask-to-root bridge in the small-seam
calculation.
-/

namespace ColomboGeneralK2.Odd

noncomputable section

namespace TwoFanData

variable {m : Nat} (D : TwoFanData m)

/-- The open-vector index occupied by a merged knot. -/
def mergeOpenIndex (q : Fin (2 * m)) : Fin (4 * m - 2) :=
  ⟨m - 1 + (q : Nat), by
    have hq := q.isLt
    have hm := D.hm
    omega⟩

@[simp]
theorem mergeOpenIndex_val (q : Fin (2 * m)) :
    (D.mergeOpenIndex q : Nat) = m - 1 + (q : Nat) := rfl

/-- The central block of the open vector is literally the merged knot list. -/
@[simp]
theorem openKnot_mergeOpenIndex (q : Fin (2 * m)) :
    D.openKnot (D.mergeOpenIndex q) = D.z q := by
  unfold openKnot mergeOpenIndex
  have hm := D.hm
  have hq := q.isLt
  dsimp only
  split_ifs with hA hZ
  · omega
  · congr 1
    apply Fin.ext
    simp
  · omega

/-- Every open-vector entry strictly before a merged knot is smaller than
that knot, including entries in the repeated left-anchor block. -/
theorem openKnot_lt_z_of_lt_mergeOpenIndex
    (i : Fin (4 * m - 2)) (q : Fin (2 * m))
    (hi : (i : Nat) < m - 1 + (q : Nat)) :
    D.openKnot i < D.z q := by
  unfold openKnot
  by_cases hA : (i : Nat) < m - 1
  · simp only [dif_pos hA]
    exact D.leftAnchor_lt q
  · simp only [dif_neg hA]
    have hZ : (i : Nat) < 3 * m - 1 := by
      have hq := q.isLt
      omega
    simp only [dif_pos hZ]
    apply D.z_strict
    change (i : Nat) - (m - 1) < (q : Nat)
    omega

/-- Every open-vector entry strictly after a merged knot is larger than that
knot, including entries in the repeated right-anchor block. -/
theorem z_lt_openKnot_of_mergeOpenIndex_lt
    (q : Fin (2 * m)) (i : Fin (4 * m - 2))
    (hi : m - 1 + (q : Nat) < (i : Nat)) :
    D.z q < D.openKnot i := by
  unfold openKnot
  have hnotA : ¬ (i : Nat) < m - 1 := by omega
  simp only [dif_neg hnotA]
  by_cases hZ : (i : Nat) < 3 * m - 1
  · simp only [dif_pos hZ]
    apply D.z_strict
    change (q : Nat) < (i : Nat) - (m - 1)
    omega
  · simp only [dif_neg hZ]
    exact D.lt_rightAnchor q

/-- A left sample knot is the open knot at its merge rank. -/
theorem openKnot_alpha (j : Fin m) :
    D.openKnot (D.mergeOpenIndex (D.alpha j)) = D.s j := by
  exact D.openKnot_mergeOpenIndex (D.alpha j)

/-- A right sample knot is the open knot at its merge rank. -/
theorem openKnot_beta (j : Fin m) :
    D.openKnot (D.mergeOpenIndex (D.beta j)) = D.u j := by
  exact D.openKnot_mergeOpenIndex (D.beta j)

/-- The labelled pair order gives the strict point order `s_j < u_j`. -/
theorem s_lt_u (j : Fin m) : D.s j < D.u j := by
  exact D.z_strict (D.alpha_lt_beta j)

end TwoFanData

end

end ColomboGeneralK2.Odd
