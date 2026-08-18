import ColomboGeneralK2.OddStaircaseSupport
import ColomboGeneralK2.OddPlucker

/-!
# Staircase promotion from solid to arbitrary minors

This file contains the inductive load-bearing steps for the generalized
staircase--Fekete recognition theorem.  In particular, the northeast-shadow
split below is an arbitrary-size theorem: a single supported cross zero
forces an entire upper-right block to vanish, and the naturally ordered
minor factors with no permutation sign.

The statements assume neither total nonnegativity nor the sign of the target
minor.  The two factors are honest minors of strictly smaller positive order.
-/

namespace ColomboGeneralK2.Odd

/-- Strict positivity of an entry is equivalent to lying inside its declared
column interval; this is the converse direction not stored as a structure
field. -/
theorem support_mem_of_entry_pos {r c : Nat}
    {A : Matrix (Fin r) (Fin c) ℝ} (S : MonotoneColumnIntervalSupport A)
    {i : Fin r} {j : Fin c} (h : 0 < A i j) :
    S.lo j ≤ i ∧ i ≤ S.hi j := by
  constructor
  · by_contra hlo
    have hz := S.entry_zero i j (Or.inl (lt_of_not_ge hlo))
    exact (ne_of_gt h) hz
  · by_contra hhi
    have hz := S.entry_zero i j (Or.inr (lt_of_not_ge hhi))
    exact (ne_of_gt h) hz

/-- Restrict an increasing selection to its first `a` indices. -/
def prefixOrderEmb {a b n : Nat} (e : Fin (a + b) ↪o Fin n) : Fin a ↪o Fin n :=
  (Fin.castAddOrderEmb b).comp e

/-- Restrict an increasing selection to its last `b` indices. -/
def suffixOrderEmb {a b n : Nat} (e : Fin (a + b) ↪o Fin n) : Fin b ↪o Fin n :=
  (Fin.natAddOrderEmb a).comp e

@[simp]
theorem prefixOrderEmb_apply {a b n : Nat} (e : Fin (a + b) ↪o Fin n)
    (i : Fin a) : prefixOrderEmb e i = e (Fin.castAdd b i) := by
  rfl

@[simp]
theorem suffixOrderEmb_apply {a b n : Nat} (e : Fin (a + b) ↪o Fin n)
    (i : Fin b) : suffixOrderEmb e i = e (Fin.natAdd a i) := by
  rfl

/-- The two positive block sizes at a proper split are both strictly below
the original order.  These are the exact decreases consumed by the outer
strong induction. -/
theorem proper_split_orders (a b : Nat) :
    a + 1 < (a + 1) + (b + 1) ∧ b + 1 < (a + 1) + (b + 1) := by
  omega

/-- The order-zero leaf of the outer strong induction. -/
theorem matrixMinor_pos_zero {r c : Nat} (A : Matrix (Fin r) (Fin c) ℝ)
    (rows : Fin 0 ↪o Fin r) (cols : Fin 0 ↪o Fin c) :
    0 < matrixMinor A rows cols := by
  simp

/-- The order-one leaf follows directly from diagonal support. -/
theorem matrixMinor_pos_one_of_diagonalSupported
    {r c : Nat} {A : Matrix (Fin r) (Fin c) ℝ}
    (S : MonotoneColumnIntervalSupport A)
    (rows : Fin 1 ↪o Fin r) (cols : Fin 1 ↪o Fin c)
    (hsupp : DiagonalSupported S rows cols) :
    0 < matrixMinor A rows cols := by
  rw [matrixMinor_one]
  exact hsupp.entry_pos 0

/-- A zero upper-right block gives a sign-free factorization of a naturally
ordered minor into its prefix and suffix minors.  The formulation is fully
rectangular in the ambient matrix and arbitrary in both block sizes. -/
theorem matrixMinor_eq_mul_of_upperRight_zero
    {r c a b : Nat} (A : Matrix (Fin r) (Fin c) ℝ)
    (rows : Fin (a + b) ↪o Fin r) (cols : Fin (a + b) ↪o Fin c)
    (hzero : ∀ i : Fin a, ∀ j : Fin b,
      A (rows (Fin.castAdd b i)) (cols (Fin.natAdd a j)) = 0) :
    matrixMinor A rows cols =
      matrixMinor A (prefixOrderEmb rows) (prefixOrderEmb cols) *
      matrixMinor A (suffixOrderEmb rows) (suffixOrderEmb cols) := by
  let X : Matrix (Fin (a + b)) (Fin (a + b)) ℝ := A.submatrix rows cols
  let P : Matrix (Fin a) (Fin a) ℝ :=
    A.submatrix (prefixOrderEmb rows) (prefixOrderEmb cols)
  let Q : Matrix (Fin b) (Fin b) ℝ :=
    A.submatrix (suffixOrderEmb rows) (suffixOrderEmb cols)
  let L : Matrix (Fin b) (Fin a) ℝ :=
    A.submatrix (suffixOrderEmb rows) (prefixOrderEmb cols)
  have hblocks :
      X.submatrix finSumFinEquiv finSumFinEquiv =
        Matrix.fromBlocks P (0 : Matrix (Fin a) (Fin b) ℝ) L Q := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · simpa [X] using hzero i j
    · rfl
    · rfl
  rw [matrixMinor, matrixMinor, matrixMinor]
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv X]
  rw [hblocks, Matrix.det_fromBlocks_zero₁₂]

/-- The northeast-shadow split in its staircase form.

The selected diagonal is supported.  If the entry immediately northeast of
a proper cut is zero, positivity inside the column interval rules out a zero
on the lower side.  Monotonicity of the lower endpoints then propagates that
zero to the full upper-right block, so the determinant factors into minors of
orders `a+1` and `b+1`.
-/
theorem matrixMinor_eq_mul_of_supported_cross_zero
    {r c a b : Nat} {A : Matrix (Fin r) (Fin c) ℝ}
    (S : MonotoneColumnIntervalSupport A)
    (rows : Fin ((a + 1) + (b + 1)) ↪o Fin r)
    (cols : Fin ((a + 1) + (b + 1)) ↪o Fin c)
    (hsupp : DiagonalSupported S rows cols)
    (hcross : A
      (rows (Fin.castAdd (b + 1) (Fin.last a)))
      (cols (Fin.natAdd (a + 1) (0 : Fin (b + 1)))) = 0) :
    matrixMinor A rows cols =
      matrixMinor A (prefixOrderEmb rows) (prefixOrderEmb cols) *
      matrixMinor A (suffixOrderEmb rows) (suffixOrderEmb cols) := by
  have hindex :
      (Fin.castAdd (b + 1) (Fin.last a) : Fin ((a + 1) + (b + 1))) <
        Fin.natAdd (a + 1) (0 : Fin (b + 1)) := by
    change a < a + 1
    omega
  have habove :
      rows (Fin.castAdd (b + 1) (Fin.last a)) <
        S.lo (cols (Fin.natAdd (a + 1) (0 : Fin (b + 1)))) := by
    by_contra h
    have hlo : S.lo (cols (Fin.natAdd (a + 1) (0 : Fin (b + 1)))) ≤
        rows (Fin.castAdd (b + 1) (Fin.last a)) := le_of_not_gt h
    have hhi : rows (Fin.castAdd (b + 1) (Fin.last a)) ≤
        S.hi (cols (Fin.natAdd (a + 1) (0 : Fin (b + 1)))) :=
      le_trans (rows.monotone (le_of_lt hindex)) (hsupp _).2
    exact (ne_of_gt (S.entry_pos _ _ hlo hhi)) hcross
  apply matrixMinor_eq_mul_of_upperRight_zero A rows cols
  intro i j
  apply S.entry_zero
  left
  refine lt_of_le_of_lt (rows.monotone ?_)
    (lt_of_lt_of_le habove (S.lo_mono (cols.monotone ?_)))
  · change (i : Nat) ≤ a
    omega
  · change a + 1 ≤ a + 1 + (j : Nat)
    omega

/-- Both exact factors in the northeast-shadow split retain supported
increasing diagonals. -/
theorem diagonalSupported_prefix_suffix
    {r c a b : Nat} {A : Matrix (Fin r) (Fin c) ℝ}
    {S : MonotoneColumnIntervalSupport A}
    {rows : Fin (a + b) ↪o Fin r} {cols : Fin (a + b) ↪o Fin c}
    (hsupp : DiagonalSupported S rows cols) :
    DiagonalSupported S (prefixOrderEmb rows) (prefixOrderEmb cols) ∧
      DiagonalSupported S (suffixOrderEmb rows) (suffixOrderEmb cols) := by
  exact ⟨hsupp.comp (Fin.castAddOrderEmb b), hsupp.comp (Fin.natAddOrderEmb a)⟩

/-- Positivity propagation across the northeast-shadow split.  Its inputs
are only the signs of the two exact lower-order factors produced above; in a
strong induction these are the two strictly smaller-order hypotheses. -/
theorem matrixMinor_pos_of_supported_cross_zero
    {r c a b : Nat} {A : Matrix (Fin r) (Fin c) ℝ}
    (S : MonotoneColumnIntervalSupport A)
    (rows : Fin ((a + 1) + (b + 1)) ↪o Fin r)
    (cols : Fin ((a + 1) + (b + 1)) ↪o Fin c)
    (hsupp : DiagonalSupported S rows cols)
    (hcross : A
      (rows (Fin.castAdd (b + 1) (Fin.last a)))
      (cols (Fin.natAdd (a + 1) (0 : Fin (b + 1)))) = 0)
    (hprefix : 0 < matrixMinor A
      (prefixOrderEmb rows) (prefixOrderEmb cols))
    (hsuffix : 0 < matrixMinor A
      (suffixOrderEmb rows) (suffixOrderEmb cols)) :
    0 < matrixMinor A rows cols := by
  rw [matrixMinor_eq_mul_of_supported_cross_zero S rows cols hsupp hcross]
  exact mul_pos hprefix hsuffix

/-- The same northeast-shadow branch packaged for the outer strong
induction.  The only recursive input ranges over strictly smaller orders;
it cannot be instantiated with the target order. -/
theorem matrixMinor_pos_of_supported_cross_zero_of_lower_order
    {r c a b : Nat} {A : Matrix (Fin r) (Fin c) ℝ}
    (S : MonotoneColumnIntervalSupport A)
    (rows : Fin ((a + 1) + (b + 1)) ↪o Fin r)
    (cols : Fin ((a + 1) + (b + 1)) ↪o Fin c)
    (hsupp : DiagonalSupported S rows cols)
    (hcross : A
      (rows (Fin.castAdd (b + 1) (Fin.last a)))
      (cols (Fin.natAdd (a + 1) (0 : Fin (b + 1)))) = 0)
    (hIH : ∀ l : Nat, l < (a + 1) + (b + 1) →
      ∀ (subRows : Fin l ↪o Fin r) (subCols : Fin l ↪o Fin c),
        DiagonalSupported S subRows subCols →
          0 < matrixMinor A subRows subCols) :
    0 < matrixMinor A rows cols := by
  obtain ⟨hfirst, hsecond⟩ := diagonalSupported_prefix_suffix hsupp
  obtain ⟨hfirstOrder, hsecondOrder⟩ := proper_split_orders a b
  apply matrixMinor_pos_of_supported_cross_zero S rows cols hsupp hcross
  · exact hIH (a + 1) hfirstOrder _ _ hfirst
  · exact hIH (b + 1) hsecondOrder _ _ hsecond

/-- An increasing selection has an adjacent ambient gap when one of its
successive values differs by more than one. -/
def HasAdjacentGap {k n : Nat} (e : Fin (k + 1) ↪o Fin n) : Prop :=
  ∃ i : Fin k, (e i.castSucc : Nat) + 1 < (e i.succ : Nat)

/-- The inner induction measure, written as the sum of all adjacent ambient
gaps.  This is definitionally nonnegative and is zero exactly for a
consecutive selection. -/
def embeddingDispersion {k n : Nat} (e : Fin (k + 1) ↪o Fin n) : Nat :=
  ∑ i : Fin k,
    ((e (Fin.succ i) : Nat) - ((e (Fin.castSucc i) : Nat) + 1))

/-- An increasing selection advances by at least one ambient index at every
step. -/
theorem orderEmb_start_add_le {k n : Nat} (e : Fin (k + 1) ↪o Fin n)
    (i : Fin (k + 1)) : (e 0 : Nat) + (i : Nat) ≤ (e i : Nat) := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
      have hadj : (e i.castSucc : Nat) + 1 ≤ (e i.succ : Nat) := by
        exact e.strictMono (Fin.castSucc_lt_succ (i := i))
      have ih' : (e 0 : Nat) + (i.castSucc : Nat) + 1 ≤
          (e i.castSucc : Nat) + 1 := Nat.add_le_add_right ih 1
      simpa only [Fin.val_succ, Fin.val_castSucc, Nat.add_assoc] using
        le_trans ih' hadj

/-- Telescoping form of the dispersion.  This turns endpoint changes in the
natural Pluecker frames into literal strict decreases of the induction
measure. -/
theorem embeddingDispersion_eq_span {k n : Nat}
    (e : Fin (k + 1) ↪o Fin n) :
    embeddingDispersion e =
      (e (Fin.last k) : Nat) - (e 0 : Nat) - k := by
  induction k with
  | zero => simp [embeddingDispersion]
  | succ k ih =>
      let e' : Fin (k + 1) ↪o Fin n :=
        (Fin.castLEOrderEmb (by omega : k + 1 ≤ k + 2)).comp e
      have ih' := ih e'
      have he'last : (e' (Fin.last k) : Nat) = (e ⟨k, by omega⟩ : Nat) := by
        rfl
      have he'zero : (e' 0 : Nat) = (e 0 : Nat) := by
        rfl
      rw [he'last, he'zero] at ih'
      rw [embeddingDispersion, Fin.sum_univ_castSucc]
      rw [show (∑ i : Fin k,
          ((e (Fin.succ i.castSucc) : Nat) -
            ((e (Fin.castSucc i.castSucc) : Nat) + 1))) =
          embeddingDispersion e' by rfl]
      rw [ih']
      have h01 : (e 0 : Nat) + k ≤ (e ⟨k, by omega⟩ : Nat) := by
        exact orderEmb_start_add_le e ⟨k, by omega⟩
      have h12 : (e ⟨k, by omega⟩ : Nat) + 1 ≤
          (e (Fin.last (k + 1)) : Nat) := by
        have hidx : (⟨k, by omega⟩ : Fin (k + 2)) < Fin.last (k + 1) := by
          change k < k + 1
          omega
        exact e.strictMono hidx
      change
        ((e ⟨k, by omega⟩ : Nat) - (e 0 : Nat) - k) +
          ((e (Fin.last (k + 1)) : Nat) - ((e ⟨k, by omega⟩ : Nat) + 1)) =
        (e (Fin.last (k + 1)) : Nat) - (e 0 : Nat) - (k + 1)
      omega

theorem embeddingDispersion_eq_zero_iff {k n : Nat}
    (e : Fin (k + 1) ↪o Fin n) :
    embeddingDispersion e = 0 ↔ ¬ HasAdjacentGap e := by
  have hsum : embeddingDispersion e = 0 ↔
      ∀ i : Fin k, (e i.succ : Nat) - ((e i.castSucc : Nat) + 1) = 0 := by
    rw [embeddingDispersion,
      Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ Nat.zero_le _)]
    simp
  rw [hsum]
  constructor
  · intro h hgap
    obtain ⟨i, hi⟩ := hgap
    have hzero := h i
    rw [Nat.sub_eq_zero_iff_le] at hzero
    exact (not_le_of_gt hi) hzero
  · intro h i
    rw [Nat.sub_eq_zero_iff_le]
    exact le_of_not_gt (fun hi ↦ h ⟨i, hi⟩)

/-- Filling the first missing value in an internal adjacent gap decreases
dispersion by exactly one.  The inserted slot is neither endpoint, so the
span is unchanged while the selected order increases by one. -/
theorem insertGap_dispersion_add_one {k n : Nat}
    (e : Fin (k + 1) ↪o Fin n) (i : Fin k)
    (hgap : (e i.castSucc : Nat) + 1 < (e i.succ : Nat)) :
    embeddingDispersion (insertGapOrderEmb e i hgap) + 1 =
      embeddingDispersion e := by
  let full := insertGapOrderEmb e i hgap
  have herase := insertGapOrderEmb_erase e i hgap
  have hfirst := DFunLike.congr_fun herase (0 : Fin (k + 1))
  have hlast := DFunLike.congr_fun herase (Fin.last k)
  rw [embeddingDispersion_eq_span, embeddingDispersion_eq_span]
  change (full (Fin.last (k + 1)) : Nat) - (full 0 : Nat) - (k + 1) + 1 =
    (e (Fin.last k) : Nat) - (e 0 : Nat) - k
  have hfirst' : full 0 = e 0 := by
    simpa [full, gapSlot_ne_zero] using hfirst
  have hlast' : full (Fin.last (k + 1)) = e (Fin.last k) := by
    simpa [full, gapSlot_ne_last] using hlast
  rw [hfirst', hlast']
  have hdispPos : 0 < embeddingDispersion e := by
    rw [embeddingDispersion]
    apply Finset.sum_pos' (fun _ _ ↦ Nat.zero_le _)
    refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [Nat.sub_pos_iff_lt]
    exact hgap
  rw [embeddingDispersion_eq_span] at hdispPos
  have hspan : (e 0 : Nat) + k + 1 ≤ (e (Fin.last k) : Nat) := by
    omega
  omega

/-- In the first same-order Pluecker branch, deleting the first column of
the gap-filled selection strictly raises its first endpoint and therefore
strictly decreases dispersion. -/
theorem dropFirst_insertGap_dispersion_lt {k n : Nat}
    (e : Fin (k + 1) ↪o Fin n) (i : Fin k)
    (hgap : (e i.castSucc : Nat) + 1 < (e i.succ : Nat)) :
    embeddingDispersion
      ((Fin.succOrderEmb (k + 1)).comp (insertGapOrderEmb e i hgap)) <
        embeddingDispersion e := by
  let full := insertGapOrderEmb e i hgap
  let big : Fin (k + 1) ↪o Fin n := (Fin.succOrderEmb (k + 1)).comp full
  have herase := insertGapOrderEmb_erase e i hgap
  have hfirst := DFunLike.congr_fun herase (0 : Fin (k + 1))
  have hlast := DFunLike.congr_fun herase (Fin.last k)
  have hfirst' : full 0 = e 0 := by
    simpa [full, gapSlot_ne_zero] using hfirst
  have hlast' : full (Fin.last (k + 1)) = e (Fin.last k) := by
    simpa [full, gapSlot_ne_last] using hlast
  rw [embeddingDispersion_eq_span, embeddingDispersion_eq_span]
  change (big (Fin.last k) : Nat) - (big 0 : Nat) - k <
    (e (Fin.last k) : Nat) - (e 0 : Nat) - k
  have hbigStart : big 0 = full 1 := by rfl
  have hbigLast : big (Fin.last k) = full (Fin.last (k + 1)) := by rfl
  rw [hbigStart, hbigLast, hlast', ← hfirst']
  have hstrict : (full 0 : Nat) < (full 1 : Nat) := by
    exact full.strictMono (by simp)
  have hspan : (full 1 : Nat) + k ≤ (full (Fin.last (k + 1)) : Nat) := by
    exact orderEmb_start_add_le big (Fin.last k)
  omega

/-- In the second same-order Pluecker branch, deleting the last column of
the gap-filled selection strictly lowers its last endpoint and therefore
strictly decreases dispersion. -/
theorem dropLast_insertGap_dispersion_lt {k n : Nat}
    (e : Fin (k + 1) ↪o Fin n) (i : Fin k)
    (hgap : (e i.castSucc : Nat) + 1 < (e i.succ : Nat)) :
    embeddingDispersion
      ((Fin.castAddOrderEmb 1).comp (insertGapOrderEmb e i hgap)) <
        embeddingDispersion e := by
  let full := insertGapOrderEmb e i hgap
  let big : Fin (k + 1) ↪o Fin n := (Fin.castAddOrderEmb 1).comp full
  have herase := insertGapOrderEmb_erase e i hgap
  have hfirst := DFunLike.congr_fun herase (0 : Fin (k + 1))
  have hlast := DFunLike.congr_fun herase (Fin.last k)
  have hfirst' : full 0 = e 0 := by
    simpa [full, gapSlot_ne_zero] using hfirst
  have hlast' : full (Fin.last (k + 1)) = e (Fin.last k) := by
    simpa [full, gapSlot_ne_last] using hlast
  rw [embeddingDispersion_eq_span, embeddingDispersion_eq_span]
  change (big (Fin.last k) : Nat) - (big 0 : Nat) - k <
    (e (Fin.last k) : Nat) - (e 0 : Nat) - k
  have hbigStart : big 0 = full 0 := by rfl
  have hbigLast : big (Fin.last k) = full ⟨k, by omega⟩ := by rfl
  rw [hbigStart, hbigLast, hfirst', ← hlast']
  have hstrict : (full ⟨k, by omega⟩ : Nat) <
      (full (Fin.last (k + 1)) : Nat) := by
    apply full.strictMono
    change k < k + 1
    omega
  have hspan : (full 0 : Nat) + k ≤ (full ⟨k, by omega⟩ : Nat) := by
    exact orderEmb_start_add_le big (Fin.last k)
  omega

/-- Subtraction-free positivity propagation for the fully natural-order
Pluecker frame.  The two cross factors need only be nonnegative; in the
staircase induction each is either structurally zero or positive at a
strictly smaller order/dispersion. -/
theorem natural_plucker_target_pos {n : Nat}
    (X : Matrix (Fin (n + 2)) (Fin (n + 3)) ℝ)
    (p : Fin (n + 3)) (hp0 : 0 < p) (hpLast : p < Fin.last (n + 2))
    (hD : (X.submatrix (OddPlucker.middleEmb n)
      (OddPlucker.commonColEmb p)).det ≠ 0)
    (hden : 0 < OddPlucker.denMinor X)
    (hsmall : 0 < OddPlucker.smallJOneMinor X p hpLast)
    (hbig : 0 < OddPlucker.bigPJLastMinor X)
    (hcrossSmall : 0 ≤ OddPlucker.smallJLastMinor X p)
    (hcrossBig : 0 ≤ OddPlucker.bigJOnePMinor X) :
    0 < OddPlucker.targetMinor X p := by
  have hprod : 0 < OddPlucker.denMinor X * OddPlucker.targetMinor X p := by
    rw [OddPlucker.natural_plucker_frame X p hp0 hpLast hD]
    exact add_pos_of_pos_of_nonneg (mul_pos hsmall hbig)
      (mul_nonneg hcrossSmall hcrossBig)
  exact pos_of_mul_pos_right hprod hden.le

/-- A complete, strictly well-founded column-gap Pluecker step.

The five support premises record only the combinatorial fact that the common
frame and first-branch minors have supported diagonals; they contain no sign
information.  Every sign is obtained from either the strictly lower-order
hypothesis or the same-order hypothesis at a strictly smaller dispersion.
The remaining same-order cross minor is split into the supported/structural-
zero cases inside the proof.
-/
theorem columnGap_plucker_step
    {r c n : Nat} {A : Matrix (Fin r) (Fin c) ℝ}
    (S : MonotoneColumnIntervalSupport A)
    (rows : Fin (n + 2) ↪o Fin r) (cols : Fin (n + 2) ↪o Fin c)
    (i : Fin (n + 1))
    (hgap : (cols i.castSucc : Nat) + 1 < (cols i.succ : Nat))
    (hDsup : DiagonalSupported S
      ((OddPlucker.middleEmb n).comp rows)
      ((OddPlucker.commonColEmb (gapSlot i)).comp
        (insertGapOrderEmb cols i hgap)))
    (hdenSup : DiagonalSupported S
      ((OddPlucker.topEmb n).comp rows)
      ((OddPlucker.interiorEmb n).comp
        (insertGapOrderEmb cols i hgap)))
    (hsmallSup : DiagonalSupported S
      ((OddPlucker.topEmb n).comp rows)
      ((OddPlucker.smallJOneEmb (gapSlot i) (by
        change (i : Nat) + 1 < n + 2
        omega)).comp (insertGapOrderEmb cols i hgap)))
    (hbigSup : DiagonalSupported S rows
      ((Fin.succOrderEmb (n + 2)).comp
        (insertGapOrderEmb cols i hgap)))
    (hcrossSmallSup : DiagonalSupported S
      ((OddPlucker.topEmb n).comp rows)
      ((OddPlucker.smallJLastEmb (gapSlot i)).comp
        (insertGapOrderEmb cols i hgap)))
    (hLower : ∀ l : Nat, l < n + 2 →
      ∀ (subRows : Fin l ↪o Fin r) (subCols : Fin l ↪o Fin c),
        DiagonalSupported S subRows subCols →
          0 < matrixMinor A subRows subCols)
    (hSame : ∀ (subCols : Fin (n + 2) ↪o Fin c),
      embeddingDispersion subCols < embeddingDispersion cols →
      DiagonalSupported S rows subCols →
        0 < matrixMinor A rows subCols) :
    0 < matrixMinor A rows cols := by
  let p : Fin (n + 3) := gapSlot i
  let full : Fin (n + 3) ↪o Fin c := insertGapOrderEmb cols i hgap
  let X : Matrix (Fin (n + 2)) (Fin (n + 3)) ℝ := A.submatrix rows full
  have hp0 : (0 : Fin (n + 3)) < p := by
    change 0 < (i : Nat) + 1
    omega
  have hpLast : p < Fin.last (n + 2) := by
    change (i : Nat) + 1 < n + 2
    omega
  have hDpos : 0 < (X.submatrix (OddPlucker.middleEmb n)
      (OddPlucker.commonColEmb p)).det := by
    simpa [X, p, full, matrixMinor, Matrix.submatrix_submatrix] using
      hLower n (by omega) _ _ hDsup
  have hden : 0 < OddPlucker.denMinor X := by
    simpa [OddPlucker.denMinor, X, p, full, matrixMinor,
      Matrix.submatrix_submatrix] using
      hLower (n + 1) (by omega) _ _ hdenSup
  have hsmall : 0 < OddPlucker.smallJOneMinor X p hpLast := by
    simpa [OddPlucker.smallJOneMinor, X, p, full, matrixMinor,
      Matrix.submatrix_submatrix] using
      hLower (n + 1) (by omega) _ _ hsmallSup
  have hbig : 0 < OddPlucker.bigPJLastMinor X := by
    simpa [OddPlucker.bigPJLastMinor, X, full, matrixMinor,
      Matrix.submatrix_submatrix] using
      hSame ((Fin.succOrderEmb (n + 2)).comp full)
        (by simpa [full] using
          dropFirst_insertGap_dispersion_lt cols i hgap) hbigSup
  have hcrossSmall : 0 ≤ OddPlucker.smallJLastMinor X p := by
    have hpos : 0 < OddPlucker.smallJLastMinor X p := by
      simpa [OddPlucker.smallJLastMinor, X, p, full, matrixMinor,
        Matrix.submatrix_submatrix] using
        hLower (n + 1) (by omega) _ _ hcrossSmallSup
    exact hpos.le
  have hcrossBig : 0 ≤ OddPlucker.bigJOnePMinor X := by
    let crossCols : Fin (n + 2) ↪o Fin c :=
      (Fin.castAddOrderEmb 1).comp full
    by_cases hs : DiagonalSupported S rows crossCols
    · have hpos : 0 < matrixMinor A rows crossCols :=
        hSame crossCols (by
          simpa [crossCols, full] using
            dropLast_insertGap_dispersion_lt cols i hgap) hs
      simpa [OddPlucker.bigJOnePMinor, X, crossCols, full, matrixMinor,
        Matrix.submatrix_submatrix] using hpos.le
    · have hz := matrixMinor_eq_zero_of_not_diagonalSupported S rows crossCols hs
      change 0 ≤ matrixMinor A rows ((OddPlucker.prefixEmb n).comp full)
      have heq : (OddPlucker.prefixEmb n).comp full = crossCols := by
        rfl
      rw [heq, hz]
  have htarget : 0 < OddPlucker.targetMinor X p :=
    OddPlucker.natural_plucker_target_pos X p hp0 hpLast hDpos.ne'
      hden hsmall hbig hcrossSmall hcrossBig
  change 0 < matrixMinor A rows ((gapSlot i).succAboveOrderEmb.comp full) at htarget
  rw [show (gapSlot i).succAboveOrderEmb.comp full = cols by
    simpa [full] using insertGapOrderEmb_erase cols i hgap] at htarget
  exact htarget

/-! ### Support verification for the natural column-gap frame -/

theorem common_gap_cols_eq {c n : Nat}
    (cols : Fin (n + 2) ↪o Fin c) (i : Fin (n + 1))
    (hgap : (cols i.castSucc : Nat) + 1 < (cols i.succ : Nat)) :
    (OddPlucker.commonColEmb (gapSlot i)).comp (insertGapOrderEmb cols i hgap) =
      (OddPlucker.middleEmb n).comp cols := by
  ext j
  simp only [OddPlucker.commonColEmb, OrderEmbedding.coe_comp,
    Function.comp_apply]
  exact congrArg Fin.val (DFunLike.congr_fun
    (insertGapOrderEmb_erase cols i hgap) (OddPlucker.middleEmb n j))

theorem smallJOne_gap_cols_eq {c n : Nat}
    (cols : Fin (n + 2) ↪o Fin c) (i : Fin (n + 1))
    (hgap : (cols i.castSucc : Nat) + 1 < (cols i.succ : Nat)) :
    (OddPlucker.smallJOneEmb (gapSlot i) (by
      change (i : Nat) + 1 < n + 2
      omega)).comp (insertGapOrderEmb cols i hgap) =
      (OddPlucker.topEmb n).comp cols := by
  ext j
  simp only [OrderEmbedding.coe_comp, Function.comp_apply]
  have hind : OddPlucker.smallJOneEmb (gapSlot i) (by
      change (i : Nat) + 1 < n + 2
      omega) j = (gapSlot i).succAbove (OddPlucker.topEmb n j) := by
    apply Fin.ext
    simp only [OddPlucker.smallJOneEmb, OddPlucker.prefixEmb,
      OddPlucker.topEmb, gapSlot, Fin.succAbove,
      OrderEmbedding.coe_comp, Function.comp_apply,
      Fin.castLEOrderEmb_apply, Fin.val_castLE,
      Fin.succAboveOrderEmb_apply]
    split_ifs <;> simp
    case neg h₁ h₂ =>
      change (j : Nat) < (i : Nat) + 1 at h₁
      change ¬(j : Nat) < (i : Nat) + 1 at h₂
      exact h₂ h₁
    case pos h₁ h₂ =>
      change ¬(j : Nat) < (i : Nat) + 1 at h₁
      change (j : Nat) < (i : Nat) + 1 at h₂
      exact h₁ h₂
  rw [hind, insertGapOrderEmb_apply_succAbove]

theorem smallJLast_gap_cols_eq {c n : Nat}
    (cols : Fin (n + 2) ↪o Fin c) (i : Fin (n + 1))
    (hgap : (cols i.castSucc : Nat) + 1 < (cols i.succ : Nat)) :
    (OddPlucker.smallJLastEmb (gapSlot i)).comp
        (insertGapOrderEmb cols i hgap) =
      (Fin.succOrderEmb (n + 1)).comp cols := by
  ext j
  simp only [OddPlucker.smallJLastEmb, OrderEmbedding.coe_comp,
    Function.comp_apply]
  exact congrArg Fin.val (DFunLike.congr_fun
    (insertGapOrderEmb_erase cols i hgap) (Fin.succOrderEmb (n + 1) j))

/-- Under a positive superdiagonal, the full first Pluecker big minor is
supported.  At the inserted gap value, lower-endpoint support comes from the
old superdiagonal and upper-endpoint support from the old diagonal, with
monotonicity interpolating between the two columns. -/
theorem bigPJ_gap_diagonalSupported
    {r c n : Nat} {A : Matrix (Fin r) (Fin c) ℝ}
    (S : MonotoneColumnIntervalSupport A)
    (rows : Fin (n + 2) ↪o Fin r) (cols : Fin (n + 2) ↪o Fin c)
    (hsupp : DiagonalSupported S rows cols)
    (hsuper : ∀ t : Fin (n + 1),
      0 < A (rows t.castSucc) (cols t.succ))
    (i : Fin (n + 1))
    (hgap : (cols i.castSucc : Nat) + 1 < (cols i.succ : Nat)) :
    DiagonalSupported S rows
      ((Fin.succOrderEmb (n + 2)).comp (insertGapOrderEmb cols i hgap)) := by
  intro t
  apply support_mem_of_entry_pos S
  let full := insertGapOrderEmb cols i hgap
  by_cases hti : (t : Nat) < (i : Nat)
  · let u : Fin (n + 1) := ⟨t, by omega⟩
    have htcast : u.castSucc = t := by ext; rfl
    have hidx : (gapSlot i).succAbove u.succ = t.succ := by
      apply Fin.ext
      rw [Fin.succAbove_of_castSucc_lt]
      · rfl
      · change (t : Nat) + 1 < (i : Nat) + 1
        omega
    have hcol : full t.succ = cols u.succ := by
      rw [← hidx]
      exact insertGapOrderEmb_apply_succAbove cols i hgap u.succ
    change 0 < A (rows t) (full t.succ)
    rw [hcol, ← htcast]
    exact hsuper u
  · by_cases htiEq : (t : Nat) = (i : Nat)
    · have ht : t = i.castSucc := by ext; exact htiEq
      subst t
      have hcol : full i.castSucc.succ = gapValue cols i hgap := by
        have hslot : i.castSucc.succ = gapSlot i := rfl
        rw [hslot, insertGapOrderEmb_apply_gapSlot]
      change 0 < A (rows i.castSucc) (full i.castSucc.succ)
      rw [hcol]
      apply S.entry_pos
      · exact le_trans
          (S.lo_mono (by
            change (gapValue cols i hgap : Nat) ≤ (cols i.succ : Nat)
            simp [gapValue]))
          (support_mem_of_entry_pos S (hsuper i)).1
      · exact le_trans (hsupp i.castSucc).2
          (S.hi_mono (by
            change (cols i.castSucc : Nat) ≤ (gapValue cols i hgap : Nat)
            simp [gapValue]))
    · have hit : (i : Nat) < (t : Nat) := by omega
      have hidx : (gapSlot i).succAbove t = t.succ := by
        apply Fin.ext
        rw [Fin.succAbove_of_le_castSucc]
        change (i : Nat) + 1 ≤ (t : Nat)
        omega
      have hcol : full t.succ = cols t := by
        rw [← hidx]
        exact insertGapOrderEmb_apply_succAbove cols i hgap t
      change 0 < A (rows t) (full t.succ)
      rw [hcol]
      exact hsupp.entry_pos t

theorem common_gap_diagonalSupported
    {r c n : Nat} {A : Matrix (Fin r) (Fin c) ℝ}
    (S : MonotoneColumnIntervalSupport A)
    (rows : Fin (n + 2) ↪o Fin r) (cols : Fin (n + 2) ↪o Fin c)
    (hsupp : DiagonalSupported S rows cols)
    (i : Fin (n + 1))
    (hgap : (cols i.castSucc : Nat) + 1 < (cols i.succ : Nat)) :
    DiagonalSupported S ((OddPlucker.middleEmb n).comp rows)
      ((OddPlucker.commonColEmb (gapSlot i)).comp
        (insertGapOrderEmb cols i hgap)) := by
  rw [common_gap_cols_eq cols i hgap]
  exact hsupp.comp (OddPlucker.middleEmb n)

theorem smallJOne_gap_diagonalSupported
    {r c n : Nat} {A : Matrix (Fin r) (Fin c) ℝ}
    (S : MonotoneColumnIntervalSupport A)
    (rows : Fin (n + 2) ↪o Fin r) (cols : Fin (n + 2) ↪o Fin c)
    (hsupp : DiagonalSupported S rows cols)
    (i : Fin (n + 1))
    (hgap : (cols i.castSucc : Nat) + 1 < (cols i.succ : Nat)) :
    DiagonalSupported S ((OddPlucker.topEmb n).comp rows)
      ((OddPlucker.smallJOneEmb (gapSlot i) (by
        change (i : Nat) + 1 < n + 2
        omega)).comp (insertGapOrderEmb cols i hgap)) := by
  rw [smallJOne_gap_cols_eq cols i hgap]
  exact hsupp.comp (OddPlucker.topEmb n)

theorem smallJLast_gap_diagonalSupported
    {r c n : Nat} {A : Matrix (Fin r) (Fin c) ℝ}
    (S : MonotoneColumnIntervalSupport A)
    (rows : Fin (n + 2) ↪o Fin r) (cols : Fin (n + 2) ↪o Fin c)
    (hsuper : ∀ t : Fin (n + 1),
      0 < A (rows t.castSucc) (cols t.succ))
    (i : Fin (n + 1))
    (hgap : (cols i.castSucc : Nat) + 1 < (cols i.succ : Nat)) :
    DiagonalSupported S ((OddPlucker.topEmb n).comp rows)
      ((OddPlucker.smallJLastEmb (gapSlot i)).comp
        (insertGapOrderEmb cols i hgap)) := by
  rw [smallJLast_gap_cols_eq cols i hgap]
  intro t
  apply support_mem_of_entry_pos S
  change 0 < A (rows t.castSucc) (cols t.succ)
  exact hsuper t

theorem den_gap_diagonalSupported
    {r c n : Nat} {A : Matrix (Fin r) (Fin c) ℝ}
    (S : MonotoneColumnIntervalSupport A)
    (rows : Fin (n + 2) ↪o Fin r) (cols : Fin (n + 2) ↪o Fin c)
    (hsupp : DiagonalSupported S rows cols)
    (hsuper : ∀ t : Fin (n + 1),
      0 < A (rows t.castSucc) (cols t.succ))
    (i : Fin (n + 1))
    (hgap : (cols i.castSucc : Nat) + 1 < (cols i.succ : Nat)) :
    DiagonalSupported S ((OddPlucker.topEmb n).comp rows)
      ((OddPlucker.interiorEmb n).comp
        (insertGapOrderEmb cols i hgap)) := by
  have hbig := bigPJ_gap_diagonalSupported S rows cols hsupp hsuper i hgap
  have hrest := hbig.comp (OddPlucker.topEmb n)
  simpa [OddPlucker.interiorEmb, OddPlucker.topEmb] using hrest

/-- The column-gap step with all five branch-support facts discharged from
the target diagonal and the absence of a northeast shadow zero. -/
theorem columnGap_plucker_step_of_superdiag_pos
    {r c n : Nat} {A : Matrix (Fin r) (Fin c) ℝ}
    (S : MonotoneColumnIntervalSupport A)
    (rows : Fin (n + 2) ↪o Fin r) (cols : Fin (n + 2) ↪o Fin c)
    (hsupp : DiagonalSupported S rows cols)
    (hsuper : ∀ t : Fin (n + 1),
      0 < A (rows t.castSucc) (cols t.succ))
    (i : Fin (n + 1))
    (hgap : (cols i.castSucc : Nat) + 1 < (cols i.succ : Nat))
    (hLower : ∀ l : Nat, l < n + 2 →
      ∀ (subRows : Fin l ↪o Fin r) (subCols : Fin l ↪o Fin c),
        DiagonalSupported S subRows subCols →
          0 < matrixMinor A subRows subCols)
    (hSame : ∀ (subCols : Fin (n + 2) ↪o Fin c),
      embeddingDispersion subCols < embeddingDispersion cols →
      DiagonalSupported S rows subCols →
        0 < matrixMinor A rows subCols) :
    0 < matrixMinor A rows cols := by
  apply columnGap_plucker_step S rows cols i hgap
  · exact common_gap_diagonalSupported S rows cols hsupp i hgap
  · exact den_gap_diagonalSupported S rows cols hsupp hsuper i hgap
  · exact smallJOne_gap_diagonalSupported S rows cols hsupp i hgap
  · exact bigPJ_gap_diagonalSupported S rows cols hsupp hsuper i hgap
  · exact smallJLast_gap_diagonalSupported S rows cols hsuper i hgap
  · exact hLower
  · exact hSame

/-! ### Dynamic proper-factorization branches -/

/-- A selected northeast zero at an arbitrary cut closes the target from the
strictly lower-order induction hypothesis.  The proof transports the dynamic
cut to the explicit positive block sizes consumed by the factorization
theorem and transports the determinant back without a permutation sign. -/
theorem superdiag_zero_lower_order_step
    {r c n : Nat} {A : Matrix (Fin r) (Fin c) ℝ}
    (S : MonotoneColumnIntervalSupport A)
    (rows : Fin (n + 2) ↪o Fin r) (cols : Fin (n + 2) ↪o Fin c)
    (hsupp : DiagonalSupported S rows cols)
    (t : Fin (n + 1))
    (hzero : A (rows t.castSucc) (cols t.succ) = 0)
    (hLower : ∀ l : Nat, l < n + 2 →
      ∀ (subRows : Fin l ↪o Fin r) (subCols : Fin l ↪o Fin c),
        DiagonalSupported S subRows subCols →
          0 < matrixMinor A subRows subCols) :
    0 < matrixMinor A rows cols := by
  let a : Nat := t
  let b : Nat := n - t
  have hsize : (a + 1) + (b + 1) = n + 2 := by
    dsimp [a, b]
    omega
  let cast : Fin ((a + 1) + (b + 1)) ≃o Fin (n + 2) :=
    Fin.castOrderIso hsize
  let rows' : Fin ((a + 1) + (b + 1)) ↪o Fin r :=
    cast.toOrderEmbedding.comp rows
  let cols' : Fin ((a + 1) + (b + 1)) ↪o Fin c :=
    cast.toOrderEmbedding.comp cols
  have hsupp' : DiagonalSupported S rows' cols' :=
    hsupp.comp cast.toOrderEmbedding
  have hleft : cast (Fin.castAdd (b + 1) (Fin.last a)) = t.castSucc := by
    apply Fin.ext
    simp [cast, a, b]
  have hright : cast (Fin.natAdd (a + 1) (0 : Fin (b + 1))) = t.succ := by
    apply Fin.ext
    simp [cast, a, b]
  have hcross : A
      (rows' (Fin.castAdd (b + 1) (Fin.last a)))
      (cols' (Fin.natAdd (a + 1) (0 : Fin (b + 1)))) = 0 := by
    simpa [rows', cols', hleft, hright] using hzero
  have hpos : 0 < matrixMinor A rows' cols' := by
    apply matrixMinor_pos_of_supported_cross_zero_of_lower_order
      S rows' cols' hsupp' hcross
    intro l hl subRows subCols hsub
    apply hLower l
    · simpa [hsize] using hl
    · exact hsub
  rw [matrixMinor] at hpos ⊢
  have hdet := Matrix.det_submatrix_equiv_self cast.toEquiv
    (A.submatrix rows cols)
  rw [← hdet]
  simpa [rows', cols', Matrix.submatrix_submatrix] using hpos

/-- The algebraic lower-left analogue of
`matrixMinor_eq_mul_of_upperRight_zero`, obtained by transposing the selected
matrix. -/
theorem matrixMinor_eq_mul_of_lowerLeft_zero
    {r c a b : Nat} (A : Matrix (Fin r) (Fin c) ℝ)
    (rows : Fin (a + b) ↪o Fin r) (cols : Fin (a + b) ↪o Fin c)
    (hzero : ∀ i : Fin b, ∀ j : Fin a,
      A (rows (Fin.natAdd a i)) (cols (Fin.castAdd b j)) = 0) :
    matrixMinor A rows cols =
      matrixMinor A (prefixOrderEmb rows) (prefixOrderEmb cols) *
      matrixMinor A (suffixOrderEmb rows) (suffixOrderEmb cols) := by
  have h := matrixMinor_eq_mul_of_upperRight_zero A.transpose cols rows
    (fun j i ↦ hzero i j)
  simpa only [matrixMinor_transpose] using h

/-- A supported selected subdiagonal zero propagates to the complete
lower-left block and yields a sign-free factorization. -/
theorem matrixMinor_eq_mul_of_supported_subdiag_zero
    {r c a b : Nat} {A : Matrix (Fin r) (Fin c) ℝ}
    (S : MonotoneColumnIntervalSupport A)
    (rows : Fin ((a + 1) + (b + 1)) ↪o Fin r)
    (cols : Fin ((a + 1) + (b + 1)) ↪o Fin c)
    (hsupp : DiagonalSupported S rows cols)
    (hcross : A
      (rows (Fin.natAdd (a + 1) (0 : Fin (b + 1))))
      (cols (Fin.castAdd (b + 1) (Fin.last a))) = 0) :
    matrixMinor A rows cols =
      matrixMinor A (prefixOrderEmb rows) (prefixOrderEmb cols) *
      matrixMinor A (suffixOrderEmb rows) (suffixOrderEmb cols) := by
  have hindex :
      (Fin.castAdd (b + 1) (Fin.last a) : Fin ((a + 1) + (b + 1))) <
        Fin.natAdd (a + 1) (0 : Fin (b + 1)) := by
    change a < a + 1
    omega
  have hbelow : S.hi (cols (Fin.castAdd (b + 1) (Fin.last a))) <
      rows (Fin.natAdd (a + 1) (0 : Fin (b + 1))) := by
    by_contra h
    have hhi : S.hi (cols (Fin.castAdd (b + 1) (Fin.last a))) ≥
        rows (Fin.natAdd (a + 1) (0 : Fin (b + 1))) := le_of_not_gt h
    have hlo : S.lo (cols (Fin.castAdd (b + 1) (Fin.last a))) ≤
        rows (Fin.natAdd (a + 1) (0 : Fin (b + 1))) :=
      le_trans (hsupp _).1 (rows.monotone (le_of_lt hindex))
    exact (ne_of_gt (S.entry_pos _ _ hlo hhi)) hcross
  apply matrixMinor_eq_mul_of_lowerLeft_zero A rows cols
  intro i j
  apply S.entry_zero
  right
  exact lt_of_le_of_lt
    (S.hi_mono (cols.monotone (by
      change (j : Nat) ≤ a
      omega)))
    (lt_of_lt_of_le hbelow (rows.monotone (by
      change a + 1 ≤ a + 1 + (i : Nat)
      omega)))

/-- Lower-left factorization packaged for the strict outer induction. -/
theorem matrixMinor_pos_of_supported_subdiag_zero_of_lower_order
    {r c a b : Nat} {A : Matrix (Fin r) (Fin c) ℝ}
    (S : MonotoneColumnIntervalSupport A)
    (rows : Fin ((a + 1) + (b + 1)) ↪o Fin r)
    (cols : Fin ((a + 1) + (b + 1)) ↪o Fin c)
    (hsupp : DiagonalSupported S rows cols)
    (hcross : A
      (rows (Fin.natAdd (a + 1) (0 : Fin (b + 1))))
      (cols (Fin.castAdd (b + 1) (Fin.last a))) = 0)
    (hIH : ∀ l : Nat, l < (a + 1) + (b + 1) →
      ∀ (subRows : Fin l ↪o Fin r) (subCols : Fin l ↪o Fin c),
        DiagonalSupported S subRows subCols →
          0 < matrixMinor A subRows subCols) :
    0 < matrixMinor A rows cols := by
  obtain ⟨hfirst, hsecond⟩ := diagonalSupported_prefix_suffix hsupp
  obtain ⟨hfirstOrder, hsecondOrder⟩ := proper_split_orders a b
  rw [matrixMinor_eq_mul_of_supported_subdiag_zero S rows cols hsupp hcross]
  exact mul_pos (hIH (a + 1) hfirstOrder _ _ hfirst)
    (hIH (b + 1) hsecondOrder _ _ hsecond)

/-- A selected southwest zero at an arbitrary cut closes the target from the
strictly lower-order induction hypothesis. -/
theorem subdiag_zero_lower_order_step
    {r c n : Nat} {A : Matrix (Fin r) (Fin c) ℝ}
    (S : MonotoneColumnIntervalSupport A)
    (rows : Fin (n + 2) ↪o Fin r) (cols : Fin (n + 2) ↪o Fin c)
    (hsupp : DiagonalSupported S rows cols)
    (t : Fin (n + 1))
    (hzero : A (rows t.succ) (cols t.castSucc) = 0)
    (hLower : ∀ l : Nat, l < n + 2 →
      ∀ (subRows : Fin l ↪o Fin r) (subCols : Fin l ↪o Fin c),
        DiagonalSupported S subRows subCols →
          0 < matrixMinor A subRows subCols) :
    0 < matrixMinor A rows cols := by
  let a : Nat := t
  let b : Nat := n - t
  have hsize : (a + 1) + (b + 1) = n + 2 := by
    dsimp [a, b]
    omega
  let cast : Fin ((a + 1) + (b + 1)) ≃o Fin (n + 2) :=
    Fin.castOrderIso hsize
  let rows' : Fin ((a + 1) + (b + 1)) ↪o Fin r :=
    cast.toOrderEmbedding.comp rows
  let cols' : Fin ((a + 1) + (b + 1)) ↪o Fin c :=
    cast.toOrderEmbedding.comp cols
  have hsupp' : DiagonalSupported S rows' cols' :=
    hsupp.comp cast.toOrderEmbedding
  have hleft : cast (Fin.castAdd (b + 1) (Fin.last a)) = t.castSucc := by
    apply Fin.ext
    simp [cast, a, b]
  have hright : cast (Fin.natAdd (a + 1) (0 : Fin (b + 1))) = t.succ := by
    apply Fin.ext
    simp [cast, a, b]
  have hcross : A
      (rows' (Fin.natAdd (a + 1) (0 : Fin (b + 1))))
      (cols' (Fin.castAdd (b + 1) (Fin.last a))) = 0 := by
    simpa [rows', cols', hleft, hright] using hzero
  have hpos : 0 < matrixMinor A rows' cols' := by
    apply matrixMinor_pos_of_supported_subdiag_zero_of_lower_order
      S rows' cols' hsupp' hcross
    intro l hl subRows subCols hsub
    apply hLower l
    · simpa [hsize] using hl
    · exact hsub
  rw [matrixMinor] at hpos ⊢
  have hdet := Matrix.det_submatrix_equiv_self cast.toEquiv
    (A.submatrix rows cols)
  rw [← hdet]
  simpa [rows', cols', Matrix.submatrix_submatrix] using hpos

/-! ### The symmetric row-gap branch -/

/-- The natural Pluecker step for a row gap, obtained by feeding the
transpose of the extended selected matrix to the rectangular frame identity.
All recursive signs remain signs of minors of the original matrix and use the
original support structure. -/
theorem rowGap_plucker_step
    {r c n : Nat} {A : Matrix (Fin r) (Fin c) ℝ}
    (S : MonotoneColumnIntervalSupport A)
    (rows : Fin (n + 2) ↪o Fin r) (cols : Fin (n + 2) ↪o Fin c)
    (i : Fin (n + 1))
    (hgap : (rows i.castSucc : Nat) + 1 < (rows i.succ : Nat))
    (hDsup : DiagonalSupported S
      ((OddPlucker.commonColEmb (gapSlot i)).comp
        (insertGapOrderEmb rows i hgap))
      ((OddPlucker.middleEmb n).comp cols))
    (hdenSup : DiagonalSupported S
      ((OddPlucker.interiorEmb n).comp
        (insertGapOrderEmb rows i hgap))
      ((OddPlucker.topEmb n).comp cols))
    (hsmallSup : DiagonalSupported S
      ((OddPlucker.smallJOneEmb (gapSlot i) (by
        change (i : Nat) + 1 < n + 2
        omega)).comp (insertGapOrderEmb rows i hgap))
      ((OddPlucker.topEmb n).comp cols))
    (hbigSup : DiagonalSupported S
      ((Fin.succOrderEmb (n + 2)).comp
        (insertGapOrderEmb rows i hgap)) cols)
    (hcrossSmallSup : DiagonalSupported S
      ((OddPlucker.smallJLastEmb (gapSlot i)).comp
        (insertGapOrderEmb rows i hgap))
      ((OddPlucker.topEmb n).comp cols))
    (hLower : ∀ l : Nat, l < n + 2 →
      ∀ (subRows : Fin l ↪o Fin r) (subCols : Fin l ↪o Fin c),
        DiagonalSupported S subRows subCols →
          0 < matrixMinor A subRows subCols)
    (hSame : ∀ (subRows : Fin (n + 2) ↪o Fin r),
      embeddingDispersion subRows < embeddingDispersion rows →
      DiagonalSupported S subRows cols →
        0 < matrixMinor A subRows cols) :
    0 < matrixMinor A rows cols := by
  let p : Fin (n + 3) := gapSlot i
  let full : Fin (n + 3) ↪o Fin r := insertGapOrderEmb rows i hgap
  let X : Matrix (Fin (n + 2)) (Fin (n + 3)) ℝ :=
    (A.submatrix full cols).transpose
  have hp0 : (0 : Fin (n + 3)) < p := by
    change 0 < (i : Nat) + 1
    omega
  have hpLast : p < Fin.last (n + 2) := by
    change (i : Nat) + 1 < n + 2
    omega
  have hDpos : 0 < (X.submatrix (OddPlucker.middleEmb n)
      (OddPlucker.commonColEmb p)).det := by
    have hpos := hLower n (by omega)
      ((OddPlucker.commonColEmb p).comp full)
      ((OddPlucker.middleEmb n).comp cols) hDsup
    rw [matrixMinor] at hpos
    rw [← Matrix.det_transpose] at hpos
    simpa [X, Matrix.submatrix_submatrix] using hpos
  have hden : 0 < OddPlucker.denMinor X := by
    have hpos := hLower (n + 1) (by omega)
      ((OddPlucker.interiorEmb n).comp full)
      ((OddPlucker.topEmb n).comp cols) hdenSup
    rw [matrixMinor] at hpos
    rw [← Matrix.det_transpose] at hpos
    simpa [OddPlucker.denMinor, X, Matrix.submatrix_submatrix] using hpos
  have hsmall : 0 < OddPlucker.smallJOneMinor X p hpLast := by
    have hpos := hLower (n + 1) (by omega)
      ((OddPlucker.smallJOneEmb p hpLast).comp full)
      ((OddPlucker.topEmb n).comp cols) hsmallSup
    rw [matrixMinor] at hpos
    rw [← Matrix.det_transpose] at hpos
    simpa [OddPlucker.smallJOneMinor, X, Matrix.submatrix_submatrix] using hpos
  have hbig : 0 < OddPlucker.bigPJLastMinor X := by
    let bigRows := (Fin.succOrderEmb (n + 2)).comp full
    have hpos := hSame bigRows
      (by simpa [bigRows, full] using
        dropFirst_insertGap_dispersion_lt rows i hgap) hbigSup
    rw [matrixMinor] at hpos
    rw [← Matrix.det_transpose] at hpos
    simpa [OddPlucker.bigPJLastMinor, X, bigRows,
      Matrix.submatrix_submatrix] using hpos
  have hcrossSmall : 0 ≤ OddPlucker.smallJLastMinor X p := by
    have hpos := hLower (n + 1) (by omega)
      ((OddPlucker.smallJLastEmb p).comp full)
      ((OddPlucker.topEmb n).comp cols) hcrossSmallSup
    rw [matrixMinor] at hpos
    rw [← Matrix.det_transpose] at hpos
    simpa [OddPlucker.smallJLastMinor, X,
      Matrix.submatrix_submatrix] using hpos.le
  have hcrossBig : 0 ≤ OddPlucker.bigJOnePMinor X := by
    let crossRows : Fin (n + 2) ↪o Fin r :=
      (Fin.castAddOrderEmb 1).comp full
    by_cases hs : DiagonalSupported S crossRows cols
    · have hpos : 0 < matrixMinor A crossRows cols :=
        hSame crossRows (by
          simpa [crossRows, full] using
            dropLast_insertGap_dispersion_lt rows i hgap) hs
      rw [matrixMinor] at hpos
      rw [← Matrix.det_transpose] at hpos
      simpa [OddPlucker.bigJOnePMinor, X, crossRows,
        Matrix.submatrix_submatrix] using hpos.le
    · have hz := matrixMinor_eq_zero_of_not_diagonalSupported S crossRows cols hs
      rw [matrixMinor] at hz
      rw [← Matrix.det_transpose] at hz
      change 0 ≤ (X.submatrix id (OddPlucker.prefixEmb n)).det
      change 0 ≤ (A.submatrix
        ((OddPlucker.prefixEmb n).comp full) cols).transpose.det
      have heq : (OddPlucker.prefixEmb n).comp full = crossRows := by rfl
      rw [heq, hz]
  have htarget : 0 < OddPlucker.targetMinor X p :=
    OddPlucker.natural_plucker_target_pos X p hp0 hpLast hDpos.ne'
      hden hsmall hbig hcrossSmall hcrossBig
  change 0 < ((A.submatrix full cols).transpose.submatrix id
    (gapSlot i).succAboveOrderEmb).det at htarget
  rw [← Matrix.det_transpose] at htarget
  change 0 < matrixMinor A ((gapSlot i).succAboveOrderEmb.comp full) cols at htarget
  rw [show (gapSlot i).succAboveOrderEmb.comp full = rows by
    simpa [full] using insertGapOrderEmb_erase rows i hgap] at htarget
  exact htarget

/-- The row version of the first Pluecker big branch is supported when every
selected subdiagonal entry is positive.  At the inserted row, both bounding
selected rows already lie in the same fixed column interval. -/
theorem bigRowGap_diagonalSupported
    {r c n : Nat} {A : Matrix (Fin r) (Fin c) ℝ}
    (S : MonotoneColumnIntervalSupport A)
    (rows : Fin (n + 2) ↪o Fin r) (cols : Fin (n + 2) ↪o Fin c)
    (hsupp : DiagonalSupported S rows cols)
    (hsub : ∀ t : Fin (n + 1),
      0 < A (rows t.succ) (cols t.castSucc))
    (i : Fin (n + 1))
    (hgap : (rows i.castSucc : Nat) + 1 < (rows i.succ : Nat)) :
    DiagonalSupported S
      ((Fin.succOrderEmb (n + 2)).comp (insertGapOrderEmb rows i hgap)) cols := by
  intro t
  apply support_mem_of_entry_pos S
  let full := insertGapOrderEmb rows i hgap
  by_cases hti : (t : Nat) < (i : Nat)
  · let u : Fin (n + 1) := ⟨t, by omega⟩
    have htcast : u.castSucc = t := by ext; rfl
    have hidx : (gapSlot i).succAbove u.succ = t.succ := by
      apply Fin.ext
      rw [Fin.succAbove_of_castSucc_lt]
      · rfl
      · change (t : Nat) + 1 < (i : Nat) + 1
        omega
    have hrow : full t.succ = rows u.succ := by
      rw [← hidx]
      exact insertGapOrderEmb_apply_succAbove rows i hgap u.succ
    change 0 < A (full t.succ) (cols t)
    rw [hrow, ← htcast]
    exact hsub u
  · by_cases htiEq : (t : Nat) = (i : Nat)
    · have ht : t = i.castSucc := by ext; exact htiEq
      subst t
      have hrow : full i.castSucc.succ = gapValue rows i hgap := by
        have hslot : i.castSucc.succ = gapSlot i := rfl
        rw [hslot, insertGapOrderEmb_apply_gapSlot]
      change 0 < A (full i.castSucc.succ) (cols i.castSucc)
      rw [hrow]
      apply S.entry_pos
      · exact le_trans (hsupp i.castSucc).1 (by
          change (rows i.castSucc : Nat) ≤ (gapValue rows i hgap : Nat)
          simp [gapValue])
      · exact le_trans (by
          change (gapValue rows i hgap : Nat) ≤ (rows i.succ : Nat)
          simp [gapValue]) (support_mem_of_entry_pos S (hsub i)).2
    · have hit : (i : Nat) < (t : Nat) := by omega
      have hidx : (gapSlot i).succAbove t = t.succ := by
        apply Fin.ext
        rw [Fin.succAbove_of_le_castSucc]
        change (i : Nat) + 1 ≤ (t : Nat)
        omega
      have hrow : full t.succ = rows t := by
        rw [← hidx]
        exact insertGapOrderEmb_apply_succAbove rows i hgap t
      change 0 < A (full t.succ) (cols t)
      rw [hrow]
      exact hsupp.entry_pos t

/-- The row-gap step with all branch-support premises discharged from the
target diagonal and a positive selected subdiagonal. -/
theorem rowGap_plucker_step_of_subdiag_pos
    {r c n : Nat} {A : Matrix (Fin r) (Fin c) ℝ}
    (S : MonotoneColumnIntervalSupport A)
    (rows : Fin (n + 2) ↪o Fin r) (cols : Fin (n + 2) ↪o Fin c)
    (hsupp : DiagonalSupported S rows cols)
    (hsub : ∀ t : Fin (n + 1),
      0 < A (rows t.succ) (cols t.castSucc))
    (i : Fin (n + 1))
    (hgap : (rows i.castSucc : Nat) + 1 < (rows i.succ : Nat))
    (hLower : ∀ l : Nat, l < n + 2 →
      ∀ (subRows : Fin l ↪o Fin r) (subCols : Fin l ↪o Fin c),
        DiagonalSupported S subRows subCols →
          0 < matrixMinor A subRows subCols)
    (hSame : ∀ (subRows : Fin (n + 2) ↪o Fin r),
      embeddingDispersion subRows < embeddingDispersion rows →
      DiagonalSupported S subRows cols →
        0 < matrixMinor A subRows cols) :
    0 < matrixMinor A rows cols := by
  have hD : DiagonalSupported S
      ((OddPlucker.commonColEmb (gapSlot i)).comp
        (insertGapOrderEmb rows i hgap))
      ((OddPlucker.middleEmb n).comp cols) := by
    rw [common_gap_cols_eq rows i hgap]
    exact hsupp.comp (OddPlucker.middleEmb n)
  have hsmall : DiagonalSupported S
      ((OddPlucker.smallJOneEmb (gapSlot i) (by
        change (i : Nat) + 1 < n + 2
        omega)).comp (insertGapOrderEmb rows i hgap))
      ((OddPlucker.topEmb n).comp cols) := by
    rw [smallJOne_gap_cols_eq rows i hgap]
    exact hsupp.comp (OddPlucker.topEmb n)
  have hcrossSmall : DiagonalSupported S
      ((OddPlucker.smallJLastEmb (gapSlot i)).comp
        (insertGapOrderEmb rows i hgap))
      ((OddPlucker.topEmb n).comp cols) := by
    rw [smallJLast_gap_cols_eq rows i hgap]
    intro t
    apply support_mem_of_entry_pos S
    change 0 < A (rows t.succ) (cols t.castSucc)
    exact hsub t
  have hbig := bigRowGap_diagonalSupported S rows cols hsupp hsub i hgap
  have hden : DiagonalSupported S
      ((OddPlucker.interiorEmb n).comp (insertGapOrderEmb rows i hgap))
      ((OddPlucker.topEmb n).comp cols) := by
    have hrest := hbig.comp (OddPlucker.topEmb n)
    simpa [OddPlucker.interiorEmb, OddPlucker.topEmb] using hrest
  exact rowGap_plucker_step S rows cols i hgap hD hden hsmall hbig
    hcrossSmall hLower hSame

/-- A positive total dispersion exposes a concrete row or column gap. -/
theorem hasAdjacentGap_of_total_dispersion_pos
    {k r c : Nat} (rows : Fin (k + 1) ↪o Fin r)
    (cols : Fin (k + 1) ↪o Fin c)
    (hdisp : 0 < embeddingDispersion rows + embeddingDispersion cols) :
    HasAdjacentGap rows ∨ HasAdjacentGap cols := by
  by_contra h
  rw [not_or] at h
  have hr := (embeddingDispersion_eq_zero_iff rows).mpr h.1
  have hc := (embeddingDispersion_eq_zero_iff cols).mpr h.2
  omega

/-- If an increasing nonempty selection has no adjacent gap, it is literally
one of the consecutive embeddings used by `SupportedSolidMinorsPositive`.
This is the exact bridge from the dispersion-zero induction case to the
solid-minor hypothesis. -/
theorem eq_intervalOrderEmb_of_not_hasAdjacentGap {k n : Nat}
    (e : Fin (k + 1) ↪o Fin n) (hgap : ¬ HasAdjacentGap e) :
    ∃ (start : Nat) (h : start + (k + 1) ≤ n),
      e = intervalOrderEmb start h := by
  have hstep (i : Fin k) :
      (e i.succ : Nat) = (e i.castSucc : Nat) + 1 := by
    have hlo : (e i.castSucc : Nat) + 1 ≤ (e i.succ : Nat) := by
      have := e.strictMono (Fin.castSucc_lt_succ (i := i))
      exact this
    have hhi : (e i.succ : Nat) ≤ (e i.castSucc : Nat) + 1 := by
      exact le_of_not_gt (fun h ↦ hgap ⟨i, h⟩)
    omega
  have hval (i : Fin (k + 1)) :
      (e i : Nat) = (e 0 : Nat) + (i : Nat) := by
    induction i using Fin.induction with
    | zero => simp
    | succ i ih =>
        calc
          (e i.succ : Nat) = (e i.castSucc : Nat) + 1 := hstep i
          _ = ((e 0 : Nat) + (i.castSucc : Nat)) + 1 := by rw [ih]
          _ = (e 0 : Nat) + (i.succ : Nat) := by
            simp only [Fin.val_succ, Fin.val_castSucc]
            omega
  let start : Nat := (e 0 : Nat)
  have hbound : start + (k + 1) ≤ n := by
    have hlast := (e (Fin.last k)).isLt
    rw [hval] at hlast
    change start + (k + 1) ≤ n
    change start + k < n at hlast
    omega
  refine ⟨start, hbound, ?_⟩
  ext i
  rw [intervalOrderEmb_val, hval]

/-- Exact dichotomy used by the inner dispersion induction: a nonempty
increasing selection is consecutive or exposes an adjacent gap. -/
theorem hasAdjacentGap_or_eq_intervalOrderEmb {k n : Nat}
    (e : Fin (k + 1) ↪o Fin n) :
    HasAdjacentGap e ∨
      ∃ (start : Nat) (h : start + (k + 1) ≤ n),
        e = intervalOrderEmb start h := by
  by_cases h : HasAdjacentGap e
  · exact Or.inl h
  · exact Or.inr (eq_intervalOrderEmb_of_not_hasAdjacentGap e h)

/-- The dispersion-zero leaf of staircase promotion closes using only the
stated supported-solid-minor hypothesis. -/
theorem matrixMinor_pos_of_no_adjacent_gaps
    {r c k : Nat} {A : Matrix (Fin r) (Fin c) ℝ}
    (S : MonotoneColumnIntervalSupport A)
    (hsolid : SupportedSolidMinorsPositive S)
    (rows : Fin (k + 1) ↪o Fin r) (cols : Fin (k + 1) ↪o Fin c)
    (hsupp : DiagonalSupported S rows cols)
    (hrows : ¬ HasAdjacentGap rows) (hcols : ¬ HasAdjacentGap cols) :
    0 < matrixMinor A rows cols := by
  obtain ⟨rowStart, hrow, rfl⟩ :=
    eq_intervalOrderEmb_of_not_hasAdjacentGap rows hrows
  obtain ⟨colStart, hcol, rfl⟩ :=
    eq_intervalOrderEmb_of_not_hasAdjacentGap cols hcols
  exact hsolid (k + 1) rowStart colStart hrow hcol hsupp

/-- The zero leaf stated directly in the strict inner-induction measure. -/
theorem matrixMinor_pos_of_zero_total_dispersion
    {r c k : Nat} {A : Matrix (Fin r) (Fin c) ℝ}
    (S : MonotoneColumnIntervalSupport A)
    (hsolid : SupportedSolidMinorsPositive S)
    (rows : Fin (k + 1) ↪o Fin r) (cols : Fin (k + 1) ↪o Fin c)
    (hsupp : DiagonalSupported S rows cols)
    (hdisp : embeddingDispersion rows + embeddingDispersion cols = 0) :
    0 < matrixMinor A rows cols := by
  rw [Nat.add_eq_zero_iff] at hdisp
  exact matrixMinor_pos_of_no_adjacent_gaps S hsolid rows cols hsupp
    ((embeddingDispersion_eq_zero_iff rows).mp hdisp.1)
    ((embeddingDispersion_eq_zero_iff cols).mp hdisp.2)

/-! ## Generalized staircase--Fekete promotion -/

/-- Every supported naturally ordered minor is strictly positive when all
supported solid minors are positive.

The outer strong induction is on minor order.  At fixed positive order, the
inner strong induction is on total row-plus-column dispersion.  Northeast or
southwest support zeros factor the target into two strictly lower-order
supported minors.  Otherwise a column gap, or symmetrically a row gap, is
closed by the subtraction-free natural Pluecker relation; its two same-order
large minors have strictly smaller dispersion.  Dispersion zero is exactly
the solid-minor hypothesis.
-/
theorem matrixMinor_pos_of_diagonalSupported
    {r c k : Nat} {A : Matrix (Fin r) (Fin c) ℝ}
    (S : MonotoneColumnIntervalSupport A)
    (hsolid : SupportedSolidMinorsPositive S)
    (rows : Fin k ↪o Fin r) (cols : Fin k ↪o Fin c)
    (hsupp : DiagonalSupported S rows cols) :
    0 < matrixMinor A rows cols := by
  induction k using Nat.strong_induction_on with
  | h k orderIH =>
      cases k with
      | zero => exact matrixMinor_pos_zero A rows cols
      | succ k =>
          cases k with
          | zero => exact matrixMinor_pos_one_of_diagonalSupported S rows cols hsupp
          | succ n =>
              let P : Nat → Prop := fun d ↦
                ∀ (subRows : Fin (n + 2) ↪o Fin r)
                  (subCols : Fin (n + 2) ↪o Fin c),
                  embeddingDispersion subRows + embeddingDispersion subCols = d →
                  DiagonalSupported S subRows subCols →
                    0 < matrixMinor A subRows subCols
              have hP : P (embeddingDispersion rows + embeddingDispersion cols) := by
                refine Nat.strong_induction_on (p := P)
                  (embeddingDispersion rows + embeddingDispersion cols) ?_
                intro d dispIH subRows subCols hd hsubSupp
                by_cases hsuperZero : ∃ t : Fin (n + 1),
                    A (subRows t.castSucc) (subCols t.succ) = 0
                · obtain ⟨t, ht⟩ := hsuperZero
                  apply superdiag_zero_lower_order_step S subRows subCols hsubSupp t ht
                  intro l hl lowerRows lowerCols hlowerSupp
                  exact orderIH l (by omega) lowerRows lowerCols hlowerSupp
                · have hsuper : ∀ t : Fin (n + 1),
                      0 < A (subRows t.castSucc) (subCols t.succ) := by
                    intro t
                    exact lt_of_le_of_ne (S.entry_nonneg _ _)
                      (Ne.symm (fun hz ↦ hsuperZero ⟨t, hz⟩))
                  by_cases hcolGap : HasAdjacentGap subCols
                  · obtain ⟨i, hi⟩ := hcolGap
                    apply columnGap_plucker_step_of_superdiag_pos S subRows subCols
                      hsubSupp hsuper i hi
                    · intro l hl lowerRows lowerCols hlowerSupp
                      exact orderIH l (by omega) lowerRows lowerCols hlowerSupp
                    · intro smallerCols hlt hsmallerSupp
                      exact dispIH
                        (embeddingDispersion subRows + embeddingDispersion smallerCols)
                        (by omega) subRows smallerCols rfl hsmallerSupp
                  · by_cases hrowGap : HasAdjacentGap subRows
                    · obtain ⟨i, hi⟩ := hrowGap
                      by_cases hsubZero : ∃ t : Fin (n + 1),
                          A (subRows t.succ) (subCols t.castSucc) = 0
                      · obtain ⟨t, ht⟩ := hsubZero
                        apply subdiag_zero_lower_order_step S subRows subCols
                          hsubSupp t ht
                        intro l hl lowerRows lowerCols hlowerSupp
                        exact orderIH l (by omega) lowerRows lowerCols hlowerSupp
                      · have hsubdiag : ∀ t : Fin (n + 1),
                            0 < A (subRows t.succ) (subCols t.castSucc) := by
                          intro t
                          exact lt_of_le_of_ne (S.entry_nonneg _ _)
                            (Ne.symm (fun hz ↦ hsubZero ⟨t, hz⟩))
                        apply rowGap_plucker_step_of_subdiag_pos S subRows subCols
                          hsubSupp hsubdiag i hi
                        · intro l hl lowerRows lowerCols hlowerSupp
                          exact orderIH l (by omega) lowerRows lowerCols hlowerSupp
                        · intro smallerRows hlt hsmallerSupp
                          exact dispIH
                            (embeddingDispersion smallerRows + embeddingDispersion subCols)
                            (by omega) smallerRows subCols rfl hsmallerSupp
                    · exact matrixMinor_pos_of_no_adjacent_gaps S hsolid
                        subRows subCols hsubSupp hrowGap hcolGap
              exact hP rows cols rfl hsupp

/-- Generalized staircase--Fekete recognition: positive supported solid
minors promote to total nonnegativity.  Unsupported minors vanish by the Hall
obstruction, while supported minors are strictly positive by the theorem
above. -/
theorem isTotallyNonnegative_of_supportedSolidMinorsPositive
    {r c : Nat} {A : Matrix (Fin r) (Fin c) ℝ}
    (S : MonotoneColumnIntervalSupport A)
    (hsolid : SupportedSolidMinorsPositive S) :
    IsTotallyNonnegative A := by
  intro k rows cols
  by_cases hsupp : DiagonalSupported S rows cols
  · exact (matrixMinor_pos_of_diagonalSupported S hsolid rows cols hsupp).le
  · rw [matrixMinor_eq_zero_of_not_diagonalSupported S rows cols hsupp]

end ColomboGeneralK2.Odd
