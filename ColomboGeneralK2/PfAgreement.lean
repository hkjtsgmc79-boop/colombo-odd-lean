import ColomboGeneralK2.GeneralADMS
import Mathlib.Data.List.FinRange

/-!
# Agreement of the two recursive Pfaffians

`localPf` recurses over an explicitly ordered list of rows, while
`recursivePf` is the canonical-row recursion used by the general
anti-diagonal minor-summation theorem.  This module proves that they agree on
`Fin (2 * m)` with the canonical order `List.ofFn id`.

The proof also records the small fuel, reindexing, and `eraseIdx` lemmas needed
to pass from the list recursion to the canonical matrix recursion.  No
skew-symmetry hypothesis is needed.
-/

namespace ColomboGeneralK2

variable {R I J : Type*} [CommRing R]

/-- Once the fuel is at least the list length, adding one unit of fuel does
not change `localPfAux`. -/
theorem localPfAux_stable (A : I → I → R) (is : List I) (n : Nat)
    (h : is.length ≤ n) :
    localPfAux A (n + 1) is = localPfAux A n is := by
  induction n generalizing is with
  | zero =>
      cases is with
      | nil => rfl
      | cons i is => simp at h
  | succ n ih =>
      cases is with
      | nil => rfl
      | cons i is =>
          have htail : is.length ≤ n := by simpa using h
          simp only [localPfAux]
          apply Finset.sum_congr rfl
          intro k hk
          congr 1
          apply ih
          have herase := List.length_eraseIdx_add_one k.isLt
          omega

/-- The sufficient-fuel wrapper exposes its first-row recursion. -/
theorem localPf_cons (A : I → I → R) (i : I) (is : List I) :
    localPf A (i :: is) =
      ∑ k : Fin is.length,
        (-1 : R) ^ (k : Nat) * A i (is.get k) * localPf A (is.eraseIdx k) := by
  simp only [localPf, localPfAux]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  calc
    localPfAux A is.length (is.eraseIdx k) =
        localPfAux A ((is.eraseIdx k).length + 1) (is.eraseIdx k) := by
      rw [List.length_eraseIdx_add_one k.isLt]
    _ = localPfAux A (is.eraseIdx k).length (is.eraseIdx k) :=
      localPfAux_stable A _ _ (by rfl)

/-- `localPfAux` is invariant under simultaneous reindexing of the matrix and
its explicit row list. -/
theorem localPfAux_map (A : I → I → R) (f : J → I) (fuel : Nat) (js : List J) :
    localPfAux A fuel (js.map f) =
      localPfAux (fun i j ↦ A (f i) (f j)) fuel js := by
  induction fuel generalizing js with
  | zero => cases js <;> rfl
  | succ fuel ih =>
      cases js with
      | nil => rfl
      | cons j js =>
          simp only [List.map_cons, localPfAux]
          let e : Fin (List.map f js).length ≃ Fin js.length :=
            finCongr (List.length_map f)
          rw [← e.sum_comp (fun x : Fin js.length ↦
            (-1 : R) ^ (x : Nat) * A (f j) (f (js.get x)) *
              localPfAux (fun i j ↦ A (f i) (f j)) fuel (js.eraseIdx x))]
          apply Fintype.sum_congr
          intro k
          simp only [e, finCongr_apply, List.get_eq_getElem,
            List.getElem_map, List.eraseIdx_map, ih]
          rfl

/-- The sufficient-fuel wrapper inherits simultaneous reindexing. -/
theorem localPf_map (A : I → I → R) (f : J → I) (js : List J) :
    localPf A (js.map f) =
      localPf (fun i j ↦ A (f i) (f j)) js := by
  simp only [localPf, List.length_map]
  exact localPfAux_map A f js.length js

/-- The canonical ordered list of a finite row type. -/
def canonicalRows (m : Nat) : List (Fin m) :=
  List.ofFn id

/-- Canonical rows begin with zero and continue with the successor rows. -/
theorem canonicalRows_succ (m : Nat) :
    canonicalRows (m + 1) =
      (0 : Fin (m + 1)) :: List.ofFn (fun row : Fin m ↦ Fin.succ row) := by
  simp [canonicalRows, List.ofFn_succ]

/-- Canonical rows at the next even size, in the form used by the Pfaffian
row recurrence. -/
theorem canonicalRows_even_cons (n : Nat) :
    (List.ofFn id : List (Fin (2 * (n + 1)))) =
      (0 : Fin (2 * (n + 1))) ::
        List.ofFn (fun row : Fin (2 * n + 1) ↦ Fin.succ row) := by
  simpa only [show 2 * (n + 1) = (2 * n + 1) + 1 by omega] using
    canonicalRows_succ (2 * n + 1)

/-- The `k`th member of the successor tail is the row `k.succ`. -/
theorem canonicalTail_get (n : Nat) (k : Fin (2 * n + 1)) :
    (List.ofFn (fun row : Fin (2 * n + 1) ↦
      (Fin.succ row : Fin (2 * (n + 1))))).get
        ⟨k, by simpa only [List.length_ofFn] using k.isLt⟩ = Fin.succ k := by
  rw [List.get_ofFn]
  rfl

/-- Erasing tail position `k` gives the canonical two-row-deletion
reindexing. -/
theorem canonicalTail_eraseIdx (n : Nat) (k : Fin (2 * n + 1)) :
    (List.ofFn (fun row : Fin (2 * n + 1) ↦
      (Fin.succ row : Fin (2 * (n + 1))))).eraseIdx k =
      List.ofFn (fun row : Fin (2 * n) ↦ Fin.succ (k.succAbove row)) := by
  apply List.ext_get
  · rw [List.length_eraseIdx_of_lt (by simpa using k.isLt)]
    simp
  · intro row hleft hright
    simp only [List.get_eq_getElem, List.getElem_eraseIdx, List.getElem_ofFn]
    ext
    simp only [Fin.succAbove, Fin.lt_def]
    split_ifs <;> simp_all

/-- The erased canonical list is `localPf` of the canonical two-row
submatrix. -/
theorem localPf_canonicalTail_eraseIdx {n : Nat}
    (A : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) R)
    (k : Fin (2 * n + 1)) :
    localPf A
        ((List.ofFn (fun row : Fin (2 * n + 1) ↦
          (Fin.succ row : Fin (2 * (n + 1))))).eraseIdx k) =
      localPf
        (A.submatrix (fun row ↦ Fin.succ (k.succAbove row))
          (fun col ↦ Fin.succ (k.succAbove col)))
        (List.ofFn id) := by
  rw [canonicalTail_eraseIdx]
  let f : Fin (2 * n) → Fin (2 * (n + 1)) :=
    fun row ↦ Fin.succ (k.succAbove row)
  have hrows :
      List.ofFn f = (List.ofFn id : List (Fin (2 * n))).map f := by
    simpa only [id_eq] using
      (List.ofFn_comp' (id : Fin (2 * n) → Fin (2 * n)) f)
  change localPf A (List.ofFn f) =
    localPf (fun row col ↦ A (f row) (f col)) (List.ofFn id)
  rw [hrows, localPf_map]

/-- `localPf` on canonical rows satisfies the same canonical matrix recurrence
as `recursivePf`. -/
theorem localPf_canonical_even_recurrence (n : Nat)
    (A : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) R) :
    localPf A (List.ofFn id) =
      ∑ k : Fin (2 * n + 1),
        (-1 : R) ^ (k : Nat) * A 0 (Fin.succ k) *
          localPf
            (A.submatrix (fun row ↦ Fin.succ (k.succAbove row))
              (fun col ↦ Fin.succ (k.succAbove col)))
            (List.ofFn id) := by
  rw [canonicalRows_even_cons, localPf_cons]
  let tail : List (Fin (2 * (n + 1))) :=
    List.ofFn (fun row : Fin (2 * n + 1) ↦ Fin.succ row)
  let e : Fin tail.length ≃ Fin (2 * n + 1) :=
    finCongr (by simp [tail])
  rw [← e.sum_comp (fun k : Fin (2 * n + 1) ↦
    (-1 : R) ^ (k : Nat) * A 0 (Fin.succ k) *
      localPf
        (A.submatrix (fun row ↦ Fin.succ (k.succAbove row))
          (fun col ↦ Fin.succ (k.succAbove col)))
        (List.ofFn id))]
  apply Fintype.sum_congr
  intro k
  change
    (-1 : R) ^ (k : Nat) * A 0 (tail.get k) * localPf A (tail.eraseIdx k) = _
  have hkval : (e k : Nat) = (k : Nat) := by
    simp [e, finCongr_apply]
  have hget : tail.get k = Fin.succ (e k) := by
    let k' : Fin tail.length :=
      ⟨e k, by simpa [tail] using (e k).isLt⟩
    have hkk : k = k' := by
      apply Fin.ext
      exact hkval.symm
    rw [hkk]
    simpa [tail] using canonicalTail_get n (e k)
  rw [hget]
  have herase : tail.eraseIdx (k : Nat) = tail.eraseIdx (e k : Nat) := by
    rw [hkval]
  rw [herase]
  rw [show (-1 : R) ^ (k : Nat) = (-1 : R) ^ (e k : Nat) by rw [hkval]]
  exact congrArg
    (fun x ↦ (-1 : R) ^ (e k : Nat) * A 0 (Fin.succ (e k)) * x)
    (localPf_canonicalTail_eraseIdx A (e k))

/-- The canonical matrix recursion and the explicit-list recursion define the
same Pfaffian on every even finite size. -/
theorem recursivePf_eq_localPf (m : Nat)
    (A : Matrix (Fin (2 * m)) (Fin (2 * m)) R) :
    recursivePf m A = localPf A (List.ofFn id) := by
  induction m with
  | zero => rfl
  | succ n ih =>
      rw [localPf_canonical_even_recurrence]
      simp only [recursivePf]
      apply Finset.sum_congr rfl
      intro k hk
      rw [ih]

end ColomboGeneralK2
