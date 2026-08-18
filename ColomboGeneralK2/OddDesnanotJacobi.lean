import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Desnanot--Jacobi condensation for the large-seam step

This file isolates the determinant identity used in the large-seam
condensation argument.  The matrix is written with its two distinguished
boundary rows and columns first and its arbitrary finite middle block last.
The four `border` matrices are literally the four one-row/one-column
deletions, after this common reindexing.

The hypothesis `[Invertible D]` is exactly the nonzero-middle-minor condition
needed by Dodgson condensation over a field.  It is sufficient for the
positive large-seam application, where that middle minor is positive.
-/

namespace ColomboGeneralK2

namespace OddDesnanotJacobi

open Matrix

variable {R : Type*} [CommRing R]

/-- The `(n+1) x (n+1)` bordered matrix obtained after deleting one of the two
distinguished rows and one of the two distinguished columns. -/
def border {n : Nat} (a : R) (b : Fin n → R) (c : Fin n → R)
    (D : Matrix (Fin n) (Fin n) R) : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) R :=
  Matrix.fromBlocks (fun _ _ => a) (fun _ j => b j) (fun i _ => c i) D

/-- The four bordered determinants satisfy Desnanot--Jacobi, at every middle
dimension.  The order of the cross term is explicit: top-right times
bottom-left is subtracted. -/
theorem desnanot_jacobi_border {n : Nat}
    (A : Matrix (Fin 2) (Fin 2) R)
    (B : Matrix (Fin 2) (Fin n) R)
    (C : Matrix (Fin n) (Fin 2) R)
    (D : Matrix (Fin n) (Fin n) R) [Invertible D] :
    (Matrix.fromBlocks A B C D).det * D.det =
      (border (A 0 0) (B 0) (fun i => C i 0) D).det *
          (border (A 1 1) (B 1) (fun i => C i 1) D).det -
        (border (A 0 1) (B 0) (fun i => C i 1) D).det *
          (border (A 1 0) (B 1) (fun i => C i 0) D).det := by
  let S : Matrix (Fin 2) (Fin 2) R := A - B * ⅟D * C
  have hmain : (Matrix.fromBlocks A B C D).det = D.det * S.det := by
    simpa [S] using Matrix.det_fromBlocks₂₂ A B C D
  have h00 : (border (A 0 0) (B 0) (fun i => C i 0) D).det = D.det * S 0 0 := by
    rw [border, Matrix.det_fromBlocks₂₂]
    apply congrArg (fun x => D.det * x)
    rw [Matrix.det_unique]
    simp only [S, Matrix.sub_apply, Matrix.mul_apply]
  have h11 : (border (A 1 1) (B 1) (fun i => C i 1) D).det = D.det * S 1 1 := by
    rw [border, Matrix.det_fromBlocks₂₂]
    apply congrArg (fun x => D.det * x)
    rw [Matrix.det_unique]
    simp only [S, Matrix.sub_apply, Matrix.mul_apply]
  have h01 : (border (A 0 1) (B 0) (fun i => C i 1) D).det = D.det * S 0 1 := by
    rw [border, Matrix.det_fromBlocks₂₂]
    apply congrArg (fun x => D.det * x)
    rw [Matrix.det_unique]
    simp only [S, Matrix.sub_apply, Matrix.mul_apply]
  have h10 : (border (A 1 0) (B 1) (fun i => C i 0) D).det = D.det * S 1 0 := by
    rw [border, Matrix.det_fromBlocks₂₂]
    apply congrArg (fun x => D.det * x)
    rw [Matrix.det_unique]
    simp only [S, Matrix.sub_apply, Matrix.mul_apply]
  rw [hmain, h00, h11, h01, h10, Matrix.det_fin_two]
  ring

/-- Field-valued interface for condensation applications: a nonzero middle
determinant supplies the invertibility instance required by the Schur
complement proof. -/
theorem desnanot_jacobi_border_field {K : Type*} [Field K] {n : Nat}
    (A : Matrix (Fin 2) (Fin 2) K)
    (B : Matrix (Fin 2) (Fin n) K)
    (C : Matrix (Fin n) (Fin 2) K)
    (D : Matrix (Fin n) (Fin n) K) (hD : D.det ≠ 0) :
    (Matrix.fromBlocks A B C D).det * D.det =
      (border (A 0 0) (B 0) (fun i => C i 0) D).det *
          (border (A 1 1) (B 1) (fun i => C i 1) D).det -
        (border (A 0 1) (B 0) (fun i => C i 1) D).det *
          (border (A 1 0) (B 1) (fun i => C i 0) D).det := by
  letI : Invertible D.det := invertibleOfNonzero hD
  letI : Invertible D := Matrix.invertibleOfDetInvertible D
  exact desnanot_jacobi_border A B C D

end OddDesnanotJacobi

end ColomboGeneralK2
