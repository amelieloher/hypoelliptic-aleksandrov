module

public import HypoellipticAleksandrov.Ambient.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Entrywise matrix contraction

This module defines the entrywise Frobenius contraction used by the
time--velocity operator and relates it to matrix trace when the second matrix
is symmetric.
-/

@[expose] public section

open scoped BigOperators

namespace HypoellipticAleksandrov

/-- The entrywise Frobenius contraction of two real square matrices. -/
def matrixContraction {d : ℕ} (A H : PDE.Mat d) : ℝ :=
  ∑ i, ∑ j, A i j * H i j

/-- The contraction with a zero left factor vanishes. -/
@[simp]
theorem matrixContraction_zero_left {d : ℕ} (H : PDE.Mat d) :
    matrixContraction 0 H = 0 := by
  simp [matrixContraction]

/-- The contraction with a zero right factor vanishes. -/
@[simp]
theorem matrixContraction_zero_right {d : ℕ} (A : PDE.Mat d) :
    matrixContraction A 0 = 0 := by
  simp [matrixContraction]

/-- The contraction is additive in its left factor. -/
@[simp]
theorem matrixContraction_add_left {d : ℕ} (A B H : PDE.Mat d) :
    matrixContraction (A + B) H =
      matrixContraction A H + matrixContraction B H := by
  simp [matrixContraction, add_mul, Finset.sum_add_distrib]

/-- The contraction is additive in its right factor. -/
@[simp]
theorem matrixContraction_add_right {d : ℕ} (A H K : PDE.Mat d) :
    matrixContraction A (H + K) =
      matrixContraction A H + matrixContraction A K := by
  simp [matrixContraction, mul_add, Finset.sum_add_distrib]

/-- The contraction is homogeneous in its left factor. -/
@[simp]
theorem matrixContraction_smul_left {d : ℕ} (c : ℝ) (A H : PDE.Mat d) :
    matrixContraction (c • A) H = c * matrixContraction A H := by
  simp [matrixContraction, smul_eq_mul, mul_assoc, Finset.mul_sum]

/-- The contraction is homogeneous in its right factor. -/
@[simp]
theorem matrixContraction_smul_right {d : ℕ} (c : ℝ) (A H : PDE.Mat d) :
    matrixContraction A (c • H) = c * matrixContraction A H := by
  simp [matrixContraction, smul_eq_mul, mul_left_comm, Finset.mul_sum]

/-- Negating the left factor negates the contraction. -/
@[simp]
theorem matrixContraction_neg_left {d : ℕ} (A H : PDE.Mat d) :
    matrixContraction (-A) H = -matrixContraction A H := by
  simp [matrixContraction]

/-- Negating the right factor negates the contraction. -/
@[simp]
theorem matrixContraction_neg_right {d : ℕ} (A H : PDE.Mat d) :
    matrixContraction A (-H) = -matrixContraction A H := by
  simp [matrixContraction]

/-- For a symmetric right factor, entrywise contraction equals the trace product. -/
theorem matrixContraction_eq_trace_mul_of_isSymm {d : ℕ}
    (A H : PDE.Mat d) (hH : H.IsSymm) :
    matrixContraction A H = (A * H).trace := by
  unfold matrixContraction
  calc
    (∑ i, ∑ j, A i j * H i j) = ∑ i, ∑ j, A i j * H j i := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      refine Finset.sum_congr rfl ?_
      intro j _hj
      rw [hH.apply j i]
    _ = (A * H).trace := rfl

end HypoellipticAleksandrov
