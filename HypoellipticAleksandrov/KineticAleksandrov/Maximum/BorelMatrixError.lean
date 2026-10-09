module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelMatrixColumn
public import HypoellipticAleksandrov.Ambient.MatrixContraction
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Matrix.Normed

/-! # The exact Frobenius contraction bound for the source coefficient error -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open scoped MatrixOrder Matrix.Norms.Frobenius

/-- Mathlib's Frobenius norm, named to make the Euclidean normalization explicit. -/
def borelFrobeniusNorm {d : ℕ} (M : PDE.Mat d) : ℝ := ‖M‖

/-- The Frobenius norm is the square root of the sum of squared entries. -/
theorem borelFrobeniusNorm_eq {d : ℕ} (M : PDE.Mat d) :
    borelFrobeniusNorm M = Real.sqrt (∑ i, ∑ j, (M i j) ^ 2) := by
  simp only [borelFrobeniusNorm,Matrix.frobenius_norm_def,Real.rpow_two,
    Real.norm_eq_abs,sq_abs,Real.sqrt_eq_rpow]

/-- The sharp ellipticity-to-Frobenius bound has the source factor sqrt d. -/
theorem borel_frobenius_norm_le {d : ℕ} {lam Lam : ℝ} {A : PDE.Mat d}
    (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hlo : lam • (1 : PDE.Mat d) ≤ A) (hhi : A ≤ Lam • (1 : PDE.Mat d)) :
    borelFrobeniusNorm A ≤ Real.sqrt d * Lam := by
  have hn : 0 ≤ Lam := hlam.le.trans hLam
  have hs : (∑ i, ∑ j, (A i j) ^ 2) ≤ (d : ℝ) * Lam ^ 2 := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _j : Fin d, Lam ^ 2 := Finset.sum_le_sum fun j _ =>
        borel_matrix_column_sq_sum_le hlam hLam hlo hhi j
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [borelFrobeniusNorm_eq]
  have hnon : 0 ≤ ∑ i : Fin d, ∑ j : Fin d, (A i j) ^ 2 := by positivity
  have hsq := Real.sq_sqrt hnon
  have hdim := Real.sq_sqrt (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  have hr := Real.sqrt_nonneg (∑ i, ∑ j, (A i j) ^ 2)
  have hd := Real.sqrt_nonneg (d : ℝ)
  apply (sq_le_sq₀ hr (mul_nonneg hd hn)).mp
  calc
    _ = _ := hsq
    _ ≤ _ := hs
    _ = _ := by rw [mul_pow,hdim]

/-- Finite-dimensional Cauchy--Schwarz for the literal entrywise contraction. -/
theorem borel_matrix_contraction_le {d : ℕ} (M H : PDE.Mat d) :
    |matrixContraction M H| ≤ borelFrobeniusNorm M * borelFrobeniusNorm H := by
  have hplus := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun ij : Fin d × Fin d => M ij.1 ij.2) (fun ij => H ij.1 ij.2)
  have hminus := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun ij : Fin d × Fin d => -M ij.1 ij.2) (fun ij => H ij.1 ij.2)
  simp only [Fintype.sum_prod_type,neg_mul,Finset.sum_neg_distrib,neg_sq] at hplus hminus
  rw [borelFrobeniusNorm_eq,borelFrobeniusNorm_eq,abs_le]
  exact ⟨neg_le.mp hminus,hplus⟩

/-- The source error domination retains exactly 2 sqrt d times the upper bound. -/
theorem borel_coefficient_error_bound {d : ℕ} {lam Lam : ℝ} {A C : PDE.Mat d}
    (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hAl : lam • (1 : PDE.Mat d) ≤ A) (hAu : A ≤ Lam • (1 : PDE.Mat d))
    (hCl : lam • (1 : PDE.Mat d) ≤ C) (hCu : C ≤ Lam • (1 : PDE.Mat d))
    (H : PDE.Mat d) :
    |matrixContraction (C - A) H| ≤ 2 * Real.sqrt d * Lam * borelFrobeniusNorm H := by
  have hnorm : borelFrobeniusNorm (C - A) ≤ 2 * Real.sqrt d * Lam := by
    have hA := borel_frobenius_norm_le hlam hLam hAl hAu
    have hC := borel_frobenius_norm_le hlam hLam hCl hCu
    have ht := norm_sub_le C A
    change borelFrobeniusNorm (C - A) ≤ borelFrobeniusNorm C + borelFrobeniusNorm A at ht
    linarith only [hA,hC,ht]
  exact (borel_matrix_contraction_le (C - A) H).trans
    (mul_le_mul_of_nonneg_right hnorm (norm_nonneg H))

end HypoellipticAleksandrov.KineticAleksandrov
