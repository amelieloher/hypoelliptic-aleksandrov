module

public import HypoellipticAleksandrov.Parabolic.ScalarClassical
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring

/-!
# Calculus for the explicit Euclidean norm on raw vectors

This file records the first derivatives of `PDE.vecNormSq` and
`PDE.vecEuclideanNorm`.  These are the explicit finite-coordinate Euclidean
functions on `PDE.Vec`; no norm inherited from a type-class instance is used.
-/

@[expose] public section

namespace HypoellipticAleksandrov

noncomputable section

open scoped BigOperators

/-- The continuous linear functional `w ↦ 2 (z · w)`. -/
noncomputable def vecNormSqFDeriv {d : ℕ} (z : PDE.Vec d) : PDE.Vec d →L[ℝ] ℝ :=
  ∑ i, (2 * z i) • ContinuousLinearMap.proj i

@[simp]
theorem vecNormSqFDeriv_apply {d : ℕ} (z w : PDE.Vec d) :
    vecNormSqFDeriv z w = 2 * PDE.vecDot z w := by
  classical
  unfold vecNormSqFDeriv PDE.vecDot
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- The squared explicit Euclidean norm has derivative `w ↦ 2 (z · w)`. -/
theorem hasFDerivAt_vecNormSq {d : ℕ} (z : PDE.Vec d) :
    HasFDerivAt PDE.vecNormSq (vecNormSqFDeriv z) z := by
  classical
  have hd : DifferentiableAt ℝ PDE.vecNormSq z := by
    unfold PDE.vecNormSq PDE.vecDot
    fun_prop
  convert hd.hasFDerivAt using 1
  ext w
  rw [vecNormSqFDeriv_apply]
  unfold PDE.vecNormSq PDE.vecDot
  rw [fderiv_fun_sum fun i _ => by fun_prop]
  simp only [ContinuousLinearMap.sum_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [fderiv_fun_mul (by fun_prop) (by fun_prop)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [(hasFDerivAt_apply (𝕜 := ℝ) i z).fderiv]
  simp only [ContinuousLinearMap.proj_apply]
  ring

/-- Pointwise formula for the Fréchet derivative of the squared Euclidean norm. -/
theorem fderiv_vecNormSq_apply {d : ℕ} (z w : PDE.Vec d) :
    fderiv ℝ PDE.vecNormSq z w = 2 * PDE.vecDot z w := by
  rw [(hasFDerivAt_vecNormSq z).fderiv, vecNormSqFDeriv_apply]

/-- The continuous linear functional `w ↦ (z · w) / |z|`. -/
noncomputable def vecEuclideanNormFDeriv {d : ℕ} (z : PDE.Vec d) :
    PDE.Vec d →L[ℝ] ℝ :=
  (PDE.vecEuclideanNorm z)⁻¹ • ∑ i, z i • ContinuousLinearMap.proj i

@[simp]
theorem vecEuclideanNormFDeriv_apply {d : ℕ} (z w : PDE.Vec d) :
    vecEuclideanNormFDeriv z w = PDE.vecDot z w / PDE.vecEuclideanNorm z := by
  classical
  unfold vecEuclideanNormFDeriv PDE.vecDot
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [div_eq_inv_mul]

/-- Away from zero, the explicit Euclidean norm has derivative
`w ↦ (z · w) / |z|`. -/
theorem hasFDerivAt_vecEuclideanNorm {d : ℕ} {z : PDE.Vec d} (hz : z ≠ 0) :
    HasFDerivAt PDE.vecEuclideanNorm (vecEuclideanNormFDeriv z) z := by
  have hsq : PDE.vecNormSq z ≠ 0 := fun h =>
    hz (PDE.vecNormSq_eq_zero h)
  unfold PDE.vecEuclideanNorm
  have hsqrt := (hasFDerivAt_vecNormSq z).sqrt hsq
  convert hsqrt using 1
  ext w
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul,
    vecNormSqFDeriv_apply, vecEuclideanNormFDeriv_apply]
  change PDE.vecDot z w * (Real.sqrt (PDE.vecNormSq z))⁻¹ =
    (1 / (2 * Real.sqrt (PDE.vecNormSq z))) * (2 * PDE.vecDot z w)
  ring

/-- Pointwise formula for the Fréchet derivative of the explicit Euclidean norm away from zero. -/
theorem fderiv_vecEuclideanNorm_apply {d : ℕ} {z : PDE.Vec d} (hz : z ≠ 0)
    (w : PDE.Vec d) :
    fderiv ℝ PDE.vecEuclideanNorm z w =
      PDE.vecDot z w / PDE.vecEuclideanNorm z := by
  rw [(hasFDerivAt_vecEuclideanNorm hz).fderiv, vecEuclideanNormFDeriv_apply]

end

end HypoellipticAleksandrov
