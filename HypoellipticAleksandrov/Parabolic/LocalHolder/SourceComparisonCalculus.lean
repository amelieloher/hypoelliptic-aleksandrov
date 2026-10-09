module

public import HypoellipticAleksandrov.Parabolic.ScalarDirichletData
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Add

/-! # Classical subtraction for signed source corrections

These local public subtraction lemmas provide the calculus needed to combine positive
Dirichlet solutions without changing the comparison module.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter Set Matrix
open scoped Topology

/-- Time derivatives commute with subtraction of classical functions. -/
theorem scalarTimeDerivative_sub {n : ℕ} {u v : TimeVelocity n → ℝ}
    {D : Set (TimeVelocity n)} (hu : IsScalarC12On u D) (hv : IsScalarC12On v D)
    {z : TimeVelocity n} (hz : z ∈ D) :
    scalarTimeDerivative (fun q => u q - v q) z =
      scalarTimeDerivative u z - scalarTimeDerivative v z := by
  exact ((hu.timeSlice_hasDerivAt hz).sub (hv.timeSlice_hasDerivAt hz)).deriv

/-- Spatial gradients commute with subtraction of classical functions. -/
theorem scalarSpatialGradient_sub {n : ℕ} {u v : TimeVelocity n → ℝ}
    {D : Set (TimeVelocity n)} (hu : IsScalarC12On u D) (hv : IsScalarC12On v D)
    {z : TimeVelocity n} (hz : z ∈ D) :
    scalarSpatialGradient (fun q => u q - v q) z =
      scalarSpatialGradient u z - scalarSpatialGradient v z := by
  ext i
  change fderiv ℝ (fun y : PDE.Vec n => u (z.1, y) - v (z.1, y)) z.2
      (PDE.basisVec i) = _
  rw [fderiv_fun_sub ((hu.spatialSlice_contDiffAt hz).differentiableAt (by norm_num))
    ((hv.spatialSlice_contDiffAt hz).differentiableAt (by norm_num))]
  rfl

private theorem scalarSpatialHessian_apply_eq_sndFDeriv {n : ℕ}
    {u : TimeVelocity n → ℝ} {z : TimeVelocity n}
    (hu : ContDiffAt ℝ 2 (fun y : PDE.Vec n => u (z.1, y)) z.2)
    (i j : Fin n) :
    scalarSpatialHessian u z i j =
      fderiv ℝ (fderiv ℝ (fun y : PDE.Vec n => u (z.1, y))) z.2
        (PDE.basisVec i) (PDE.basisVec j) := by
  let g : PDE.Vec n → ℝ := fun y => u (z.1, y)
  have hsecond : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) z.2) z.2 :=
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hdiff : ∀ j : Fin n,
      DifferentiableAt ℝ (fun y : PDE.Vec n => fderiv ℝ g y (PDE.basisVec j)) z.2 := by
    intro j
    exact (hsecond.clm_apply (hasFDerivAt_const (PDE.basisVec j) z.2)).differentiableAt
  change (fderiv ℝ (fun y : PDE.Vec n => fun j =>
      fderiv ℝ g y (PDE.basisVec j)) z.2 (PDE.basisVec i)) j = _
  rw [fderiv_pi hdiff]
  have hj := (hsecond.clm_apply (hasFDerivAt_const (PDE.basisVec j) z.2)).fderiv
  have hjApply := congrArg (fun L : PDE.Vec n →L[ℝ] ℝ => L (PDE.basisVec i)) hj
  simpa [ContinuousLinearMap.flip_apply] using hjApply

/-- Spatial Hessians commute with subtraction of classical functions. -/
theorem scalarSpatialHessian_sub {n : ℕ} {u v : TimeVelocity n → ℝ}
    {D : Set (TimeVelocity n)} (hu : IsScalarC12On u D) (hv : IsScalarC12On v D)
    {z : TimeVelocity n} (hz : z ∈ D) :
    scalarSpatialHessian (fun q => u q - v q) z =
      scalarSpatialHessian u z - scalarSpatialHessian v z := by
  let g_u : PDE.Vec n → ℝ := fun y => u (z.1, y)
  let g_v : PDE.Vec n → ℝ := fun y => v (z.1, y)
  have hfirst : fderiv ℝ (fun y => g_u y - g_v y) =ᶠ[𝓝 z.2]
      fun y => fderiv ℝ g_u y - fderiv ℝ g_v y := by
    filter_upwards [(hu.spatialSlice_contDiffAt hz).eventually (by norm_num),
      (hv.spatialSlice_contDiffAt hz).eventually (by norm_num)] with y huy hvy
    exact fderiv_fun_sub (huy.differentiableAt (by norm_num))
      (hvy.differentiableAt (by norm_num))
  have huSecond : HasFDerivAt (fun y : PDE.Vec n => fderiv ℝ g_u y)
      (fderiv ℝ (fderiv ℝ g_u) z.2) z.2 :=
    ((hu.spatialSlice_contDiffAt hz).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num) |>.hasFDerivAt
  have hvSecond : HasFDerivAt (fun y : PDE.Vec n => fderiv ℝ g_v y)
      (fderiv ℝ (fderiv ℝ g_v) z.2) z.2 :=
    ((hv.spatialSlice_contDiffAt hz).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num) |>.hasFDerivAt
  have hsecond : fderiv ℝ (fderiv ℝ (fun y => g_u y - g_v y)) z.2 =
      fderiv ℝ (fderiv ℝ g_u) z.2 - fderiv ℝ (fderiv ℝ g_v) z.2 := by
    calc
      fderiv ℝ (fderiv ℝ (fun y => g_u y - g_v y)) z.2 =
          fderiv ℝ (fun y => fderiv ℝ g_u y - fderiv ℝ g_v y) z.2 :=
        hfirst.fderiv_eq
      _ = fderiv ℝ (fderiv ℝ g_u) z.2 - fderiv ℝ (fderiv ℝ g_v) z.2 :=
        fderiv_fun_sub huSecond.differentiableAt hvSecond.differentiableAt
  ext i j
  rw [Matrix.sub_apply,
    scalarSpatialHessian_apply_eq_sndFDeriv
    ((hu.spatialSlice_contDiffAt hz).sub (hv.spatialSlice_contDiffAt hz)) i j,
    scalarSpatialHessian_apply_eq_sndFDeriv (hu.spatialSlice_contDiffAt hz) i j,
    scalarSpatialHessian_apply_eq_sndFDeriv (hv.spatialSlice_contDiffAt hz) i j,
    hsecond]
  rfl

/-- The anisotropic classical carrier is closed under subtraction. -/
theorem isScalarC12On_sub {n : ℕ} {u v : TimeVelocity n → ℝ}
    {D : Set (TimeVelocity n)} (hu : IsScalarC12On u D) (hv : IsScalarC12On v D) :
    IsScalarC12On (fun q => u q - v q) D := by
  refine ⟨hu.continuousOn.sub hv.continuousOn, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (hu.timeSlice_differentiableAt hz).sub (hv.timeSlice_differentiableAt hz)
  · intro z hz
    exact (hu.spatialSlice_contDiffAt hz).sub (hv.spatialSlice_contDiffAt hz)
  · apply (hu.continuousOn_scalarTimeDerivative.sub
      hv.continuousOn_scalarTimeDerivative).congr
    intro z hz
    exact scalarTimeDerivative_sub hu hv hz
  · apply (hu.continuousOn_scalarSpatialGradient.sub
      hv.continuousOn_scalarSpatialGradient).congr
    intro z hz
    exact scalarSpatialGradient_sub hu hv hz
  · apply (hu.continuousOn_scalarSpatialHessian.sub
      hv.continuousOn_scalarSpatialHessian).congr
    intro z hz
    exact scalarSpatialHessian_sub hu hv hz

/-- The backward operator is linear on classical functions. -/
theorem scalarParabolicZeroOrderOperator_sub {n : ℕ}
    (a : CoefficientField n) (b : ℝ → PDE.Vec n → PDE.Vec n)
    (c : ℝ → PDE.Vec n → ℝ) {u v : TimeVelocity n → ℝ}
    {D : Set (TimeVelocity n)} (hu : IsScalarC12On u D) (hv : IsScalarC12On v D)
    {z : TimeVelocity n} (hz : z ∈ D) :
    scalarParabolicZeroOrderOperator a b c (fun q => u q - v q) z =
      scalarParabolicZeroOrderOperator a b c u z -
        scalarParabolicZeroOrderOperator a b c v z := by
  rw [scalarParabolicZeroOrderOperator_apply, scalarParabolicZeroOrderOperator_apply,
    scalarParabolicZeroOrderOperator_apply, scalarTimeDerivative_sub hu hv hz,
    scalarSpatialGradient_sub hu hv hz, scalarSpatialHessian_sub hu hv hz]
  have hHessian : matrixContraction (a z.1 z.2)
      (scalarSpatialHessian u z - scalarSpatialHessian v z) =
      matrixContraction (a z.1 z.2) (scalarSpatialHessian u z) -
        matrixContraction (a z.1 z.2) (scalarSpatialHessian v z) := by
    unfold matrixContraction
    simp only [Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]
  have hGradient : PDE.vecDot (b z.1 z.2)
      (scalarSpatialGradient u z - scalarSpatialGradient v z) =
      PDE.vecDot (b z.1 z.2) (scalarSpatialGradient u z) -
        PDE.vecDot (b z.1 z.2) (scalarSpatialGradient v z) := by
    unfold PDE.vecDot
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  rw [hHessian, hGradient]
  ring


end HypoellipticAleksandrov.Parabolic.LocalHolder
