module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripMassQuadraticCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! # One-dimensional diffused profile calculus for collar barriers -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Evolution

/-- A scalar velocity profile, written in the native diffused coordinate. -/
def reconstructionProfile (f : ℝ → ℝ) (p : Point) : ℝ := f (p.position 0)

/-- A twice smooth scalar profile has the required native slice regularity. -/
theorem reconstructionProfile_regular {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (p : Point) :
    IsSliceRegularAt (reconstructionProfile f) p := by
  refine ⟨?_, ?_, ?_⟩
  · change DifferentiableAt ℝ (fun _ : ℝ => f (p.position 0)) p.time
    exact differentiableAt_const _
  · exact (hf.comp (contDiff_apply ℝ ℝ (0 : Fin 1))).contDiffAt
  · change ContDiffAt ℝ 2 (fun _ : PDE.Vec 1 => f (p.position 0)) p.velocity
    exact contDiffAt_const

/-- A continuous scalar profile is continuous on native spacetime. -/
theorem reconstructionProfile_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (reconstructionProfile f) :=
  hf.comp ((continuous_apply 0).comp continuous_position)

private theorem profile_gradient {f : ℝ → ℝ} (hf : Differentiable ℝ f) (y : PDE.Vec 1) :
    PDE.classicalGradient (fun z : PDE.Vec 1 => f (z 0)) y =
      fun _ => deriv f (y 0) := by
  ext i
  have h := (hf (y 0)).hasDerivAt.comp_hasFDerivAt y (hasFDerivAt_apply (𝕜 := ℝ) 0 y)
  change fderiv ℝ (fun z : PDE.Vec 1 => f (z 0)) y (PDE.basisVec i) = _
  have hd : fderiv ℝ (fun z : PDE.Vec 1 => f (z 0)) y =
      deriv f (y 0) • ContinuousLinearMap.proj 0 := by
    simpa only [Function.comp_def] using! h.fderiv
  rw [hd]
  fin_cases i
  simp [PDE.basisVec]

private theorem profile_hessian {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (y : PDE.Vec 1) :
    sliceHessian (fun z : PDE.Vec 1 => f (z 0)) y 0 0 = deriv (deriv f) (y 0) := by
  have hg : (fun z => PDE.classicalGradient (fun w : PDE.Vec 1 => f (w 0)) z) =
      fun z _ => deriv f (z 0) :=
    funext (profile_gradient (hf.differentiable (by norm_num)))
  have h := (hf.differentiable_deriv_two (y 0)).hasDerivAt.comp_hasFDerivAt y
    (hasFDerivAt_apply (𝕜 := ℝ) 0 y)
  have hp := hasFDerivAt_pi.mpr (fun _ : Fin 1 => h)
  unfold sliceHessian
  rw [hg]
  have hd : fderiv ℝ (fun z : PDE.Vec 1 => fun _ : Fin 1 => deriv f (z 0)) y =
      ContinuousLinearMap.pi (fun _ : Fin 1 =>
        deriv (deriv f) (y 0) • ContinuousLinearMap.proj 0) := by
    simpa only [Function.comp_def] using! hp.fderiv
  rw [hd]
  simp [PDE.basisVec]

/-- The scalar profile operator is exactly the coefficient times its second derivative. -/
theorem reconstructionProfile_operator (a : ℝ → ℝ → ℝ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (p : Point) :
    transportedForwardOperator (evolutionCoefficient a) (SectionTwo.identityDrift 1)
      (reconstructionProfile f) p = a (p.velocity 0) (p.position 0) *
        deriv (deriv f) (p.position 0) := by
  have hg : kineticVelocityGradient (reconstructionProfile f) p = 0 := by
    ext i
    change fderiv ℝ (fun _ : PDE.Vec 1 => f (p.position 0)) p.velocity (PDE.basisVec i) = 0
    rw [(hasFDerivAt_const (f (p.position 0)) p.velocity).fderiv]
    rfl
  rw [transportedForwardOperator_apply, hg]
  simp only [kineticTimeDerivative, reconstructionProfile, deriv_const,
    PDE.vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add, add_zero]
  rw [diffusedHessian_eq_sliceHessian]
  simp only [fullKineticCoefficientAt, evolutionCoefficient, matrixContraction,
    Fin.sum_univ_one, reconstructionProfile]
  rw [profile_hessian hf]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
