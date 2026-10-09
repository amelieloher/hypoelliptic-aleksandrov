module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Setting
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ScalarAdaptersCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic

/-! # Exact cutoff errors for the physical kinetic operator

The position and velocity cutoffs are separate scalar functions. The product
identity contains no derivative of the coefficient field.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov.Parabolic

/-- Product of scalar position and velocity cutoffs with a physical test function. -/
def spatialCutoffTest (chi psi : ℝ → ℝ) (phi : Point → ℝ) (p : Point) : ℝ :=
  chi (p.position 0)*psi (p.velocity 0)*phi p

/-- Scalar second-derivative Leibniz rule for C² factors. -/
theorem second_deriv_product (f g : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (v : ℝ) :
    deriv (deriv (fun w => f w*g w)) v =
      deriv (deriv f) v*g v+2*deriv f v*deriv g v+f v*deriv (deriv g) v := by
  have hd := hf.differentiable (by norm_num)
  have he := hg.differentiable (by norm_num)
  have heq : deriv (fun w => f w*g w) =
      fun w => deriv f w*g w+f w*deriv g w := by
    funext w
    exact deriv_fun_mul (hd w) (he w)
  have h₁ : DifferentiableAt ℝ (fun w => deriv f w*g w) v :=
    (hf.differentiable_deriv_two v).mul (he v)
  have h₂ : DifferentiableAt ℝ (fun w => f w*deriv g w) v :=
    (hd v).mul (hg.differentiable_deriv_two v)
  rw [heq, deriv_fun_add h₁ h₂,
    deriv_fun_mul (hf.differentiable_deriv_two v) (he v),
    deriv_fun_mul (hd v) (hg.differentiable_deriv_two v)]
  ring

/-- Exact physical cutoff product rule, with only the actual slice regularity. -/
theorem spatialCutoffTest_operator (a : ℝ → ℝ → ℝ) (chi psi : ℝ → ℝ)
    (hchi : ContDiff ℝ 2 chi) (hpsi : ContDiff ℝ 2 psi)
    (phi : Point → ℝ) (p : Point)
    (ht : DifferentiableAt ℝ (fun t => phi ⟨t, p.position, p.velocity⟩) p.time)
    (hx : DifferentiableAt ℝ (fun x => phi ⟨p.time, fun _ => x, p.velocity⟩)
      (p.position 0))
    (hv : ContDiff ℝ 2 (fun v => phi ⟨p.time, p.position, fun _ => v⟩)) :
    forwardScalarOperator a (spatialCutoffTest chi psi phi) p =
      chi (p.position 0)*psi (p.velocity 0)*forwardScalarOperator a phi p+
      p.velocity 0*deriv chi (p.position 0)*psi (p.velocity 0)*phi p+
      a (p.position 0) (p.velocity 0)*chi (p.position 0)*
        deriv (deriv psi) (p.velocity 0)*phi p+
      2*a (p.position 0) (p.velocity 0)*chi (p.position 0)*deriv psi (p.velocity 0)*
        kineticVelocityGradient phi p 0 := by
  have hc := hchi.differentiable (by norm_num)
  have hp := hpsi.differentiable (by norm_num)
  have htime : kineticTimeDerivative (spatialCutoffTest chi psi phi) p =
      chi (p.position 0)*psi (p.velocity 0)*kineticTimeDerivative phi p := by
    change deriv (fun t => (chi (p.position 0)*psi (p.velocity 0))*
      phi ⟨t, p.position, p.velocity⟩) p.time = _
    exact deriv_const_mul _ ht
  have hposition : kineticPositionGradient (spatialCutoffTest chi psi phi) p 0 =
      deriv chi (p.position 0)*psi (p.velocity 0)*phi p+
        chi (p.position 0)*psi (p.velocity 0)*kineticPositionGradient phi p 0 := by
    rw [kineticPositionGradient_scalar, kineticPositionGradient_scalar]
    change deriv (fun x => (chi x*psi (p.velocity 0))*
      phi ⟨p.time, fun _ => x, p.velocity⟩) (p.position 0) = _
    rw [deriv_fun_mul ((hc _).mul_const _) hx, deriv_mul_const (hc _) _]
    have he : phi ⟨p.time, fun _ => p.position 0, p.velocity⟩ = phi p := by
      congr 1
      ext i
      · rfl
      · rw [Fin.eq_zero i]
      · rfl
    rw [he]
  have hvelocity : kineticVelocityHessian (spatialCutoffTest chi psi phi) p 0 0 =
      chi (p.position 0)*
        (deriv (deriv psi) (p.velocity 0)*phi p+
          2*deriv psi (p.velocity 0)*kineticVelocityGradient phi p 0+
          psi (p.velocity 0)*kineticVelocityHessian phi p 0 0) := by
    rw [kineticVelocityHessian_scalar, kineticVelocityHessian_scalar,
      kineticVelocityGradient_scalar]
    have he : (fun v => spatialCutoffTest chi psi phi
        ⟨p.time, p.position, fun _ => v⟩) =
        fun v => chi (p.position 0)*(psi v*phi ⟨p.time, p.position, fun _ => v⟩) := by
      funext v
      dsimp [spatialCutoffTest]
      ring
    rw [he, deriv_const_mul_field', deriv_const_mul_field,
      second_deriv_product psi _ hpsi hv]
    have he' : phi ⟨p.time, p.position, fun _ => p.velocity 0⟩ = phi p := by
      congr 1
      ext i
      · rfl
      · rfl
      · rw [Fin.eq_zero i]
    rw [he']
  dsimp [forwardScalarOperator]
  rw [htime, hposition, hvelocity]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
