module

public import HypoellipticAleksandrov.Parabolic.ScalarDirichletData
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-! # Locality of the stationary scalar operator

Equality on an open spatial set identifies both levels of the spatial derivative.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter Set
open scoped Topology

/-- Stationary scalar operators agree wherever their spatial representatives agree openly. -/
theorem stationary_scalarOperator_eqOn {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (f q : PDE.Vec d → ℝ) (heq : EqOn f q Ω)
    (A : CoefficientField d) (z : TimeVelocity d) (hz : z.2 ∈ Ω) :
    scalarParabolicZeroOrderOperator A (fun _ _ => 0) (fun _ _ => 0)
      (fun z => f z.2) z =
    scalarParabolicZeroOrderOperator A (fun _ _ => 0) (fun _ _ => 0)
      (fun z => q z.2) z := by
  have he (y : PDE.Vec d) (hy : y ∈ Ω) : f =ᶠ[𝓝 y] q := by
    filter_upwards [hΩ.mem_nhds hy] with x hx
    exact heq hx
  have hg : PDE.classicalGradient f =ᶠ[𝓝 z.2] PDE.classicalGradient q := by
    filter_upwards [hΩ.mem_nhds hz] with y hy
    exact congrArg (fun L : PDE.Vec d →L[ℝ] ℝ => fun i => L (PDE.basisVec i))
      (he y hy).fderiv_eq
  have hh : scalarSpatialHessian (fun z => f z.2) z =
      scalarSpatialHessian (fun z => q z.2) z := by
    ext i j
    exact congrArg (fun L : PDE.Vec d →L[ℝ] PDE.Vec d => L (PDE.basisVec i) j)
      hg.fderiv_eq
  have htf : scalarTimeDerivative (fun z => f z.2) z = 0 := by
    change deriv (fun _ : ℝ => f z.2) z.1 = 0
    exact deriv_const _ _
  have htq : scalarTimeDerivative (fun z => q z.2) z = 0 := by
    change deriv (fun _ : ℝ => q z.2) z.1 = 0
    exact deriv_const _ _
  simp only [scalarParabolicZeroOrderOperator_apply, htf, htq, hh, Pi.zero_apply,
    PDE.vecDot, zero_mul, Finset.sum_const_zero, add_zero]

end HypoellipticAleksandrov.Parabolic.LocalHolder
