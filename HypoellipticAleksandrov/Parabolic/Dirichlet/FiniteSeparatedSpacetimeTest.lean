module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.OriginalTimeSpacetimeTest
public import HypoellipticAleksandrov.Parabolic.Derivatives

/-!
# Finite separated spacetime tests

This module packages finite sums of smooth separated time--space tests and
identifies their literal time derivative.
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- A finite sum of smooth separated time--space tests. -/
structure FiniteSeparatedSpacetimeTest
    {d : ℕ} (τ₁ τ₂ : ℝ) (O : Set (PDE.Vec d)) where
  termCount : ℕ
  timeFactor : Fin termCount → OriginalTimeScalarTest τ₁ τ₂
  spatialFactor : Fin termCount → PDE.WeakTestFunction O

/-- The raw spacetime function represented by a finite separated test. -/
noncomputable def FiniteSeparatedSpacetimeTest.toFun
    {d : ℕ} {τ₁ τ₂ : ℝ} {O : Set (PDE.Vec d)}
    (q : FiniteSeparatedSpacetimeTest τ₁ τ₂ O) :
    TimeVelocity d → ℝ :=
  fun z => ∑ m : Fin q.termCount,
    q.timeFactor m z.1 * q.spatialFactor m z.2

/-- The literal time derivative of a finite separated test. -/
noncomputable def FiniteSeparatedSpacetimeTest.timeDeriv
    {d : ℕ} {τ₁ τ₂ : ℝ} {O : Set (PDE.Vec d)}
    (q : FiniteSeparatedSpacetimeTest τ₁ τ₂ O) :
    TimeVelocity d → ℝ :=
  fun z => ∑ m : Fin q.termCount,
    (q.timeFactor m).deriv z.1 * q.spatialFactor m z.2

/-- The time derivative of a finite separated test differentiates only its time factors. -/
@[simp] theorem timeDerivative_finiteSeparatedSpacetimeTest
    {d : ℕ} {τ₁ τ₂ : ℝ} {O : Set (PDE.Vec d)}
    (q : FiniteSeparatedSpacetimeTest τ₁ τ₂ O)
    (z : TimeVelocity d) :
    timeDerivative q.toFun z = q.timeDeriv z := by
  unfold timeDerivative FiniteSeparatedSpacetimeTest.toFun
    FiniteSeparatedSpacetimeTest.timeDeriv
  rw [fderiv_fun_sum]
  simp only [ContinuousLinearMap.sum_apply]
  · apply Finset.sum_congr rfl
    intro m _
    have htime : DifferentiableAt ℝ
        (fun w : TimeVelocity d => q.timeFactor m w.1) z :=
      ((q.timeFactor m).contDiff.comp contDiff_fst).differentiable
        (by simp) z
    have hspace : DifferentiableAt ℝ
        (fun w : TimeVelocity d => q.spatialFactor m w.2) z :=
      ((q.spatialFactor m).contDiff.comp contDiff_snd).differentiable
        (by simp) z
    change (fderiv ℝ
      ((fun w : TimeVelocity d => q.timeFactor m w.1) *
        fun w : TimeVelocity d => q.spatialFactor m w.2) z) (1, 0) = _
    rw [fderiv_mul htime hspace]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have htimeFDeriv : HasFDerivAt
        (fun w : TimeVelocity d => q.timeFactor m w.1)
        ((fderiv ℝ (q.timeFactor m) z.1).comp
          (ContinuousLinearMap.fst ℝ ℝ (PDE.Vec d))) z := by
      simpa only [Function.comp_def] using!
        ((q.timeFactor m).contDiff.differentiable (by simp) z.1).hasFDerivAt.comp z
          (hasFDerivAt_fst (𝕜 := ℝ))
    have hspaceFDeriv : HasFDerivAt
        (fun w : TimeVelocity d => q.spatialFactor m w.2)
        ((fderiv ℝ (q.spatialFactor m) z.2).comp
          (ContinuousLinearMap.snd ℝ ℝ (PDE.Vec d))) z := by
      simpa only [Function.comp_def] using!
        ((q.spatialFactor m).contDiff.differentiable (by simp) z.2).hasFDerivAt.comp z
          (hasFDerivAt_snd (𝕜 := ℝ))
    rw [htimeFDeriv.fderiv, hspaceFDeriv.fderiv]
    rw [OriginalTimeScalarTest.deriv_apply]
    change q.timeFactor m z.1 * fderiv ℝ (q.spatialFactor m) z.2 0 +
      q.spatialFactor m z.2 * fderiv ℝ (q.timeFactor m) z.1 1 =
        deriv (q.timeFactor m) z.1 * q.spatialFactor m z.2
    rw [map_zero, mul_zero, zero_add]
    rw [deriv]
    ring
  · intro m _
    exact (((q.timeFactor m).contDiff.comp contDiff_fst).mul
      ((q.spatialFactor m).contDiff.comp contDiff_snd)).differentiable
        (by simp) z

end HypoellipticAleksandrov.Parabolic.Dirichlet
