module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import HypoellipticAleksandrov.Parabolic.Dirichlet.WeakTimeDerivative

/-!
# Bounded spatial operators on Gelfand weak time derivatives

This module transports a reverse-time Gelfand weak derivative through a bounded
spatial operator whose action is symmetric for the scalar `L²` pivot.  The
dual action is Banach-dual precomposition, not a Hilbert adjoint.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- Precompose an `H10` dual functional with a bounded spatial operator. -/
noncomputable def h10HilbertGraphDualPrecompose
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω)
    (S : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ) :
    H10HilbertGraphDual hΩ →L[ℝ] H10HilbertGraphDual hΩ :=
  (ContinuousLinearMap.compL ℝ (H10HilbertGraph hΩ) (H10HilbertGraph hΩ) ℝ).flip S

/-- Evaluation of dual precomposition. -/
@[simp] theorem h10HilbertGraphDualPrecompose_apply
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω)
    (S : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ)
    (ell : H10HilbertGraphDual hΩ) (v : H10HilbertGraph hΩ) :
    h10HilbertGraphDualPrecompose hΩ S ell v = ell (S v) := by
  rfl

private theorem ae_reverseTimeValueCLM_compLpL_apply
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ)
    (S : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ)
    (u : ReverseTimeL2V hΩ T) :
    reverseTimeValueCLM hΩ T
        (S.compLpL (2 : ℝ≥0∞) (reverseTimeVolume T) u) =ᵐ[reverseTimeVolume T]
      fun τ => valueCLM hΩ (S (u τ)) := by
  filter_upwards [
    coeFn_reverseTimeValueCLM hΩ T
      (S.compLpL (2 : ℝ≥0∞) (reverseTimeVolume T) u),
    ContinuousLinearMap.coeFn_compLpL S u
  ] with τ hvalue hS
  rw [hvalue, hS]

private theorem ae_h10HilbertGraphDualPrecompose_compLpL_apply
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ)
    (S : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ)
    (g : ReverseTimeL2VStar hΩ T) :
    (h10HilbertGraphDualPrecompose hΩ S).compLpL
        (2 : ℝ≥0∞) (reverseTimeVolume T) g =ᵐ[reverseTimeVolume T]
      fun τ => h10HilbertGraphDualPrecompose hΩ S (g τ) :=
  ContinuousLinearMap.coeFn_compLpL (h10HilbertGraphDualPrecompose hΩ S) g

private theorem ae_pivot_symmetric_left_pairing
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ)
    (u : ReverseTimeL2V hΩ T)
    (S : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ)
    (hS : ∀ x y : H10HilbertGraph hΩ,
      inner ℝ (valueCLM hΩ x) (valueCLM hΩ (S y)) =
        inner ℝ (valueCLM hΩ (S x)) (valueCLM hΩ y))
    (v : H10HilbertGraph hΩ) (eta : ReverseTimeScalarTest T) :
    (fun τ =>
      inner ℝ (valueCLM hΩ v)
        (reverseTimeValueCLM hΩ T
          (S.compLpL (2 : ℝ≥0∞) (reverseTimeVolume T) u) τ) * eta.deriv τ) =ᵐ[
        reverseTimeVolume T]
      fun τ => inner ℝ (valueCLM hΩ (S v))
        (reverseTimeValueCLM hΩ T u τ) * eta.deriv τ := by
  filter_upwards [
    ae_reverseTimeValueCLM_compLpL_apply hΩ T S u,
    coeFn_reverseTimeValueCLM hΩ T u
  ] with τ hSu hu
  rw [hSu, hu, hS]

private theorem ae_pivot_symmetric_right_pairing
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ)
    (g : ReverseTimeL2VStar hΩ T)
    (S : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ)
    (v : H10HilbertGraph hΩ) (eta : ReverseTimeScalarTest T) :
    (fun τ =>
      ((h10HilbertGraphDualPrecompose hΩ S).compLpL
        (2 : ℝ≥0∞) (reverseTimeVolume T) g τ) v * eta τ) =ᵐ[
        reverseTimeVolume T]
      fun τ => (g τ) (S v) * eta τ := by
  filter_upwards [ae_h10HilbertGraphDualPrecompose_compLpL_apply hΩ T S g] with τ hg
  rw [hg]
  rfl

/-- A Gelfand weak derivative is preserved by a bounded spatial operator that
is symmetric for the scalar `L²` pivot. -/
theorem HasGelfandWeakTimeDerivative.comp_of_pivot_symmetric
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    {hΩ : IsOpen Ω} {T : ℝ} {hT : 0 < T}
    {u : ReverseTimeL2V hΩ T} {g : ReverseTimeL2VStar hΩ T}
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (S : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ)
    (hS : ∀ x y : H10HilbertGraph hΩ,
      inner ℝ (valueCLM hΩ x) (valueCLM hΩ (S y)) =
        inner ℝ (valueCLM hΩ (S x)) (valueCLM hΩ y)) :
    HasGelfandWeakTimeDerivative hΩ T hT
      (S.compLpL (2 : ℝ≥0∞) (reverseTimeVolume T) u)
      ((h10HilbertGraphDualPrecompose hΩ S).compLpL
        (2 : ℝ≥0∞) (reverseTimeVolume T) g) := by
  intro v eta
  obtain ⟨hleft, hright, hidentity⟩ := hderiv (S v) eta
  refine ⟨?_, ?_, ?_⟩
  · exact hleft.congr
      (ae_pivot_symmetric_left_pairing hΩ T u S hS v eta).symm
  · exact hright.congr
      (ae_pivot_symmetric_right_pairing hΩ T g S v eta).symm
  calc
    (∫ τ,
      inner ℝ (valueCLM hΩ v)
        (reverseTimeValueCLM hΩ T
          (S.compLpL (2 : ℝ≥0∞) (reverseTimeVolume T) u) τ) * eta.deriv τ
        ∂reverseTimeVolume T) =
        ∫ τ, inner ℝ (valueCLM hΩ (S v))
          (reverseTimeValueCLM hΩ T u τ) * eta.deriv τ
          ∂reverseTimeVolume T :=
      integral_congr_ae (ae_pivot_symmetric_left_pairing hΩ T u S hS v eta)
    _ = -(∫ τ, (g τ) (S v) * eta τ ∂reverseTimeVolume T) := hidentity
    _ = -(∫ τ,
      ((h10HilbertGraphDualPrecompose hΩ S).compLpL
        (2 : ℝ≥0∞) (reverseTimeVolume T) g τ) v * eta τ
        ∂reverseTimeVolume T) := by
      exact congrArg Neg.neg <|
        (integral_congr_ae (ae_pivot_symmetric_right_pairing hΩ T g S v eta)).symm

end HypoellipticAleksandrov.Parabolic.Dirichlet
