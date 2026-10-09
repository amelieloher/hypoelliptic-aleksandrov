module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.MeasureDerivativeKernel
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-! # Concrete weighted measure pairings on the native Mathlib test space -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory

/-- The ordinary derivative is a linear map on the native real compact test space. -/
def bellmanTestDerivativeLinearMap : BellmanRealTest →ₗ[ℝ] BellmanRealTest where
  toFun := bellmanTestDerivative
  map_add' φ ψ := by
    apply DFunLike.ext
    intro x
    change deriv (fun y => φ y + ψ y) x = deriv φ x + deriv ψ x
    exact deriv_add (φ.contDiff.differentiable (by simp) x)
      (ψ.contDiff.differentiable (by simp) x)
  map_smul' c φ := by
    apply DFunLike.ext
    intro x
    change deriv (fun y => c * φ y) x = c * deriv φ x
    exact deriv_const_mul c (φ.contDiff.differentiable (by simp) x)

/-- The actual weighted measure pairing, using Mathlib's integral-against-test linear map. -/
def bellmanWeightedTestIntegral (μ : Measure ℝ) (g : ℝ → ℝ) : BellmanRealTest →ₗ[ℝ] ℝ :=
  (TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.lsmul ℝ ℝ) μ g).toLinearMap

/-- For a locally integrable weight the concrete test pairing is its literal measure integral. -/
theorem bellmanWeightedTestIntegral_apply (μ : Measure ℝ) (g : ℝ → ℝ)
    (hg : LocallyIntegrable g μ) (φ : BellmanRealTest) :
    bellmanWeightedTestIntegral μ g φ = ∫ x, φ x * g x ∂μ := by
  exact TestFunction.integralAgainstBilinCLM_eq_integral (hg.locallyIntegrableOn Set.univ)

end HypoellipticAleksandrov.KineticAleksandrov
