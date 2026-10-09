module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationTestSupport
import Mathlib.Tactic

/-! # Exact derivatives of the smooth zero-extended source tests -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Filter
open scoped Topology

/-- The zero extension has the exact source transport derivative at every angular point. -/
theorem bellmanAngularTest_transport (ζ φ : ℝ → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (w : BellmanPositiveTime × ℝ) :
    (bellmanAngularPoint w).val.2 *
      fderiv ℝ (bellmanAngularTest ζ φ) (bellmanAngularPoint w).val (1, 0) =
      w.2 / (3 * w.1.val) * deriv ζ w.1.val * φ w.2 -
        w.2 ^ 2 / (3 * w.1.val ^ 2) * ζ w.1.val * deriv φ w.2 := by
  have he := bellmanAngularTest_eventuallyEq_positive ζ φ (bellmanAngularPoint w).val
    (pow_pos w.1.property 3)
  rw [he.fderiv_eq]
  exact bellmanSeparatedExpression_transport ζ φ w
    (hζ.differentiable (by simp) _) (hφ.differentiable (by simp) _)

/-- The second velocity derivative of the zero extension is exactly ζ(s)φ''(y)/s². -/
theorem bellmanAngularTest_velocity_second (ζ φ : ℝ → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (w : BellmanPositiveTime × ℝ) :
    fderiv ℝ (fun q => fderiv ℝ (bellmanAngularTest ζ φ) q (0, 1))
      (bellmanAngularPoint w).val (0, 1) =
      ζ w.1.val * deriv (deriv φ) w.2 / w.1.val ^ 2 := by
  have he := bellmanAngularTest_eventuallyEq_positive ζ φ (bellmanAngularPoint w).val
    (pow_pos w.1.property 3)
  have hf : (fun q => fderiv ℝ (bellmanAngularTest ζ φ) q (0, 1)) =ᶠ[
      𝓝 (bellmanAngularPoint w).val]
      (fun q => fderiv ℝ (bellmanSeparatedExpression ζ φ) q (0, 1)) := by
    filter_upwards [he.fderiv (𝕜 := ℝ)] with q hq
    exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0, 1)) hq
  rw [hf.fderiv_eq]
  exact bellmanSeparatedExpression_velocity_second ζ φ hζ hφ w

end HypoellipticAleksandrov.KineticAleksandrov
