module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationIntegrals
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationTestDerivatives
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationTestIntegrability
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic

/-! # Separated generator integrals for the actual angular product measures -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- The transport integral factors into the two exact radial and angular terms. -/
theorem bellmanAngularRep_transport_integral (β : ℝ) (F : Measure ℝ)
    [IsFiniteMeasureOnCompacts F] (ζ φ : ℝ → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hcζ : HasCompactSupport ζ) (hcφ : HasCompactSupport φ)
    (hs : tsupport ζ ⊆ Ioi (0 : ℝ)) :
    (∫ q, q.val.2 * fderiv ℝ (bellmanAngularTest ζ φ) q.val (1, 0)
      ∂bellmanAngularRep β F) =
      (1 / 3 : ℝ) * (∫ s, deriv ζ s.val / s.val ∂bellmanRadialWeight β) *
        (∫ y, y * φ y ∂F) -
      (1 / 3 : ℝ) * (∫ s, ζ s.val / s.val ^ 2 ∂bellmanRadialWeight β) *
        (∫ y, y ^ 2 * deriv φ y ∂F) := by
  have hζd := (contDiff_infty_iff_deriv.mp hζ).2
  have hφd := (contDiff_infty_iff_deriv.mp hφ).2
  have hr1 : Integrable (fun s : BellmanPositiveTime => deriv ζ s.val / s.val)
      (bellmanRadialWeight β) := by
    simpa only [pow_one] using bellmanRadialTest_integrable β (deriv ζ)
      hζd.continuous hcζ.deriv (tsupport_deriv_subset.trans hs) 1
  have hr2 := bellmanRadialTest_integrable β ζ hζ.continuous hcζ hs 2
  have ha1 : Integrable (fun y => y * φ y) F := by
    simpa only [pow_one] using bellmanAngularTestFactor_integrable F φ
      hφ.continuous hcφ 1
  have ha2 := bellmanAngularTestFactor_integrable F (deriv φ) hφd.continuous hcφ.deriv 2
  rw [bellmanAngularRep,
    isOpenEmbedding_bellmanAngularPoint.measurableEmbedding.integral_map]
  have hfun : (fun w : BellmanPositiveTime × ℝ => (bellmanAngularPoint w).val.2 *
      fderiv ℝ (bellmanAngularTest ζ φ) (bellmanAngularPoint w).val (1, 0)) =
      (fun w : BellmanPositiveTime × ℝ =>
        (1 / 3 : ℝ) * (deriv ζ w.1.val / w.1.val * (w.2 * φ w.2)) -
        (1 / 3 : ℝ) * (ζ w.1.val / w.1.val ^ 2 * (w.2 ^ 2 * deriv φ w.2))) := by
    funext w
    rw [bellmanAngularTest_transport ζ φ hζ hφ w]
    ring
  rw [hfun, integral_sub ((hr1.mul_prod ha1).const_mul (1 / 3 : ℝ))
    ((hr2.mul_prod ha2).const_mul (1 / 3 : ℝ)), integral_const_mul, integral_const_mul,
    integral_prod_mul (fun s : BellmanPositiveTime => deriv ζ s.val / s.val)
      (fun y : ℝ => y * φ y),
    integral_prod_mul (fun s : BellmanPositiveTime => ζ s.val / s.val ^ 2)
      (fun y : ℝ => y ^ 2 * deriv φ y)]
  ring

/-- The second velocity integral factors with the same radial multiplier as the angular
equation. -/
theorem bellmanAngularRep_velocity_integral (β : ℝ) (H : Measure ℝ) [SFinite H]
    (ζ φ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    (∫ q, fderiv ℝ (fun z => fderiv ℝ (bellmanAngularTest ζ φ) z (0, 1))
      q.val (0, 1) ∂bellmanAngularRep β H) =
      (∫ s, ζ s.val / s.val ^ 2 ∂bellmanRadialWeight β) *
        (∫ y, deriv (deriv φ) y ∂H) := by
  rw [bellmanAngularRep,
    isOpenEmbedding_bellmanAngularPoint.measurableEmbedding.integral_map]
  have hfun : (fun w : BellmanPositiveTime × ℝ =>
      fderiv ℝ (fun z => fderiv ℝ (bellmanAngularTest ζ φ) z (0, 1))
        (bellmanAngularPoint w).val (0, 1)) =
      (fun w : BellmanPositiveTime × ℝ =>
        (ζ w.1.val / w.1.val ^ 2) * deriv (deriv φ) w.2) := by
    funext w
    rw [bellmanAngularTest_velocity_second ζ φ hζ hφ w]
    ring
  rw [hfun]
  exact integral_prod_mul (fun s : BellmanPositiveTime => ζ s.val / s.val ^ 2)
    (deriv (deriv φ))

end HypoellipticAleksandrov.KineticAleksandrov
