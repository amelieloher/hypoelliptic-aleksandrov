module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionBounded
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitMeasureSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripMassQuadratic

/-! # Exact first moment of the actual finite-horizon exit time -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic
open SectionTwo TheoremA Evolution

/-- The literal time coordinate has scalar forward operator one. -/
theorem nested_time_operator (a : ℝ → ℝ → ℝ) (p : Point) :
    forwardScalarOperator a (fun p => p.time) p = 1 := by
  have ht : kineticTimeDerivative (fun p : Point => p.time) p = 1 := by
    change deriv (fun t : ℝ => t) p.time = 1
    exact deriv_id _
  have hx : kineticPositionGradient (fun p : Point => p.time) p 0 = 0 := by
    rw [kineticPositionGradient_scalar]
    exact deriv_const _ _
  have hv : kineticVelocityHessian (fun p : Point => p.time) p 0 0 = 0 := by
    rw [kineticVelocityHessian_scalar]
    have hd : deriv (fun _ : ℝ => p.time) = fun _ => 0 :=
      funext (fun v => deriv_const v p.time)
    rw [hd]
    exact deriv_const _ _
  simp only [forwardScalarOperator, ht, hx, hv, mul_zero, add_zero]

/-- The expected exit time is the pole time plus the actual Green mass. -/
theorem nested_exit_time_integral
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    (∫ p, p.time ∂stripExitOfRealization hH hlam hLam A H E hE T e) =
      e.1.time + (stripGreenOfKernel H E.2 T e univ).toReal := by
  have h := strip_identity_bounded_smooth_future_of_realization hH hlam hLam A H E hE
    T e (fun p => p.time) (Evolution.timeCoord 1).contDiff (by
      refine ⟨max |e.1.time| |T| + 1, fun p ht hT _ => ?_⟩
      constructor
      · have hp := abs_le.mpr (show -max |e.1.time| |T| ≤ p.time ∧
            p.time ≤ max |e.1.time| |T| from
          ⟨(neg_le_neg (le_max_left _ _)).trans ((neg_abs_le _).trans ht),
            hT.trans ((le_abs_self _).trans (le_max_right _ _))⟩)
        linarith
      · rw [nested_time_operator, abs_one]
        have hm : 0 ≤ max |e.1.time| |T| := (abs_nonneg _).trans (le_max_left _ _)
        linarith)
  simp only [nested_time_operator, integral_const, Measure.real, smul_eq_mul, mul_one] at h
  linarith

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
