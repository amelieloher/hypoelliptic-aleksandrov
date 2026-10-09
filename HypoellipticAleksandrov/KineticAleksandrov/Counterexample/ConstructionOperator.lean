module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionTimeConvergence
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.SmoothFunctions

/-! # The literal backward operator of the spatially smoothed zero extension -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open HypoellipticAleksandrov.Parabolic

/-- The exact smoothed operator uses convolution of the same three selected weak jets.
Transport retains the velocity of the evaluation point; coefficients are not convolved. -/
theorem construction_smoothed_operator_eq {d : ℕ} (hd : 1 ≤ d)
    {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r mu R m : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2)
    (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 ≤ m)
    (phi : ContDiffBump (0 : XV d)) (A : XV d → PDE.Mat d) (P : KineticPoint d) :
    backwardOperator (fun _t x v => A (x, v)) (smoothedZeroExtendedProfile h r mu R phi) P =
      spatialMollify phi (constructionExtendedTimeJet h r mu R P.time) (P.position, P.velocity) +
      PDE.vecDot P.velocity (fun i => spatialMollify phi
        (fun y => constructionExtendedNativeGradient h r mu R m P.time y (Fin.castAdd d i))
          (P.position, P.velocity)) -
      matrixContraction (A (P.position, P.velocity)) (fun i k => spatialMollify phi
        (fun y => constructionExtendedNativeHessian h r mu R m P.time y i k)
          (P.position, P.velocity)) := by
  let f := spatialMollify phi (fun y =>
    zeroExtendedProfile (profileFunction h) alpha r mu R ⟨P.time, y.1, y.2⟩)
  have hc : ContDiff ℝ (⊤ : ℕ∞) f := spatialMollify_contDiff phi _
    (continuous_zeroExtendedProfile_spatial_of_profile h r mu R hr hmu hR hscale
      (fun y hy => (hmargin y hy).trans_lt hm) P.time).locallyIntegrable
  have hdt : kineticTimeDerivative (smoothedZeroExtendedProfile h r mu R phi) P =
      spatialMollify phi (constructionExtendedTimeJet h r mu R P.time)
        (P.position, P.velocity) :=
    construction_mollified_time_jet ha h r mu R hr hmu hR
      (fun y hy => (hmargin y hy).trans_lt hm) phi P.time (P.position, P.velocity)
  have hx : kineticPositionGradient (smoothedZeroExtendedProfile h r mu R phi) P =
      fun i => spatialMollify phi (fun y =>
        constructionExtendedNativeGradient h r mu R m P.time y (Fin.castAdd d i))
          (P.position, P.velocity) := by
    have he := dx_eq_classicalGradient_at f (P.position, P.velocity)
      (hc.differentiable (by simp)).differentiableAt
    change dx f (P.position, P.velocity) =
      kineticPositionGradient (smoothedZeroExtendedProfile h r mu R phi) P at he
    rw [← he]
    funext i
    have hj := construction_mollified_first_jet hd ha ha1 h r mu R m hr hmu hR hm
      hscale hmargin P.time (Fin.castAdd d i) phi (P.position, P.velocity)
    rw [spatialCoordinate_basis_position] at hj
    simpa only [dx, PDE.basisVec, f] using! hj
  have hh : kineticVelocityHessian (smoothedZeroExtendedProfile h r mu R phi) P =
      fun i k => spatialMollify phi (fun y =>
        constructionExtendedNativeHessian h r mu R m P.time y i k)
          (P.position, P.velocity) := by
    have he := dvv_eq_sliceHessian_at f (P.position, P.velocity)
      (hc.of_le (by simp)).contDiffAt
    change dvv f (P.position, P.velocity) =
      kineticVelocityHessian (smoothedZeroExtendedProfile h r mu R phi) P at he
    rw [← he]
    funext i k
    exact construction_mollified_second_velocity_jet hd ha ha1 h r mu R m hr hmu hR hm
      hscale hmargin P.time i k phi (P.position, P.velocity)
  rw [backwardOperator_apply, hdt, hx, hh]
  rfl

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
