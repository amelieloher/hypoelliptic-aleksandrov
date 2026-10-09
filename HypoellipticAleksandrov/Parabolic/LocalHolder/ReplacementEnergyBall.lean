module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementEnergyInterior
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonBarrierPointwise
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonBallBarrierSobolev
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.LocalizedKrylovGeometry

/-! # Signed smooth corrections with both ball boundary envelopes

The internally proved energy solver gives the literal classical equation and both
the temporal and Euclidean spatial estimates, for sources reaching the boundary.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set Dirichlet KineticAleksandrov
open scoped ENNReal MatrixOrder Matrix.Norms.Elementwise

/-- Smooth signed forcing admits an interior classical correction with both zero-trace bounds. -/
theorem exists_signed_source_ballInterior_with_bounds {d : ℕ} (hd : 0 < d)
    (v₀ : PDE.Vec d) (r : ℝ) (hr : 0 < r) (a T : ℝ) (haT : a < T)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : CoefficientField d) (hA : IsSmoothCoefficient A)
    (hlo : HasLowerEllipticity lam A) (hhi : HasUpperEllipticity Lam A)
    (F : TimeVelocity d → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (M : ℝ) (hM : 0 ≤ M)
    (hFM : ∀ z ∈ scalarParabolicClosedCylinder a T (PDE.euclideanBall v₀ r), |F z| ≤ M) :
    ∃ w : TimeVelocity d → ℝ,
      IsScalarC12On w (scalarParabolicOpenCylinder a T (PDE.euclideanBall v₀ r)) ∧
      (∀ z ∈ scalarParabolicOpenCylinder a T (PDE.euclideanBall v₀ r),
        scalarTimeDerivative w z +
          matrixContraction (coefficientAt A z) (scalarSpatialHessian w z) = F z) ∧
      (∀ z ∈ scalarParabolicOpenCylinder a T (PDE.euclideanBall v₀ r),
        |w z| ≤ M * (T - z.1)) ∧
      ∀ z ∈ scalarParabolicOpenCylinder a T (PDE.euclideanBall v₀ r),
        |w z| ≤ sourceBallBarrier v₀ r lam M z.2 := by
  let Ω := PDE.euclideanBall v₀ r
  have hΩ : IsOpen Ω := PDE.isOpen_euclideanBall v₀ r
  have hΩb : Bornology.IsBounded Ω := Occupation.isBounded_euclideanBall v₀ hr
  obtain ⟨u, g, hdu, hu, w, _, hs, hw, he⟩ := exists_signed_source_classicalInterior
    hd hΩ hΩb a T haT lam Lam hlam hLam A hA hlo hhi F hF
  have htime := classicalEnergyRepresentative_abs_le_source_time hΩ hΩb a T lam haT
    hlam A hA hlo F hF M hM hFM u g hdu hu w hw.continuousOn hs
  obtain ⟨q, hq, hqe, hqo⟩ := exists_h10_sourceBallBarrier v₀ r lam M hr hlam hM A
  let G := sourceBallBarrierForcing lam M A
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := contDiff_sourceBallBarrierForcing lam M A hA
  have hqn : ∀ y ∈ Ω, 0 ≤ q.toH1Function.toFun y := by
    intro y hy
    rw [hqe (subset_closure hy)]
    exact sourceBallBarrier_nonneg v₀ r lam M hlam hM (subset_closure hy)
  have hqeq : ∀ z ∈ Icc a T ×ˢ Ω,
      scalarParabolicZeroOrderOperator A (fun _ _ => 0) (fun _ _ => 0)
        (fun z => q.toH1Function.toFun z.2) z = G z := fun z hz => hqo z hz.2
  have hGF : ∀ z ∈ scalarParabolicClosedCylinder a T Ω, G z ≤ -|F z| := by
    intro z hz
    have hGle : G z ≤ -M := by
      change sourceBallBarrierForcing lam M A z ≤ -M
      rw [show sourceBallBarrierForcing lam M A z =
        scalarParabolicZeroOrderOperator A (fun _ _ => 0) (fun _ _ => 0)
          (fun z => sourceBallBarrier v₀ r lam M z.2) z from
            (scalarOperator_sourceBallBarrier v₀ r lam M A z).symm]
      exact scalarOperator_sourceBallBarrier_le hd v₀ r lam M hlam hM A hlo z
    exact hGle.trans (neg_le_neg (hFM z hz))
  have henergy := variationalEnergySolution_abs_le_stationary_barrier hΩ hΩb a T haT
    lam hlam A hA hlo F G hF hG q (hq.of_le (by simp)) hqn hqeq hGF u g hdu hu
  have hspace := classicalEnergyRepresentative_abs_le_continuous_barrier hΩ a T haT
    u g hdu q.toH1Function.toFun hq.continuous henergy w hw.continuousOn hs
  refine ⟨w, hw, he, htime, ?_⟩
  intro z hz
  simpa only [hqe (subset_closure hz.2)] using hspace z hz

end HypoellipticAleksandrov.Parabolic.LocalHolder
