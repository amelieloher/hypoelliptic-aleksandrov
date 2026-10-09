module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsConvolutionJets
import Mathlib.Analysis.Normed.Operator.Prod

/-! # Transparent norm bounds for the position-convolution parameter jets -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Set MeasureTheory

/-- A scalar combination of the two coordinate projections has its elementary norm bound. -/
theorem barrier_projection_norm_le (a b : ℝ) :
    ‖a • barrierPositionProjection + b • barrierVelocityProjection‖ ≤ |a| + |b| := by
  exact (norm_add_le _ _).trans_eq (by
    simp only [norm_smul, Real.norm_eq_abs, barrierPositionProjection,
      barrierVelocityProjection, ContinuousLinearMap.norm_fst, ContinuousLinearMap.norm_snd,
      mul_one])

/-- The first convolution jet only needs the value and first velocity fiber majorants. -/
theorem barrierConvolutionJet_norm_le (κ : ℝ → ℝ) (phi : (ℝ × ℝ) → ℝ)
    (q : ℝ × ℝ) (Y : ℝ) :
    ‖barrierConvolutionJet κ phi q Y‖ ≤
      |deriv κ (q.1 - Y)| * |bellmanOriginExtension phi (Y, q.2)| +
        |κ (q.1 - Y)| * |bellmanDv phi (Y, q.2)| := by
  simpa only [barrierConvolutionJet, abs_mul] using
    barrier_projection_norm_le
      (deriv κ (q.1 - Y) * bellmanOriginExtension phi (Y, q.2))
      (κ (q.1 - Y) * bellmanDv phi (Y, q.2))

/-- The second convolution jet needs only the locally integrable second velocity majorant. -/
theorem barrierConvolutionSecondJet_norm_le (κ : ℝ → ℝ) (phi : (ℝ × ℝ) → ℝ)
    (q : ℝ × ℝ) (Y : ℝ) :
    ‖barrierConvolutionSecondJet κ phi q Y‖ ≤
      |deriv (deriv κ) (q.1 - Y)| * |bellmanOriginExtension phi (Y, q.2)| +
        2 * |deriv κ (q.1 - Y)| * |bellmanDv phi (Y, q.2)| +
          |κ (q.1 - Y)| * |bellmanDvv phi (Y, q.2)| := by
  unfold barrierConvolutionSecondJet
  have h1 := barrier_projection_norm_le
    (deriv (deriv κ) (q.1 - Y) * bellmanOriginExtension phi (Y, q.2))
    (deriv κ (q.1 - Y) * bellmanDv phi (Y, q.2))
  have h2 := barrier_projection_norm_le
    (deriv κ (q.1 - Y) * bellmanDv phi (Y, q.2))
    (κ (q.1 - Y) * bellmanDvv phi (Y, q.2))
  have hh := norm_add_le
    ((deriv (deriv κ) (q.1 - Y) * bellmanOriginExtension phi (Y, q.2)) •
      barrierPositionProjection + (deriv κ (q.1 - Y) * bellmanDv phi (Y, q.2)) •
      barrierVelocityProjection |>.smulRight barrierPositionProjection)
    ((deriv κ (q.1 - Y) * bellmanDv phi (Y, q.2)) • barrierPositionProjection +
      (κ (q.1 - Y) * bellmanDvv phi (Y, q.2)) • barrierVelocityProjection
        |>.smulRight barrierVelocityProjection)
  have hX : ‖barrierPositionProjection‖ = 1 := ContinuousLinearMap.norm_fst ℝ ℝ ℝ
  have hv : ‖barrierVelocityProjection‖ = 1 := ContinuousLinearMap.norm_snd ℝ ℝ ℝ
  simp only [ContinuousLinearMap.norm_smulRight_apply, hX, hv, mul_one] at hh
  simp only [abs_mul] at h1 h2
  linarith only [hh, h1, h2]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
