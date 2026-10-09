module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsConvolutionC2
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionMollification

/-! # Joint-plane regularity of the position-regularized barrier -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov

/-- The position convolution agrees with the literal parameter integral. -/
theorem positionConvolution_barrier_eq (eta : ℝ → ℝ) (phi : (ℝ × ℝ) → ℝ) :
    positionConvolution eta (bellmanOriginExtension phi) =
      positionBarrierConvolution eta phi := rfl

/-- Position smoothing has joint C² regularity required by the compact Green API. -/
theorem barrier_position_regularization_joint {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) (ha : 0 < alpha) (ha1 : alpha < 1)
    (eta : ℝ → ℝ) (heta : IsNonnegativeUnitSmoothMollifier eta) :
    ContDiff ℝ 2 (positionConvolution eta (bellmanOriginExtension phi)) := by
  rw [positionConvolution_barrier_eq]
  exact positionBarrierConvolution_contDiff h ha ha1 eta
    (heta.1.of_le (by simp)) heta.2.1

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
