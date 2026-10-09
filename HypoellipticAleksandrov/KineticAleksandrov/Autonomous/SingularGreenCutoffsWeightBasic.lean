module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsMollifier
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.DeterministicBoxOccupationGeometry
import Mathlib.MeasureTheory.Integral.Prod

/-! # The literal regularized singular weight, with all measurability discharged -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory Set

/-- A measurable position convolution is a measurable physical-plane function. -/
theorem positionConvolution_measurable (eta : ℝ → ℝ) (heta : Measurable eta)
    (Phi : Z → ℝ) (hPhi : Measurable Phi) : Measurable (positionConvolution eta Phi) := by
  have hm : Measurable (fun p : Z × ℝ => eta (p.1.1 - p.2) * Phi (p.2, p.1.2)) :=
    (heta.comp ((measurable_fst.comp measurable_fst).sub measurable_snd)).mul
      (hPhi.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- The actual source singular-weight regularization at the n-th position scale. -/
def regularizedBarrierWeight (alpha : ℝ) (n : ℕ) : Z → ℝ :=
  positionConvolution (barrierMollifier n) (fun q => bellmanGauge q ^ (alpha - 2))

/-- The regularized weight is measurable in the physical plane. -/
theorem regularizedBarrierWeight_measurable (alpha : ℝ) (n : ℕ) :
    Measurable (regularizedBarrierWeight alpha n) :=
  positionConvolution_measurable _ (barrierMollifier_spec n).1.continuous.measurable _
    (bellmanGauge_continuous.measurable.pow_const _)

/-- The regularized weight is nonnegative at every physical point. -/
theorem regularizedBarrierWeight_nonneg (alpha : ℝ) (n : ℕ) (q : Z) :
    0 ≤ regularizedBarrierWeight alpha n q :=
  integral_nonneg (fun _ => mul_nonneg ((barrierMollifier_spec n).2.2.1 _)
    (Real.rpow_nonneg (bellmanGauge_nonneg _) _))

/-- On the zero-velocity axis, the weight has precisely the integrable position power. -/
theorem barrier_weight_position_axis (beta X : ℝ) :
    bellmanGauge (X, 0) ^ beta = |X| ^ (beta / 3) := by
  have he : X ^ 2 = |X| ^ 2 := (sq_abs X).symm
  simp only [bellmanGauge, bellmanGaugePower, zero_pow (by decide : 6 ≠ 0),
    add_zero, he]
  rw [← Real.rpow_natCast_mul (abs_nonneg X), ← Real.rpow_mul (abs_nonneg X)]
  congr 1
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
