module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsRegularizedBarrier
import Mathlib.MeasureTheory.Group.Integral

/-! # Position convolution preserves the coordinate modulus -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory

/-- The position convolution can integrate the mollifier at a fixed displacement. -/
theorem positionConvolution_displacement (eta : ℝ → ℝ) (Phi : (ℝ × ℝ) → ℝ)
    (q : ℝ × ℝ) :
    positionConvolution eta Phi q = ∫ Y, eta Y * Phi (q.1 - Y, q.2) := by
  have hh := integral_sub_left_eq_self
    (fun Y : ℝ => eta (q.1 - Y) * Phi (Y, q.2)) volume q.1
  simpa only [positionConvolution, sub_sub_cancel] using hh.symm

/-- Continuous barrier fibers against a fixed compact mollifier are genuinely integrable. -/
theorem positionConvolution_displacement_integrable (eta : ℝ → ℝ)
    (heta : IsNonnegativeUnitSmoothMollifier eta) (Phi : (ℝ × ℝ) → ℝ)
    (hPhi : Continuous Phi) (q : ℝ × ℝ) :
    Integrable (fun Y : ℝ => eta Y * Phi (q.1 - Y, q.2)) volume := by
  have hc : Continuous (fun Y : ℝ => eta Y * Phi (q.1 - Y, q.2)) :=
    heta.1.continuous.mul
      (hPhi.comp ((continuous_const.sub continuous_id).prodMk continuous_const))
  exact hc.integrable_of_hasCompactSupport heta.2.1.mul_right

/-- A nonnegative normalized position convolution preserves the same coordinate modulus. -/
theorem positionConvolution_modulus (eta : ℝ → ℝ)
    (heta : IsNonnegativeUnitSmoothMollifier eta) (Phi : (ℝ × ℝ) → ℝ)
    (hPhi : Continuous Phi) (alpha D : ℝ) (hD : 0 ≤ D)
    (hm : ∀ z w : ℝ × ℝ, |Phi z - Phi w| ≤
      D * (|z.1 - w.1| ^ (alpha / 3) + |z.2 - w.2| ^ alpha)) :
    ∀ z w : ℝ × ℝ, |positionConvolution eta Phi z - positionConvolution eta Phi w| ≤
      D * (|z.1 - w.1| ^ (alpha / 3) + |z.2 - w.2| ^ alpha) := by
  intro z w
  let B := D * (|z.1 - w.1| ^ (alpha / 3) + |z.2 - w.2| ^ alpha)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hzi := positionConvolution_displacement_integrable eta heta Phi hPhi z
  have hwi := positionConvolution_displacement_integrable eta heta Phi hPhi w
  have hηi : Integrable eta volume :=
    heta.1.continuous.integrable_of_hasCompactSupport heta.2.1
  have hbd (Y : ℝ) : |eta Y * Phi (z.1 - Y, z.2) - eta Y * Phi (w.1 - Y, w.2)| ≤
      eta Y * B := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (heta.2.2.1 Y)]
    apply mul_le_mul_of_nonneg_left _ (heta.2.2.1 Y)
    have he : z.1 - Y - (w.1 - Y) = z.1 - w.1 := by ring
    simpa only [Prod.fst, Prod.snd, he, B] using hm (z.1 - Y, z.2) (w.1 - Y, w.2)
  rw [positionConvolution_displacement, positionConvolution_displacement,
    ← integral_sub hzi hwi]
  calc
    _ ≤ ∫ Y, |eta Y * Phi (z.1 - Y, z.2) - eta Y * Phi (w.1 - Y, w.2)| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ Y, eta Y * B := integral_mono (hzi.sub hwi).abs (hηi.mul_const B) hbd
    _ = B := by rw [integral_mul_const, heta.2.2.2, one_mul]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
