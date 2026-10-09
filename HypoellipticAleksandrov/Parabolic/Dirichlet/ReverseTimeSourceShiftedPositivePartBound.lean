module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialL2Mass
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialForm

/-!
# Reverse-time source bound on shifted positive parts

This file bounds the negative reverse-time source functional on a shifted
positive part by its spatial mass under an almost-everywhere source bound.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The negative reverse-time source functional on a shifted positive part is
bounded by the source amplitude times its spatial mass. -/
theorem reverseTimeSourceFunctional_apply_shiftedPositivePart_le_mass_of_ae_abs_le
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (f : PDE.ScalarLp Ω (2 : ℝ≥0∞)) (MF : ℝ≥0)
    (hf : ∀ᵐ y ∂PDE.volumeOn Ω, |f y| ≤ (MF : ℝ))
    (u : H10HilbertGraph hΩ) (k : ℝ≥0) :
    reverseTimeSourceFunctional hΩ f
        (h10ShiftedPositivePart hΩ u k) ≤
      (MF : ℝ) * spatialMassCLM hΩbounded
        (valueCLM hΩ (h10ShiftedPositivePart hΩ u k)) := by
  let w : PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
    valueCLM hΩ (h10ShiftedPositivePart hΩ u k)
  letI : IsFiniteMeasure (PDE.volumeOn Ω) :=
    isFiniteMeasure_restrict.mpr hΩbounded.measure_lt_top.ne
  have hwNonneg : ∀ᵐ y ∂PDE.volumeOn Ω, 0 ≤ w y := by
    filter_upwards [coeFn_valueCLM_h10ShiftedPositivePart hΩ u k] with y hy
    rw [show w y = max (valueCLM hΩ u y - (k : ℝ)) 0 by exact hy]
    exact le_max_right _ _
  have hwIntegrable : Integrable (fun y => w y) (PDE.volumeOn Ω) :=
    (Lp.memLp w).integrable (by norm_num)
  rw [reverseTimeSourceFunctional_apply, L2.inner_def,
    spatialMassCLM_apply, ← integral_neg, ← integral_const_mul]
  apply integral_mono_ae
    (L2.integrable_inner (𝕜 := ℝ) w f).neg
    (hwIntegrable.const_mul (MF : ℝ))
  filter_upwards [hf, hwNonneg] with y hyf hyw
  simp only [RCLike.inner_apply, conj_trivial]
  calc
    -(f y * w y) ≤ w y * |f y| := by
      simpa only [mul_comm, neg_mul] using
        (mul_le_mul_of_nonneg_left (neg_le_abs (f y)) hyw)
    _ ≤ w y * (MF : ℝ) := mul_le_mul_of_nonneg_left hyf hyw
    _ = (MF : ℝ) * w y := mul_comm _ _

end HypoellipticAleksandrov.Parabolic.Dirichlet
