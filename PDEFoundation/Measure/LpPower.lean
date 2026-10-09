module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Finite-exponent `L^p` power identities

This file relates Mathlib's extended-real `eLpNorm` to the usual real
integral-power expression when the exponent is a positive real number and the
function belongs to `L^p`.

The statements are measure-generic so that both restricted volume and
normalized restricted volume can reuse them without duplicating coercion
bookkeeping.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open Filter MeasureTheory

/-- For a positive finite real exponent, the real value of `eLpNorm` is the
usual integral-power expression. -/
theorem toReal_eLpNorm_ofReal_eq_integral_rpow_norm_rpow_inv
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f : α → E} {p : ℝ} (hp : 0 < p)
    (hf : MemLp f (ENNReal.ofReal p) μ) :
    (eLpNorm f (ENNReal.ofReal p) μ).toReal =
      (∫ x, ‖f x‖ ^ p ∂μ) ^ (1 / p : ℝ) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    intro hzero
    exact (not_le_of_gt hp) (ENNReal.ofReal_eq_zero.mp hzero)
  have hpReal : (ENNReal.ofReal p).toReal = p :=
    ENNReal.toReal_ofReal hp.le
  rw [hf.eLpNorm_eq_integral_rpow_norm hp0 ENNReal.ofReal_ne_top]
  have hnonneg :
      0 ≤
        (∫ x, ‖f x‖ ^ (ENNReal.ofReal p).toReal ∂μ) ^
          ((ENNReal.ofReal p).toReal)⁻¹ := by
    positivity
  rw [ENNReal.toReal_ofReal hnonneg, hpReal]
  simp only [one_div]

/-- Raising the real `L^p` norm to the exponent recovers the integral of the
`p`th power. -/
theorem toReal_eLpNorm_ofReal_rpow_eq_integral_rpow_norm
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f : α → E} {p : ℝ} (hp : 0 < p)
    (hf : MemLp f (ENNReal.ofReal p) μ) :
    (eLpNorm f (ENNReal.ofReal p) μ).toReal ^ p =
      ∫ x, ‖f x‖ ^ p ∂μ := by
  rw [toReal_eLpNorm_ofReal_eq_integral_rpow_norm_rpow_inv hp hf]
  have hintegralNonneg :
      0 ≤ ∫ x, ‖f x‖ ^ p ∂μ :=
    integral_nonneg_of_ae <|
      Filter.Eventually.of_forall fun x =>
        Real.rpow_nonneg (norm_nonneg _) _
  rw [← Real.rpow_mul hintegralNonneg]
  have hpNe : p ≠ 0 :=
    hp.ne'
  rw [show (1 / p : ℝ) * p = 1 by field_simp [hpNe]]
  simp only [Real.rpow_one]

/-- For a real-valued `L²` function, the square of the real value of its
extended `L²` norm is exactly the integral of its pointwise square. -/
theorem toReal_eLpNorm_two_sq_eq_integral_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : MemLp f 2 μ) :
    (eLpNorm f 2 μ).toReal ^ 2 =
      ∫ x, f x ^ 2 ∂μ := by
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa only [ENNReal.ofReal_ofNat] using hf
  have h :=
    toReal_eLpNorm_ofReal_rpow_eq_integral_rpow_norm
      (p := (2 : ℝ)) (by norm_num) hf'
  simpa only [ENNReal.ofReal_ofNat, Real.rpow_two,
    Real.norm_eq_abs, sq_abs] using h

/-- If the squared integrals of a family of genuine scalar `L²` functions
converge to zero, then their extended `L²` seminorms converge to zero. -/
theorem tendsto_eLpNorm_two_zero_of_tendsto_integral_sq
    {ι α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : ι → α → ℝ} {l : Filter ι}
    (hf : ∀ i, MemLp (f i) 2 μ)
    (hIntegral :
      Tendsto (fun i => ∫ x, f i x ^ 2 ∂μ) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (f i) 2 μ) l (𝓝 0) := by
  apply (ENNReal.tendsto_toReal_zero_iff
    (fun i => (hf i).eLpNorm_ne_top)).mp
  have hSqrt :
      Tendsto
        (fun i => Real.sqrt (∫ x, f i x ^ 2 ∂μ))
        l (𝓝 0) := by
    simpa only [Real.sqrt_zero] using!
      (Real.continuous_sqrt.tendsto 0).comp hIntegral
  have hPointwise :
      (fun i => (eLpNorm (f i) 2 μ).toReal) =
        fun i => Real.sqrt (∫ x, f i x ^ 2 ∂μ) := by
    funext i
    rw [← toReal_eLpNorm_two_sq_eq_integral_sq (hf i)]
    exact (Real.sqrt_sq ENNReal.toReal_nonneg).symm
  rw [hPointwise]
  exact hSqrt

end PDE
