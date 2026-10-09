module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.NormNum

/-! # Literal square integrals and restricted L2 norms

These identities translate the localized value, gradient, and Hessian estimates to the
norms stored in the weak-derivative families.
-/

@[expose] public section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open MeasureTheory

/-- The literal real square integral is the square of the real L2 seminorm. -/
theorem integral_square_eq_eLpNorm_two_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (f : α → ℝ) (hf : MemLp f 2 μ) :
    (∫ x, f x ^ 2 ∂μ) = (eLpNorm f 2 μ).toReal ^ 2 := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofReal (Real.rpow_nonneg
    (integral_nonneg fun _ => sq_nonneg _) _), ENNReal.toReal_ofNat,
    Real.norm_eq_abs, Real.rpow_two, sq_abs]
  exact (Real.rpow_inv_natCast_pow
    (integral_nonneg fun _ => sq_nonneg _) (by norm_num)).symm

/-- A finite-measure carrier and a value bound give a literal uniform square integral. -/
theorem integral_square_le_measure_mul_bound_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] (f : α → ℝ) (hf : MemLp f 2 μ)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ᵐ x ∂μ, |f x| ≤ B) :
    (∫ x, f x ^ 2 ∂μ) ≤ (μ Set.univ).toReal * B ^ 2 := by
  have hi : Integrable (fun x => f x ^ 2) μ := by
    simpa only [Real.norm_eq_abs, sq_abs] using hf.integrable_norm_pow (by norm_num)
  have hp : ∀ᵐ x ∂μ, f x ^ 2 ≤ B ^ 2 := hb.mono fun x hx => by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).2 hx
  have h := integral_mono_ae hi (integrable_const (B ^ 2)) hp
  simpa only [integral_const, smul_eq_mul, measureReal_def] using h

end HypoellipticAleksandrov.Parabolic.LocalHolder
