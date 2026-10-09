module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.GeometryAPI
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # The Green-density Hölder bound used by abstract Aleksandrov comparison -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory

/-- The real-valued seminorm formula for an a.e. nonnegative real source. -/
theorem abp_eLpNorm_toReal_nonneg {E : Type*} [MeasurableSpace E]
    {μ : Measure E} {g : E → ℝ} {p : ℝ} (hp : 0 < p)
    (hg : MemLp g (ENNReal.ofReal p) μ) (hnn : ∀ᵐ x ∂μ, 0 ≤ g x) :
    (eLpNorm g (ENNReal.ofReal p) μ).toReal = (∫ x, g x ^ p ∂μ) ^ (1 / p) := by
  rw [hg.eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_pos.mpr hp).ne'
    ENNReal.ofReal_ne_top]
  simp only [ENNReal.toReal_ofReal hp.le]
  have hi : 0 ≤ ∫ x, ‖g x‖ ^ p ∂μ :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hi _)]
  simp only [one_div]
  congr 1
  apply integral_congr_ae
  filter_upwards [hnn] with x hx
  rw [Real.norm_of_nonneg hx]

/-- A positive Green density with its source norm bound gives the potential estimate. -/
theorem abp_potential_holder {E : Type*} [MeasurableSpace E]
    (μ Γ : Measure E) (G g : E → ℝ) {q p K : ℝ} (hpq : q.HolderConjugate p)
    (hG : Measurable G) (hG0 : ∀ x, 0 ≤ G x) (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hΓ : Γ = μ.withDensity (fun x => ENNReal.ofReal (G x)))
    (hGq : MemLp G (ENNReal.ofReal q) μ) (hgp : MemLp g (ENNReal.ofReal p) μ)
    (hbound : (eLpNorm G (ENNReal.ofReal q) μ).toReal ≤ K) :
    ∫ x, g x ∂Γ ≤ K * (eLpNorm g (ENNReal.ofReal p) μ).toReal := by
  rw [hΓ,integral_withDensity_eq_integral_toReal_smul (hG.ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have heq : (fun x => (ENNReal.ofReal (G x)).toReal • g x) = fun x => G x * g x := by
    funext x
    rw [ENNReal.toReal_ofReal (hG0 x)]
    rfl
  rw [heq]
  have hnn : ∀ᵐ x ∂μ, 0 ≤ G x := Filter.Eventually.of_forall hG0
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hpq hnn hg0 hGq hgp
  rw [← abp_eLpNorm_toReal_nonneg hpq.pos hGq hnn,
    ← abp_eLpNorm_toReal_nonneg hpq.symm.pos hgp hg0] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right hbound ENNReal.toReal_nonneg)

end HypoellipticAleksandrov.KineticAleksandrov
