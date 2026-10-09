module

public import PDEFoundation.Measure.LpPower
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Intermediate density exponents on an infinite slab

An elementary interpolation estimate uses the split at unit size after normalization.
Unlike finite-measure exponent comparison, it applies to the infinite-volume slab.
The factor two is harmless since the occupation conditions leaves its constants unspecified.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Filter
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {g : α → ℝ}

/-- Unit `L¹` and `Lʳ` bounds imply a uniform bound at every intervening exponent. -/
theorem memLp_intermediate_of_unit_bounds {r γ : ℝ} (hr : 1 < r)
    (hγ : 1 ≤ γ) (hγr : γ ≤ r) (h1 : MemLp g 1 μ)
    (hrLp : MemLp g (ENNReal.ofReal r) μ)
    (h1n : (eLpNorm g 1 μ).toReal ≤ 1)
    (hrn : (eLpNorm g (ENNReal.ofReal r) μ).toReal ≤ 1) :
    MemLp g (ENNReal.ofReal γ) μ ∧
      (eLpNorm g (ENNReal.ofReal γ) μ).toReal ≤ 2 := by
  have hγpos : 0 < γ := zero_lt_one.trans_le hγ
  have hrpos : 0 < r := zero_lt_one.trans hr
  have hgr : Integrable (fun x => ‖g x‖ ^ r) μ := by
    simpa only [ENNReal.toReal_ofReal hrpos.le] using
      (memLp_one_iff_integrable.1 (hrLp.norm_rpow
        (ne_of_gt (ENNReal.ofReal_pos.2 hrpos)) ENNReal.ofReal_ne_top))
  have hg1 : Integrable (fun x => ‖g x‖) μ := (memLp_one_iff_integrable.1 h1).norm
  have hpoint (x : α) : ‖g x‖ ^ γ ≤ ‖g x‖ + ‖g x‖ ^ r := by
    by_cases hx : ‖g x‖ ≤ 1
    · exact (Real.rpow_le_self_of_le_one (norm_nonneg _) hx hγ).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg _) _))
    · exact (Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx) hγr).trans
        (le_add_of_nonneg_left (norm_nonneg _))
  have hpowmeas : AEStronglyMeasurable (fun x => ‖g x‖ ^ γ) μ :=
    (Real.continuous_rpow_const hγpos.le).comp_aestronglyMeasurable h1.aestronglyMeasurable.norm
  have hgγ : Integrable (fun x => ‖g x‖ ^ γ) μ :=
    (hg1.add hgr).mono' hpowmeas (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      exact hpoint x)
  have hγLp : MemLp g (ENNReal.ofReal γ) μ := by
    apply (integrable_norm_rpow_iff h1.aestronglyMeasurable
      (ne_of_gt (ENNReal.ofReal_pos.2 hγpos)) ENNReal.ofReal_ne_top).1
    simpa only [ENNReal.toReal_ofReal hγpos.le] using hgγ
  have hint : (∫ x, ‖g x‖ ^ γ ∂μ) ≤ 2 := by
    calc
      _ ≤ ∫ x, ‖g x‖ + ‖g x‖ ^ r ∂μ := integral_mono hgγ (hg1.add hgr) hpoint
      _ = (eLpNorm g 1 μ).toReal +
          (eLpNorm g (ENNReal.ofReal r) μ).toReal ^ r := by
        rw [integral_add hg1 hgr,
          ← PDE.toReal_eLpNorm_ofReal_rpow_eq_integral_rpow_norm hrpos hrLp]
        have heq := PDE.toReal_eLpNorm_ofReal_rpow_eq_integral_rpow_norm
          (p := 1) zero_lt_one (by simpa using h1)
        simpa using congrArg (fun a => a + (eLpNorm g (ENNReal.ofReal r) μ).toReal ^ r)
          heq.symm
      _ ≤ 2 := by
        have hb : (eLpNorm g (ENNReal.ofReal r) μ).toReal ^ r ≤ 1 := by
          simpa only [Real.one_rpow] using Real.rpow_le_rpow ENNReal.toReal_nonneg hrn hrpos.le
        linarith
  refine ⟨hγLp, ?_⟩
  have hp := PDE.toReal_eLpNorm_ofReal_rpow_eq_integral_rpow_norm hγpos hγLp
  have htwo : (2 : ℝ) ≤ 2 ^ γ := Real.self_le_rpow_of_one_le (by norm_num) hγ
  have hn : (eLpNorm g (ENNReal.ofReal γ) μ).toReal ^ γ ≤ 2 ^ γ := by
    rw [hp]
    exact hint.trans htwo
  exact (Real.rpow_le_rpow_iff ENNReal.toReal_nonneg (by norm_num) hγpos).mp hn

/-- Multiplication by a scalar scales the real `Lp` norm by its absolute value. -/
theorem toReal_eLpNorm_const_mul (c : ℝ) (f : α → ℝ) (p : ℝ≥0∞) (μ : Measure α) :
    (eLpNorm (fun x => c * f x) p μ).toReal = |c| * (eLpNorm f p μ).toReal := by
  change (eLpNorm (c • f) p μ).toReal = _
  rw [eLpNorm_const_smul, ENNReal.toReal_mul, toReal_enorm, Real.norm_eq_abs]

/-- Two endpoint bounds of size `A` give an intermediate bound of size `2A`, even
when the reference measure has infinite mass. -/
theorem memLp_intermediate_of_bounds {r γ A : ℝ} (hr : 1 < r)
    (hγ : 1 ≤ γ) (hγr : γ ≤ r) (hA : 0 ≤ A) (h1 : MemLp g 1 μ)
    (hrLp : MemLp g (ENNReal.ofReal r) μ)
    (h1n : (eLpNorm g 1 μ).toReal ≤ A)
    (hrn : (eLpNorm g (ENNReal.ofReal r) μ).toReal ≤ A) :
    MemLp g (ENNReal.ofReal γ) μ ∧
      (eLpNorm g (ENNReal.ofReal γ) μ).toReal ≤ 2 * A := by
  rcases hA.eq_or_lt with hAz | hAp
  · have hzero : eLpNorm g 1 μ = 0 := by
      apply (ENNReal.toReal_eq_zero_iff _).mp (le_antisymm
        (h1n.trans (by rw [← hAz])) ENNReal.toReal_nonneg) |>.resolve_right
        h1.eLpNorm_ne_top
    have hae := (eLpNorm_eq_zero_iff one_ne_zero).mp hzero
    have hn : eLpNorm g (ENNReal.ofReal γ) μ = 0 := by
      rw [eLpNorm_congr_ae hae]
      simp
    refine ⟨by rw [memLp_iff, hn]; exact ENNReal.zero_lt_top, ?_⟩
    rw [hn, ENNReal.toReal_zero, ← hAz, mul_zero]
  · let f : α → ℝ := fun x => A⁻¹ * g x
    have hf1 : MemLp f 1 μ := h1.const_mul _
    have hfr : MemLp f (ENNReal.ofReal r) μ := hrLp.const_mul _
    have hfn (p : ℝ≥0∞) (hn : (eLpNorm g p μ).toReal ≤ A) :
        (eLpNorm f p μ).toReal ≤ 1 := by
      rw [toReal_eLpNorm_const_mul, abs_of_pos (inv_pos.mpr hAp)]
      exact (mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hAp.le)).trans_eq
        (inv_mul_cancel₀ hAp.ne')
    obtain ⟨hfγ, hfγn⟩ := memLp_intermediate_of_unit_bounds hr hγ hγr hf1 hfr
      (hfn 1 h1n) (hfn _ hrn)
    have heq : (fun x => A * f x) = g := by
      funext x
      simp only [f, ← mul_assoc, mul_inv_cancel₀ hAp.ne', one_mul]
    have hγLp : MemLp g (ENNReal.ofReal γ) μ := heq ▸ hfγ.const_mul A
    refine ⟨hγLp, ?_⟩
    rw [← heq, toReal_eLpNorm_const_mul, abs_of_pos hAp]
    exact (mul_le_mul_of_nonneg_left hfγn hAp.le).trans_eq (mul_comm A 2)

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
