module

public import PDEFoundation.Measure.LpPower
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Truncated dual powers for occupation densities

Measure-generic bounded tests and their exact conjugate norms. Adapted from the
`PDEFoundation.Measure.SignedTruncatedDualPower` infrastructure; no additional duality
theorem is assumed.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The absolute value of `g`, truncated to the set where it is at most
`n + 1`. -/
def truncatedAbs (g : α → ℝ) (n : ℕ) (x : α) : ℝ :=
  {x | |g x| ≤ n + 1}.indicator (fun x => |g x|) x

/-- The signed conjugate power of the bounded absolute-value truncation. -/
def signedTruncatedDualPower (g : α → ℝ) (r : ℝ) (n : ℕ) (x : α) : ℝ :=
  if 0 ≤ g x then (truncatedAbs g n x) ^ (r - 1)
  else -(truncatedAbs g n x) ^ (r - 1)

/-- The absolute-value truncation is measurable. -/
theorem measurable_truncatedAbs {g : α → ℝ} (hg : Measurable g) (n : ℕ) :
    Measurable (truncatedAbs g n) := by
  exact hg.norm.indicator (measurableSet_le hg.norm measurable_const)

omit [MeasurableSpace α] in
/-- The absolute-value truncation is nonnegative. -/
theorem truncatedAbs_nonneg (g : α → ℝ) (n : ℕ) (x : α) :
    0 ≤ truncatedAbs g n x := by
  by_cases hx : x ∈ {x | |g x| ≤ n + 1}
  · rw [truncatedAbs, indicator_of_mem hx]
    exact abs_nonneg _
  · rw [truncatedAbs, indicator_of_notMem hx]

omit [MeasurableSpace α] in
/-- The truncation is bounded by its cutoff. -/
theorem abs_truncatedAbs_le (g : α → ℝ) (n : ℕ) (x : α) :
    |truncatedAbs g n x| ≤ n + 1 := by
  by_cases hx : x ∈ {x | |g x| ≤ n + 1}
  · rw [truncatedAbs, indicator_of_mem hx, abs_abs]
    exact hx
  · rw [truncatedAbs, indicator_of_notMem hx, abs_zero]
    positivity

/-- Bounded truncations belong to every Lp space over a finite measure. -/
theorem memLp_truncatedAbs [IsFiniteMeasure μ] {g : α → ℝ}
    (hg : Measurable g) (n : ℕ) (p : ENNReal) :
    MemLp (truncatedAbs g n) p μ := by
  apply MemLp.of_bound (measurable_truncatedAbs hg n).aestronglyMeasurable (n + 1)
  exact ae_of_all _ fun x => by
    simpa only [Real.norm_eq_abs] using abs_truncatedAbs_le g n x

/-- The signed truncated dual power is measurable and globally bounded. -/
theorem signedTruncatedDualPower_measurable_bounded
    {g : α → ℝ} (hg : Measurable g) {r : ℝ} (hr : 1 < r) (n : ℕ) :
    Measurable (signedTruncatedDualPower g r n) ∧
      ∀ x, |signedTruncatedDualPower g r n x| ≤
        (n + 1 : ℝ) ^ (r - 1) := by
  have hpow : Measurable (fun x => (truncatedAbs g n x) ^ (r - 1)) :=
    (Real.continuous_rpow_const (sub_nonneg.mpr hr.le)).measurable.comp
      (measurable_truncatedAbs hg n)
  refine ⟨Measurable.ite (measurableSet_le measurable_const hg) hpow hpow.neg,
    fun x => ?_⟩
  rw [signedTruncatedDualPower]
  by_cases hx : 0 ≤ g x
  · rw [ite_eq_left hx, abs_of_nonneg (Real.rpow_nonneg (truncatedAbs_nonneg g n x) _)]
    have hbound := abs_truncatedAbs_le g n x
    rw [abs_of_nonneg (truncatedAbs_nonneg g n x)] at hbound
    exact Real.rpow_le_rpow (truncatedAbs_nonneg g n x)
      hbound
      (sub_nonneg.mpr hr.le)
  · rw [ite_eq_right hx, abs_neg,
      abs_of_nonneg (Real.rpow_nonneg (truncatedAbs_nonneg g n x) _)]
    have hbound := abs_truncatedAbs_le g n x
    rw [abs_of_nonneg (truncatedAbs_nonneg g n x)] at hbound
    exact Real.rpow_le_rpow (truncatedAbs_nonneg g n x)
      hbound (sub_nonneg.mpr hr.le)

/-- The signed test has the same conjugate norm as the unsigned dual power. -/
theorem eLpNorm_signedTruncatedDualPower
    {g : α → ℝ} (hg : Measurable g) {r : ℝ} (hr : 1 < r) (n : ℕ) :
    eLpNorm (signedTruncatedDualPower g r n)
        (ENNReal.ofReal (r / (r - 1))) μ =
      eLpNorm (truncatedAbs g n) (ENNReal.ofReal r) μ ^ (r - 1) := by
  have hTrunc := measurable_truncatedAbs hg n
  rw [eLpNorm_congr_norm_ae
    (signedTruncatedDualPower_measurable_bounded hg hr n).1.aestronglyMeasurable
    ((hTrunc.pow_const (r - 1)).aestronglyMeasurable)
    (ae_of_all _ fun x => by
      show ‖signedTruncatedDualPower g r n x‖ =
        ‖(truncatedAbs g n x) ^ (r - 1)‖
      rw [signedTruncatedDualPower]
      split_ifs <;> simp)]
  have hrSub : 0 < r - 1 := sub_pos.mpr hr
  have hexp : ENNReal.ofReal (r / (r - 1)) * ENNReal.ofReal (r - 1) =
      ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_mul (div_nonneg (zero_le_one.trans hr.le) hrSub.le)]
    congr 1
    field_simp
  have hfun : (fun x => truncatedAbs g n x ^ (r - 1)) =
      fun x => ‖truncatedAbs g n x‖ ^ (r - 1) := by
    funext x
    rw [Real.norm_of_nonneg (truncatedAbs_nonneg g n x)]
  rw [hfun, eLpNorm_norm_rpow _ hTrunc.aestronglyMeasurable hrSub, hexp]

omit [MeasurableSpace α] in
private theorem signedTruncatedDualPower_mul
    (g : α → ℝ) {r : ℝ} (hr : 1 < r) (n : ℕ) (x : α) :
    signedTruncatedDualPower g r n x * g x =
      truncatedAbs g n x ^ r := by
  by_cases hxmem : x ∈ {x | |g x| ≤ n + 1}
  · rw [truncatedAbs, indicator_of_mem hxmem]
    by_cases hxzero : |g x| = 0
    · have hgzero : g x = 0 := abs_eq_zero.mp hxzero
      rw [signedTruncatedDualPower, truncatedAbs, indicator_of_mem hxmem, hgzero,
        abs_zero, Real.zero_rpow (sub_ne_zero.mpr (ne_of_gt hr)),
        Real.zero_rpow (ne_of_gt (zero_lt_one.trans hr))]
      simp
    · have habsPos : 0 < |g x| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hxzero)
      by_cases hx : 0 ≤ g x
      · rw [signedTruncatedDualPower, ite_eq_left hx, truncatedAbs,
          indicator_of_mem hxmem, abs_of_nonneg hx]
        calc
          g x ^ (r - 1) * g x = g x ^ (r - 1) * g x ^ (1 : ℝ) := by
            rw [Real.rpow_one]
          _ = g x ^ ((r - 1) + 1) := (Real.rpow_add (by simpa [abs_of_nonneg hx]
            using habsPos) _ _).symm
          _ = g x ^ r := by
            congr 1
            ring
      · have hxneg : g x < 0 := lt_of_not_ge hx
        rw [signedTruncatedDualPower, ite_eq_right hx, truncatedAbs,
          indicator_of_mem hxmem, abs_of_neg hxneg]
        calc
          -(-g x) ^ (r - 1) * g x = (-g x) ^ (r - 1) * (-g x) := by ring
          _ =
              (-g x) ^ (r - 1) * (-g x) ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = (-g x) ^ ((r - 1) + 1) :=
            (Real.rpow_add (by linarith) _ _).symm
          _ = (-g x) ^ r := by
            congr 1
            ring
  · rw [signedTruncatedDualPower, truncatedAbs, indicator_of_notMem hxmem]
    rw [Real.zero_rpow (sub_ne_zero.mpr (ne_of_gt hr)),
      Real.zero_rpow (ne_of_gt (zero_lt_one.trans hr))]
    simp

/-- Pairing the signed test with `g` gives exactly the `r`th moment, hence the
`r`th power of the real `Lʳ` norm of the truncation. -/
theorem integral_signedTruncatedDualPower_mul
    [IsFiniteMeasure μ] {g : α → ℝ} (hg : Measurable g)
    {r : ℝ} (hr : 1 < r) (n : ℕ) :
    ∫ x, signedTruncatedDualPower g r n x * g x ∂μ =
      (eLpNorm (truncatedAbs g n) (ENNReal.ofReal r) μ).toReal ^ r := by
  rw [PDE.toReal_eLpNorm_ofReal_rpow_eq_integral_rpow_norm
    (zero_lt_one.trans hr) (memLp_truncatedAbs hg n _)]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    change signedTruncatedDualPower g r n x * g x = ‖truncatedAbs g n x‖ ^ r
    rw [signedTruncatedDualPower_mul g hr n x, Real.norm_eq_abs,
      abs_of_nonneg (truncatedAbs_nonneg g n x)]

end

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
