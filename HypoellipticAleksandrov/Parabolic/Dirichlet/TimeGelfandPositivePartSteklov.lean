module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10PositivePartContinuity
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeGelfandSteklov
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Positive-part reverse-time Steklov energy identities

This module proves the fixed-window energy identities for the positive part of
forward and backward reverse-time Steklov averages.  The chain rule is obtained
from the convex support inequalities for the squared `L²` norm of the positive
part; no derivative of the positive-part curve is asserted.
-/

@[expose] public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private theorem positivePart_mul_sub_le_half_sq_sub_sq (x z : ℝ) :
    max z 0 * (x - z) ≤ ((max x 0) ^ 2 - (max z 0) ^ 2) / 2 := by
  rcases le_total x 0 with hx | hx <;> rcases le_total z 0 with hz | hz <;>
    simp only [max_eq_left, max_eq_right, hx, hz] <;>
    nlinarith [sq_nonneg (x - z)]

private theorem half_sq_sub_sq_le_positivePart_mul_sub (x z : ℝ) :
    ((max x 0) ^ 2 - (max z 0) ^ 2) / 2 ≤ max x 0 * (x - z) := by
  rcases le_total x 0 with hx | hx <;> rcases le_total z 0 with hz | hz <;>
    simp only [max_eq_left, max_eq_right, hx, hz] <;>
    nlinarith [sq_nonneg (x - z)]

/-- Half the squared pivot norm of the positive part. -/
def positivePartHalfEnergy
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (v : H10HilbertGraph hΩ) : ℝ :=
  (1 / 2 : ℝ) * ‖valueCLM hΩ (h10PositivePart hΩ v)‖ ^ 2

private theorem scalarLp_norm_sq_eq_integral_sq
    {d : ℕ} {Ω : Set (PDE.Vec d)} (f : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ‖f‖ ^ 2 = ∫ a, (f a) ^ 2 ∂(PDE.volumeOn Ω) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  funext a
  simp only [RCLike.inner_apply, conj_trivial, pow_two]

private theorem scalarLp_integrable_sq
    {d : ℕ} {Ω : Set (PDE.Vec d)} (f : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    Integrable (fun a => (f a) ^ 2) (PDE.volumeOn Ω) := by
  exact (MeasureTheory.Lp.memLp f).integrable_sq

private theorem scalarLp_positivePart_support_lower
    {d : ℕ} {Ω : Set (PDE.Vec d)} (f z : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    inner ℝ (MeasureTheory.Lp.posPart z) (f - z) ≤
      (1 / 2 : ℝ) * ‖MeasureTheory.Lp.posPart f‖ ^ 2 -
        (1 / 2 : ℝ) * ‖MeasureTheory.Lp.posPart z‖ ^ 2 := by
  rw [scalarLp_norm_sq_eq_integral_sq (MeasureTheory.Lp.posPart f),
    scalarLp_norm_sq_eq_integral_sq (MeasureTheory.Lp.posPart z),
    L2.inner_def]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_sub
      ((scalarLp_integrable_sq (MeasureTheory.Lp.posPart f)).const_mul _)
      ((scalarLp_integrable_sq (MeasureTheory.Lp.posPart z)).const_mul _)]
  apply integral_mono_ae
    (L2.integrable_inner (MeasureTheory.Lp.posPart z) (f - z))
    (((scalarLp_integrable_sq (MeasureTheory.Lp.posPart f)).const_mul _).sub
      ((scalarLp_integrable_sq (MeasureTheory.Lp.posPart z)).const_mul _))
  filter_upwards [Lp.coeFn_posPart f, Lp.coeFn_posPart z,
    Lp.coeFn_sub f z] with a hfa hza hsub
  simp only [Pi.sub_apply, hfa, hza, hsub, RCLike.inner_apply, conj_trivial]
  nlinarith [positivePart_mul_sub_le_half_sq_sub_sq (f a) (z a)]

private theorem scalarLp_positivePart_support_upper
    {d : ℕ} {Ω : Set (PDE.Vec d)} (f z : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    (1 / 2 : ℝ) * ‖MeasureTheory.Lp.posPart f‖ ^ 2 -
        (1 / 2 : ℝ) * ‖MeasureTheory.Lp.posPart z‖ ^ 2 ≤
      inner ℝ (MeasureTheory.Lp.posPart f) (f - z) := by
  rw [scalarLp_norm_sq_eq_integral_sq (MeasureTheory.Lp.posPart f),
    scalarLp_norm_sq_eq_integral_sq (MeasureTheory.Lp.posPart z),
    L2.inner_def]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_sub
      ((scalarLp_integrable_sq (MeasureTheory.Lp.posPart f)).const_mul _)
      ((scalarLp_integrable_sq (MeasureTheory.Lp.posPart z)).const_mul _)]
  apply integral_mono_ae
    (((scalarLp_integrable_sq (MeasureTheory.Lp.posPart f)).const_mul _).sub
      ((scalarLp_integrable_sq (MeasureTheory.Lp.posPart z)).const_mul _))
    (L2.integrable_inner (MeasureTheory.Lp.posPart f) (f - z))
  filter_upwards [Lp.coeFn_posPart f, Lp.coeFn_posPart z,
    Lp.coeFn_sub f z] with a hfa hza hsub
  simp only [Pi.sub_apply, hfa, hza, hsub, RCLike.inner_apply, conj_trivial]
  nlinarith [half_sq_sub_sq_le_positivePart_mul_sub (f a) (z a)]

private theorem positivePart_support_lower
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (x z : H10HilbertGraph hΩ) :
    (scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ x) -
        scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ z))
        (h10PositivePart hΩ z) ≤
      positivePartHalfEnergy hΩ x - positivePartHalfEnergy hΩ z := by
  rw [ContinuousLinearMap.sub_apply, scalarLpToH10HilbertGraphDual_apply,
    scalarLpToH10HilbertGraphDual_apply, valueCLM_h10PositivePart]
  simp only [positivePartHalfEnergy, valueCLM_h10PositivePart]
  rw [← inner_sub_right]
  exact scalarLp_positivePart_support_lower (valueCLM hΩ x) (valueCLM hΩ z)

private theorem positivePart_support_upper
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (x z : H10HilbertGraph hΩ) :
    positivePartHalfEnergy hΩ x - positivePartHalfEnergy hΩ z ≤
      (scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ x) -
        scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ z))
        (h10PositivePart hΩ x) := by
  rw [ContinuousLinearMap.sub_apply, scalarLpToH10HilbertGraphDual_apply,
    scalarLpToH10HilbertGraphDual_apply, valueCLM_h10PositivePart]
  simp only [positivePartHalfEnergy, valueCLM_h10PositivePart]
  rw [← inner_sub_right]
  exact scalarLp_positivePart_support_upper (valueCLM hΩ x) (valueCLM hΩ z)

private theorem tendsto_clm_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {L : Filter ℝ} {f : ℝ → V →L[ℝ] ℝ} {g : ℝ → V}
    {a : V →L[ℝ] ℝ} {b : V}
    (hf : Tendsto f L (𝓝 a)) (hg : Tendsto g L (𝓝 b)) :
    Tendsto (fun t => f t (g t)) L (𝓝 (a b)) := by
  simpa only [Function.comp_def] using
    (isBoundedBilinearMap_apply.continuous.tendsto (a, b)).comp (hf.prodMk_nhds hg)

private theorem slope_energy_error_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (E : ℝ → ℝ) (U : ℝ → V →L[ℝ] ℝ) (p : ℝ → V) {s t : ℝ}
    (hst : s ≠ t)
    (h0 : 0 ≤ (E s - E t) - (U s - U t) (p t))
    (h1 : (E s - E t) - (U s - U t) (p t) ≤
      (U s - U t) (p s - p t)) :
    |slope E t s - slope U t s (p t)| ≤
      |slope U t s (p s - p t)| := by
  have habs : |(E s - E t) - (U s - U t) (p t)| ≤
      |(U s - U t) (p s - p t)| := by
    rw [abs_of_nonneg h0]
    exact h1.trans (le_abs_self _)
  have hleft : slope E t s - slope U t s (p t) =
      (s - t)⁻¹ * ((E s - E t) - (U s - U t) (p t)) := by
    rw [slope_def_field, slope_def_module, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    field_simp [sub_ne_zero.mpr hst]
  have hright : slope U t s (p s - p t) =
      (s - t)⁻¹ * (U s - U t) (p s - p t) := by
    rw [slope_def_module, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hleft, hright, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left habs (abs_nonneg _)

private theorem hasDerivAt_of_support_inequalities
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (U : ℝ → V →L[ℝ] ℝ) (p : ℝ → V) (E : ℝ → ℝ)
    (hp : Continuous p) (y : V →L[ℝ] ℝ) (t : ℝ)
    (hpivot : HasDerivAt U y t)
    (hlower : ∀ r s, (U r - U s) (p s) ≤ E r - E s)
    (hupper : ∀ r s, E r - E s ≤ (U r - U s) (p r)) :
    HasDerivAt E (y (p t)) t := by
  have hSlopeU : Tendsto (slope U t) (𝓝[≠] t) (𝓝 y) := hpivot.tendsto_slope
  have hpDiff : Tendsto (fun s => p s - p t) (𝓝[≠] t) (𝓝 0) := by
    simpa only [sub_self] using
      ((hp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).sub
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => p t) (𝓝[≠] t) (𝓝 (p t))))
  have hSmall : Tendsto (fun s => slope U t s (p s - p t))
      (𝓝[≠] t) (𝓝 0) := by
    simpa only [map_zero] using tendsto_clm_apply hSlopeU hpDiff
  have hCompare : ∀ᶠ s in 𝓝[≠] t,
      |slope E t s - slope U t s (p t)| ≤
        |slope U t s (p s - p t)| := by
    filter_upwards [self_mem_nhdsWithin] with s hst
    have hLower := hlower s t
    have hUpper := hupper s t
    have hraw0 : 0 ≤ (E s - E t) - (U s - U t) (p t) := by
      exact sub_nonneg.mpr hLower
    have hraw1 : (E s - E t) - (U s - U t) (p t) ≤
        (U s - U t) (p s - p t) := by
      have := sub_le_sub_right hUpper ((U s - U t) (p t))
      simpa only [ContinuousLinearMap.map_sub] using this
    exact slope_energy_error_le E U p hst hraw0 hraw1
  have hErr : Tendsto (fun s => slope E t s - slope U t s (p t))
      (𝓝[≠] t) (𝓝 0) := by
    rw [Metric.tendsto_nhds] at hSmall ⊢
    intro ε hε
    filter_upwards [hCompare, hSmall ε hε] with s hcomp hsmall
    rw [Real.dist_eq]
    simpa only [sub_zero] using lt_of_le_of_lt hcomp
      (by simpa only [Real.dist_eq, sub_zero] using hsmall)
  have hEval : Tendsto (fun s => slope U t s (p t)) (𝓝[≠] t) (𝓝 (y (p t))) :=
    tendsto_clm_apply hSlopeU tendsto_const_nhds
  apply hasDerivAt_iff_tendsto_slope.mpr
  simpa only [sub_add_cancel, zero_add] using hErr.add hEval

/-- Chain rule for the half squared `L²` norm of the positive part, derived
from the derivative of the pivoted curve and convex support inequalities. -/
theorem hasDerivAt_positivePartHalfEnergy_of_pivoted_curve
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (x : ℝ → H10HilbertGraph hΩ) (hx : Continuous x)
    (y : H10HilbertGraphDual hΩ) (t : ℝ)
    (hpivot : HasDerivAt
      (fun s => scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ (x s))) y t) :
    HasDerivAt (fun s => positivePartHalfEnergy hΩ (x s))
      (y (h10PositivePart hΩ (x t))) t := by
  exact hasDerivAt_of_support_inequalities
    (fun s => scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ (x s)))
    (fun s => h10PositivePart hΩ (x s))
    (fun s => positivePartHalfEnergy hΩ (x s))
    ((continuous_h10PositivePart hΩ).comp hx) y t hpivot
    (fun r s => positivePart_support_lower hΩ (x r) (x s))
    (fun r s => positivePart_support_upper hΩ (x r) (x s))

/-- Fixed-window forward Steklov positive-part energy identity in the
reverse-time Gelfand triple. -/
theorem reverseTimeForwardSteklov_positivePart_energy_identity
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    {h a b : ℝ} (hh : 0 < h) (ha0 : 0 ≤ a) (hab : a ≤ b)
    (hbT : b + h ≤ T) :
    ‖valueCLM hΩ (h10PositivePart hΩ (reverseTimeForwardSteklov T h u b))‖ ^ 2 -
        ‖valueCLM hΩ (h10PositivePart hΩ (reverseTimeForwardSteklov T h u a))‖ ^ 2 =
      2 * (∫ t in Set.Icc a b, (reverseTimeForwardSteklov T h g t)
        (h10PositivePart hΩ (reverseTimeForwardSteklov T h u t))) := by
  let x : ℝ → H10HilbertGraph hΩ := fun t => reverseTimeForwardSteklov T h u t
  let y : ℝ → H10HilbertGraphDual hΩ := fun t => reverseTimeForwardSteklov T h g t
  let E : ℝ → ℝ := fun t => positivePartHalfEnergy hΩ (x t)
  have hx : Continuous x := continuous_reverseTimeForwardSteklov T h hh u
  have hy : Continuous y := continuous_reverseTimeForwardSteklov T h hh g
  have hE : Continuous E := by
    exact continuous_const.mul ((continuous_norm.comp ((valueCLM hΩ).continuous.comp
      ((continuous_h10PositivePart hΩ).comp hx))).pow 2)
  have hpair : Continuous (fun t => y t (h10PositivePart hΩ (x t))) :=
    hy.clm_apply ((continuous_h10PositivePart hΩ).comp hx)
  have hderivE : ∀ t ∈ Ioo a b, HasDerivAt E
      (y t (h10PositivePart hΩ (x t))) t := by
    intro t ht
    exact hasDerivAt_positivePartHalfEnergy_of_pivoted_curve hΩ x hx (y t) t
      (hasDerivAt_reverseTimeForwardSteklov_gelfand hΩ T hT u g hderiv hh
        (by linarith [ha0, ht.1]) (by linarith [hbT, ht.2]))
  have hFTC : (∫ t in a..b, y t (h10PositivePart hΩ (x t))) = E b - E a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hE.continuousOn hderivE
      (hpair.intervalIntegrable a b)
  calc
    _ = 2 * (E b - E a) := by simp only [E, positivePartHalfEnergy]; ring
    _ = 2 * (∫ t in a..b, y t (h10PositivePart hΩ (x t))) := by rw [hFTC]
    _ = 2 * (∫ t in Ioc a b, y t (h10PositivePart hΩ (x t))) := by
      rw [intervalIntegral.integral_of_le hab]
    _ = 2 * (∫ t in Icc a b, y t (h10PositivePart hΩ (x t))) := by
      rw [integral_Icc_eq_integral_Ioc]
    _ = _ := rfl

/-- Fixed-window backward Steklov positive-part energy identity in the
reverse-time Gelfand triple. -/
theorem reverseTimeBackwardSteklov_positivePart_energy_identity
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    {h a b : ℝ} (hh : 0 < h) (ha0 : 0 ≤ a - h) (hab : a ≤ b)
    (hbT : b ≤ T) :
    ‖valueCLM hΩ (h10PositivePart hΩ (reverseTimeBackwardSteklov T h u b))‖ ^ 2 -
        ‖valueCLM hΩ (h10PositivePart hΩ (reverseTimeBackwardSteklov T h u a))‖ ^ 2 =
      2 * (∫ t in Set.Icc a b, (reverseTimeBackwardSteklov T h g t)
        (h10PositivePart hΩ (reverseTimeBackwardSteklov T h u t))) := by
  let x : ℝ → H10HilbertGraph hΩ := fun t => reverseTimeBackwardSteklov T h u t
  let y : ℝ → H10HilbertGraphDual hΩ := fun t => reverseTimeBackwardSteklov T h g t
  let E : ℝ → ℝ := fun t => positivePartHalfEnergy hΩ (x t)
  have hx : Continuous x := continuous_reverseTimeBackwardSteklov T h hh u
  have hy : Continuous y := continuous_reverseTimeBackwardSteklov T h hh g
  have hE : Continuous E := by
    exact continuous_const.mul ((continuous_norm.comp ((valueCLM hΩ).continuous.comp
      ((continuous_h10PositivePart hΩ).comp hx))).pow 2)
  have hpair : Continuous (fun t => y t (h10PositivePart hΩ (x t))) :=
    hy.clm_apply ((continuous_h10PositivePart hΩ).comp hx)
  have hderivE : ∀ t ∈ Ioo a b, HasDerivAt E
      (y t (h10PositivePart hΩ (x t))) t := by
    intro t ht
    exact hasDerivAt_positivePartHalfEnergy_of_pivoted_curve hΩ x hx (y t) t
      (hasDerivAt_reverseTimeBackwardSteklov_gelfand hΩ T hT u g hderiv hh
        (by linarith [ha0, ht.1]) (by linarith [hbT, ht.2]))
  have hFTC : (∫ t in a..b, y t (h10PositivePart hΩ (x t))) = E b - E a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hE.continuousOn hderivE
      (hpair.intervalIntegrable a b)
  calc
    _ = 2 * (E b - E a) := by simp only [E, positivePartHalfEnergy]; ring
    _ = 2 * (∫ t in a..b, y t (h10PositivePart hΩ (x t))) := by rw [hFTC]
    _ = 2 * (∫ t in Ioc a b, y t (h10PositivePart hΩ (x t))) := by
      rw [intervalIntegral.integral_of_le hab]
    _ = 2 * (∫ t in Icc a b, y t (h10PositivePart hΩ (x t))) := by
      rw [integral_Icc_eq_integral_Ioc]
    _ = _ := rfl

end HypoellipticAleksandrov.Parabolic.Dirichlet
