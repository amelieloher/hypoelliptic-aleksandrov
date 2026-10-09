module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeGelfandSteklov
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Reverse-time Steklov energy identities

This module proves the fixed-positive-step Hilbert-value energy identities for
forward and backward reverse-time Steklov averages in the spatial Gelfand
triple.  It does not assert an energy identity for an unregularized curve.
-/

@[expose] public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private theorem normSq_sub_eq_inner_add_sub_inner
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (r s : H) :
    ‖r‖ ^ 2 - ‖s‖ ^ 2 = inner ℝ (r + s) r - inner ℝ (r + s) s := by
  rw [inner_add_left, inner_add_left, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq, real_inner_comm s r]
  ring

private theorem pivot_normSq_sub_eq_dualSub_apply_add
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (r s : H10HilbertGraph hΩ) :
    ‖valueCLM hΩ r‖ ^ 2 - ‖valueCLM hΩ s‖ ^ 2 =
      (scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ r) -
        scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ s)) (r + s) := by
  let vr : PDE.ScalarLp Ω (2 : ℝ≥0∞) := valueCLM hΩ r
  let vs : PDE.ScalarLp Ω (2 : ℝ≥0∞) := valueCLM hΩ s
  have hvalue : valueCLM hΩ (r + s) = vr + vs :=
    (valueCLM hΩ).map_add r s
  change ‖vr‖ ^ 2 - ‖vs‖ ^ 2 = _
  rw [ContinuousLinearMap.sub_apply,
    scalarLpToH10HilbertGraphDual_apply,
    scalarLpToH10HilbertGraphDual_apply, hvalue]
  exact normSq_sub_eq_inner_add_sub_inner vr vs

private theorem tendsto_clm_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {L : Filter ℝ} {f : ℝ → V →L[ℝ] ℝ} {g : ℝ → V}
    {a : V →L[ℝ] ℝ} {b : V}
    (hf : Filter.Tendsto f L (𝓝 a)) (hg : Filter.Tendsto g L (𝓝 b)) :
    Filter.Tendsto (fun t => f t (g t)) L (𝓝 (a b)) := by
  simpa only [Function.comp_def] using
    (isBoundedBilinearMap_apply.continuous.tendsto (a, b)).comp (hf.prodMk_nhds hg)

private theorem hasDerivAt_of_pivoted_curve
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {x : ℝ → V} {U : ℝ → V →L[ℝ] ℝ} {E : ℝ → ℝ}
    {y : ℝ → V →L[ℝ] ℝ} (hx : Continuous x) {t : ℝ}
    (hpivot : ∀ r s : ℝ, E r - E s = (U r - U s) (x r + x s))
    (hderiv : HasDerivAt U (y t) t) :
    HasDerivAt E (2 * y t (x t)) t := by
  have hSlopeU : Filter.Tendsto (slope U t) (𝓝[≠] t) (𝓝 (y t)) := by
    exact hderiv.tendsto_slope
  have hxWithin : Filter.Tendsto x (𝓝[≠] t) (𝓝 (x t)) :=
    (hx.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hsum : Filter.Tendsto (fun s => x s + x t) (𝓝[≠] t) (𝓝 (x t + x t)) :=
    hxWithin.add tendsto_const_nhds
  have hEval : Filter.Tendsto
      (fun s => slope U t s (x s + x t)) (𝓝[≠] t) (𝓝 (y t (x t + x t))) :=
    tendsto_clm_apply hSlopeU hsum
  have hSlopeEq : slope E t =ᶠ[𝓝[≠] t]
      fun s => slope U t s (x s + x t) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hst : s ≠ t := hs
    rw [slope_def_field, slope_def_module, hpivot s t,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply]
    rw [smul_eq_mul, ContinuousLinearMap.sub_apply]
    field_simp [sub_ne_zero.mpr hst]
  have hSlopeE : Filter.Tendsto (slope E t) (𝓝[≠] t) (𝓝 (2 * y t (x t))) := by
    have htwice : y t (x t + x t) = 2 * y t (x t) := by
      rw [ContinuousLinearMap.map_add]
      ring
    rw [← htwice]
    exact hEval.congr' hSlopeEq.symm
  exact hasDerivAt_iff_tendsto_slope.mpr hSlopeE

private theorem reverseTimeForwardSteklov_energy_identity_raw
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    {h a b : ℝ} (hh : 0 < h) (ha0 : 0 ≤ a) (hab : a ≤ b)
    (hbT : b + h ≤ T) :
    ‖valueCLM hΩ (reverseTimeForwardSteklov T h u b)‖ ^ 2 -
        ‖valueCLM hΩ (reverseTimeForwardSteklov T h u a)‖ ^ 2 =
      2 * (∫ t in Set.Icc a b,
        (reverseTimeForwardSteklov T h g t)
          (reverseTimeForwardSteklov T h u t)) := by
  let x : ℝ → H10HilbertGraph hΩ := fun t => reverseTimeForwardSteklov T h u t
  let y : ℝ → H10HilbertGraphDual hΩ := fun t => reverseTimeForwardSteklov T h g t
  let E : ℝ → ℝ := fun t => ‖valueCLM hΩ (x t)‖ ^ 2
  have hx : Continuous x := continuous_reverseTimeForwardSteklov T h hh u
  have hy : Continuous y := continuous_reverseTimeForwardSteklov T h hh g
  have hE : Continuous E := ((valueCLM hΩ).continuous.comp hx).norm.pow 2
  have hpair : Continuous (fun t => y t (x t)) := hy.clm_apply hx
  have hderivE : ∀ t ∈ Ioo a b, HasDerivAt E (2 * y t (x t)) t := by
    intro t ht
    apply hasDerivAt_of_pivoted_curve hx
      (fun r s => pivot_normSq_sub_eq_dualSub_apply_add hΩ (x r) (x s))
    exact hasDerivAt_reverseTimeForwardSteklov_gelfand hΩ T hT u g hderiv hh
      (by linarith [ha0, ht.1]) (by linarith [hbT, ht.2])
  have hFTC : (∫ t in a..b, 2 * y t (x t)) = E b - E a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hE.continuousOn hderivE
      ((continuous_const.mul hpair).intervalIntegrable a b)
  calc
    ‖valueCLM hΩ (reverseTimeForwardSteklov T h u b)‖ ^ 2 -
        ‖valueCLM hΩ (reverseTimeForwardSteklov T h u a)‖ ^ 2 = E b - E a := rfl
    _ = ∫ t in a..b, 2 * y t (x t) := hFTC.symm
    _ = 2 * (∫ t in Ioc a b, y t (x t)) := by
      rw [intervalIntegral.integral_of_le hab, integral_const_mul]
    _ = 2 * (∫ t in Icc a b, y t (x t)) := by
      rw [integral_Icc_eq_integral_Ioc]
    _ = 2 * (∫ t in Icc a b,
        (reverseTimeForwardSteklov T h g t) (reverseTimeForwardSteklov T h u t)) := rfl

private theorem reverseTimeBackwardSteklov_energy_identity_raw
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    {h a b : ℝ} (hh : 0 < h) (ha0 : 0 ≤ a - h) (hab : a ≤ b)
    (hbT : b ≤ T) :
    ‖valueCLM hΩ (reverseTimeBackwardSteklov T h u b)‖ ^ 2 -
        ‖valueCLM hΩ (reverseTimeBackwardSteklov T h u a)‖ ^ 2 =
      2 * (∫ t in Set.Icc a b,
        (reverseTimeBackwardSteklov T h g t)
          (reverseTimeBackwardSteklov T h u t)) := by
  let x : ℝ → H10HilbertGraph hΩ := fun t => reverseTimeBackwardSteklov T h u t
  let y : ℝ → H10HilbertGraphDual hΩ := fun t => reverseTimeBackwardSteklov T h g t
  let E : ℝ → ℝ := fun t => ‖valueCLM hΩ (x t)‖ ^ 2
  have hx : Continuous x := continuous_reverseTimeBackwardSteklov T h hh u
  have hy : Continuous y := continuous_reverseTimeBackwardSteklov T h hh g
  have hE : Continuous E := ((valueCLM hΩ).continuous.comp hx).norm.pow 2
  have hpair : Continuous (fun t => y t (x t)) := hy.clm_apply hx
  have hderivE : ∀ t ∈ Ioo a b, HasDerivAt E (2 * y t (x t)) t := by
    intro t ht
    apply hasDerivAt_of_pivoted_curve hx
      (fun r s => pivot_normSq_sub_eq_dualSub_apply_add hΩ (x r) (x s))
    exact hasDerivAt_reverseTimeBackwardSteklov_gelfand hΩ T hT u g hderiv hh
      (by linarith [ha0, ht.1]) (by linarith [hbT, ht.2])
  have hFTC : (∫ t in a..b, 2 * y t (x t)) = E b - E a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hE.continuousOn hderivE
      ((continuous_const.mul hpair).intervalIntegrable a b)
  calc
    ‖valueCLM hΩ (reverseTimeBackwardSteklov T h u b)‖ ^ 2 -
        ‖valueCLM hΩ (reverseTimeBackwardSteklov T h u a)‖ ^ 2 = E b - E a := rfl
    _ = ∫ t in a..b, 2 * y t (x t) := hFTC.symm
    _ = 2 * (∫ t in Ioc a b, y t (x t)) := by
      rw [intervalIntegral.integral_of_le hab, integral_const_mul]
    _ = 2 * (∫ t in Icc a b, y t (x t)) := by
      rw [integral_Icc_eq_integral_Ioc]
    _ = 2 * (∫ t in Icc a b,
        (reverseTimeBackwardSteklov T h g t) (reverseTimeBackwardSteklov T h u t)) := rfl

/-- Fixed-window forward Steklov energy identity in the reverse-time Gelfand triple. -/
theorem reverseTimeForwardSteklov_energy_identity
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    {h a b : ℝ} (hh : 0 < h) (ha0 : 0 ≤ a) (hab : a ≤ b)
    (hbT : b + h ≤ T) :
    ‖valueCLM hΩ (reverseTimeForwardSteklov T h u b)‖ ^ 2 -
        ‖valueCLM hΩ (reverseTimeForwardSteklov T h u a)‖ ^ 2 =
      2 * (∫ t in Set.Icc a b,
        (reverseTimeForwardSteklov T h g t)
          (reverseTimeForwardSteklov T h u t)) :=
  reverseTimeForwardSteklov_energy_identity_raw hΩ T hT u g hderiv hh ha0 hab hbT

/-- Fixed-window backward Steklov energy identity in the reverse-time Gelfand triple. -/
theorem reverseTimeBackwardSteklov_energy_identity
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    {h a b : ℝ} (hh : 0 < h) (ha0 : 0 ≤ a - h) (hab : a ≤ b)
    (hbT : b ≤ T) :
    ‖valueCLM hΩ (reverseTimeBackwardSteklov T h u b)‖ ^ 2 -
        ‖valueCLM hΩ (reverseTimeBackwardSteklov T h u a)‖ ^ 2 =
      2 * (∫ t in Set.Icc a b,
        (reverseTimeBackwardSteklov T h g t)
          (reverseTimeBackwardSteklov T h u t)) :=
  reverseTimeBackwardSteklov_energy_identity_raw hΩ T hT u g hderiv hh ha0 hab hbT

end HypoellipticAleksandrov.Parabolic.Dirichlet
