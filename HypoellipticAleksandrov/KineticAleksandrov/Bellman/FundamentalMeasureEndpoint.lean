module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureDerivativeMajorant
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureTimeScaling
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureRadon
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Order.LeftRight
import Mathlib.Tactic

/-! # Vanishing endpoints and the integrated Gaussian time equation away from the pole -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set Filter
open scoped Topology

/-- The scalar time chart vanishes at the initial endpoint away from the pole. -/
theorem bellmanGaussianTimeChart_tendsto_zero (q : BellmanPuncturedPlane) :
    Tendsto (fun s => bellmanGaussianTimeChart s q.val) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let a := q.val.1 ^ 2 + q.val.2 ^ 2
  let C := 360 * 8 ^ 6 * Real.sqrt 3 / (Real.pi * a ^ 6)
  have ha : 0 < a := bellmanPunctured_sq_pos q
  have hlim : Tendsto (fun s : ℝ => C * s ^ 4) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul ((tendsto_id.mono_left inf_le_left).pow 4) :
      Tendsto (fun s : ℝ => C * s ^ 4) (𝓝[>] 0) (𝓝 (C * 0 ^ 4)))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact (bellmanGaussianKernel_pos ⟨s, hs⟩ q.val).le
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with s hs h1
    exact bellmanGaussianKernel_le_smallTime_four ⟨s, hs⟩ h1.le q.val a ha le_rfl

/-- The scalar time chart vanishes at infinite time. -/
theorem bellmanGaussianTimeChart_tendsto_atTop (q : ℝ × ℝ) :
    Tendsto (fun s => bellmanGaussianTimeChart s q) atTop (𝓝 0) := by
  have hlim : Tendsto (fun s : ℝ => Real.sqrt 3 / (2 * Real.pi) * s ^ (-2 : ℝ))
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with s hs
    exact (bellmanGaussianKernel_pos ⟨s, hs⟩ q).le
  · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with s hs
    have hspos : 0 < s := hs
    calc
      bellmanGaussianTimeChart s q = bellmanGaussianKernel ⟨s, hspos⟩ q := rfl
      _ ≤ Real.sqrt 3 / (2 * Real.pi * s ^ 2) := bellmanGaussianKernel_le _ _
      _ = _ := by
        rw [Real.rpow_neg hspos.le, Real.rpow_two]
        ring

/-- At the pole-free initial endpoint, the time chart is right-continuous. -/
theorem bellmanGaussianTimeChart_continuousWithinAt_zero (q : BellmanPuncturedPlane) :
    ContinuousWithinAt (fun s => bellmanGaussianTimeChart s q.val) (Ici 0) 0 := by
  apply continuousWithinAt_Ioi_iff_Ici.mp
  simpa [ContinuousWithinAt, bellmanGaussianTimeChart] using
    bellmanGaussianTimeChart_tendsto_zero q

/-- The time derivative is integrable for each punctured-plane point. -/
theorem integrable_bellmanGaussianTimeDerivative (q : BellmanPuncturedPlane) :
    Integrable (fun t : BellmanPositiveTime =>
      bellmanGaussianTimeCoefficient t.val q.val * bellmanGaussianKernel t q.val)
      bellmanPositiveTimeVolume := by
  have hm : Measurable (fun t : BellmanPositiveTime =>
      bellmanGaussianTimeCoefficient t.val q.val * bellmanGaussianKernel t q.val) := by
    unfold bellmanGaussianTimeCoefficient bellmanGaussianKernel bellmanGaussianExponent
    fun_prop
  refine ((integrable_bellmanDerivativeMajorant (q.val.1 ^ 2 + q.val.2 ^ 2)).const_mul
    (bellmanGaussianTimeWeight q.val)).mono' hm.aestronglyMeasurable ?_
  exact ae_of_all _ fun t => bellmanGaussianTimeDerivative_le_majorant _
    (bellmanPunctured_sq_pos q) q.val le_rfl t

/-- The integrated time derivative of the Gaussian is zero away from its pole. -/
theorem integral_bellmanGaussianTimeDerivative_eq_zero (q : BellmanPuncturedPlane) :
    (∫ t : BellmanPositiveTime,
      bellmanGaussianTimeCoefficient t.val q.val * bellmanGaussianKernel t q.val
        ∂bellmanPositiveTimeVolume) = 0 := by
  let f' : ℝ → ℝ := fun s =>
    bellmanGaussianTimeCoefficient s q.val * bellmanGaussianTimeChart s q.val
  have he : MeasurableEmbedding (Subtype.val : BellmanPositiveTime → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Ioi
  have hi : IntegrableOn f' (Ioi 0) := by
    rw [IntegrableOn, ← map_bellmanPositiveTimeVolume_coe, he.integrable_map_iff]
    exact integrable_bellmanGaussianTimeDerivative q
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    (bellmanGaussianTimeChart_continuousWithinAt_zero q)
    (fun s hs => hasDerivAt_bellmanGaussianTimeChart ⟨s, hs⟩ q.val) hi
    (bellmanGaussianTimeChart_tendsto_atTop q.val)
  rw [← map_bellmanPositiveTimeVolume_coe, he.integral_map] at h
  simpa [f', bellmanGaussianTimeChart, bellmanGaussianKernel,
    bellmanGaussianExponent] using h

end HypoellipticAleksandrov.KineticAleksandrov
