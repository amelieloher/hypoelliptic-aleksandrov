module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureTimeDerivative
import Mathlib.Tactic

/-! # A uniform integrable derivative majorant away from the Gaussian pole -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- Time decomposition of the Gaussian derivative bound, for a squared-distance lower bound a. -/
def bellmanDerivativeMajorant (a : ℝ) (t : ℝ) : ℝ :=
  (Ioc (0 : ℝ) 1).indicator
    (fun _ => 360 * 8 ^ 6 * Real.sqrt 3 / (Real.pi * a ^ 6)) t +
  (Ioi (1 : ℝ)).indicator (fun s => Real.sqrt 3 / (2 * Real.pi) * s ^ (-2 : ℝ)) t

/-- The derivative majorant is integrable on the positive half-line. -/
theorem integrable_bellmanDerivativeMajorant (a : ℝ) :
    Integrable (fun t : BellmanPositiveTime => bellmanDerivativeMajorant a t.val)
      bellmanPositiveTimeVolume := by
  have hsmall : IntegrableOn (fun _ : ℝ => 360 * 8 ^ 6 * Real.sqrt 3 / (Real.pi * a ^ 6))
      (Ioc (0 : ℝ) 1) := integrableOn_const measure_Ioc_lt_top.ne
  have hlarge : IntegrableOn (fun s : ℝ => Real.sqrt 3 / (2 * Real.pi) *
      s ^ (-2 : ℝ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
      (by norm_num : (0 : ℝ) < 1)).const_mul _
  have hi : Integrable (bellmanDerivativeMajorant a) (volume : Measure ℝ) :=
    (hsmall.integrable_indicator measurableSet_Ioc).add
      (hlarge.integrable_indicator measurableSet_Ioi)
  have hmap : Measure.map (Subtype.val : BellmanPositiveTime → ℝ)
      bellmanPositiveTimeVolume = volume.restrict (Ioi (0 : ℝ)) := by
    unfold bellmanPositiveTimeVolume
    convert! map_comap_subtype_coe (s := Ioi (0 : ℝ)) measurableSet_Ioi
      (volume.restrict (Ioi (0 : ℝ))) using 1
    rw [Measure.restrict_restrict measurableSet_Ioi, inter_self]
  have h : Integrable (bellmanDerivativeMajorant a)
      (Measure.map (Subtype.val : BellmanPositiveTime → ℝ) bellmanPositiveTimeVolume) := by
    rw [hmap]
    exact hi.restrict
  exact (MeasurableEmbedding.subtype_coe (s := Ioi (0 : ℝ))
    measurableSet_Ioi).integrable_map_iff.mp h

/-- The majorant is nonnegative at positive time. -/
theorem bellmanDerivativeMajorant_nonneg (a : ℝ) (t : BellmanPositiveTime) :
    0 ≤ bellmanDerivativeMajorant a t.val := by
  unfold bellmanDerivativeMajorant
  apply add_nonneg
  · exact indicator_nonneg (fun _ _ => by positivity) _
  · apply indicator_nonneg _ _
    intro s hs
    have hspos : 0 < s := lt_trans (by norm_num) hs
    positivity

/-- The actual Gaussian time derivative has an integrable separated bound. -/
theorem bellmanGaussianTimeDerivative_le_majorant (a : ℝ) (ha : 0 < a)
    (q : ℝ × ℝ) (hq : a ≤ q.1 ^ 2 + q.2 ^ 2) (t : BellmanPositiveTime) :
    ‖bellmanGaussianTimeCoefficient t.val q * bellmanGaussianKernel t q‖ ≤
      bellmanGaussianTimeWeight q * bellmanDerivativeMajorant a t.val := by
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (bellmanGaussianKernel_pos t q)]
  by_cases ht : t.val ≤ 1
  · simp only [bellmanDerivativeMajorant, indicator_of_mem
      (show t.val ∈ Ioc (0 : ℝ) 1 from ⟨t.property, ht⟩),
      indicator_of_notMem (show t.val ∉ Ioi (1 : ℝ) from not_lt.mpr ht), add_zero]
    have h := mul_le_mul (bellmanGaussianTimeCoefficient_small t ht q)
      (bellmanGaussianKernel_le_smallTime_four t ht q a ha hq)
      (bellmanGaussianKernel_pos t q).le
      (div_nonneg (bellmanGaussianTimeWeight_nonneg q) (by positivity))
    refine h.trans_eq ?_
    field_simp [ne_of_gt t.property]
  · have h1 : 1 < t.val := lt_of_not_ge ht
    simp only [bellmanDerivativeMajorant, indicator_of_notMem
      (show t.val ∉ Ioc (0 : ℝ) 1 from fun h => ht h.2),
      indicator_of_mem (show t.val ∈ Ioi (1 : ℝ) from h1), zero_add]
    have h := mul_le_mul (bellmanGaussianTimeCoefficient_large t h1.le q)
      (bellmanGaussianKernel_le t q) (bellmanGaussianKernel_pos t q).le
      (bellmanGaussianTimeWeight_nonneg q)
    refine h.trans_eq ?_
    rw [Real.rpow_neg t.property.le, Real.rpow_two]
    ring

end HypoellipticAleksandrov.KineticAleksandrov
