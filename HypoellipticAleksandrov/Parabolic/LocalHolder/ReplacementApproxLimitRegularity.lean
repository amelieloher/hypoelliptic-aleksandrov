module

public import HypoellipticAleksandrov.Parabolic.FiniteOrderSobolevC12Representative
public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxWeakLimit
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.LocalizedKrylovRegularity

/-! # Classical regularity of a continuous higher-weak-derivative limit

The finite Sobolev representatives agree pointwise with the continuous limit on their
open collars. Scalar classical regularity then follows by locality.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter Set MeasureTheory
open scoped Topology

/-- Scalar anisotropic classical regularity is local on its carrier. -/
theorem scalarC12On_of_locally_scalarC12On {d : ℕ}
    {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    (hlocal : ∀ z ∈ U, ∃ V, IsOpen V ∧ z ∈ V ∧ IsScalarC12On u V) :
    IsScalarC12On u U := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply continuousOn_of_locally_continuousOn
    intro z hz
    obtain ⟨V, hV, hzV, huV⟩ := hlocal z hz
    exact ⟨V, hV, hzV, huV.continuousOn.mono inter_subset_right⟩
  · intro z hz
    obtain ⟨V, _, hzV, huV⟩ := hlocal z hz
    exact huV.timeSlice_differentiableAt hzV
  · intro z hz
    obtain ⟨V, _, hzV, huV⟩ := hlocal z hz
    exact huV.spatialSlice_contDiffAt hzV
  · apply continuousOn_of_locally_continuousOn
    intro z hz
    obtain ⟨V, hV, hzV, huV⟩ := hlocal z hz
    exact ⟨V, hV, hzV, huV.continuousOn_scalarTimeDerivative.mono inter_subset_right⟩
  · apply continuousOn_of_locally_continuousOn
    intro z hz
    obtain ⟨V, hV, hzV, huV⟩ := hlocal z hz
    exact ⟨V, hV, hzV, huV.continuousOn_scalarSpatialGradient.mono inter_subset_right⟩
  · apply continuousOn_of_locally_continuousOn
    intro z hz
    obtain ⟨V, hV, hzV, huV⟩ := hlocal z hz
    exact ⟨V, hV, hzV, huV.continuousOn_scalarSpatialHessian.mono inter_subset_right⟩

/-- A continuous function carrying the actual higher weak family is classical on its carrier. -/
theorem scalarC12On_of_continuousOn_higher_weak_family {d : ℕ}
    {U : Set (TimeVelocity d)} (hU : IsOpen U)
    {u : TimeVelocity d → ℝ} (hu : ContinuousOn u U)
    (D : ParabolicWeakDerivativeFamily d (2 * (d + 4)) U u) :
    IsScalarC12On u U := by
  apply scalarC12On_of_locally_scalarC12On
  intro z hz
  obtain ⟨rho, hrho, v, hsub, hv, hv12, hvae, hjet⟩ :=
    exists_finiteOrderSobolevC12Representative hU (isCompact_singleton (x := z))
      (singleton_subset_iff.mpr hz) D
  let V := Metric.thickening rho ({z} : Set (TimeVelocity d))
  have hV : IsOpen V := Metric.isOpen_thickening
  have heq : EqOn v u V := Measure.eqOn_open_of_ae_eq hvae hV
    hv.continuous.continuousOn (hu.mono hsub)
  refine ⟨V, hV, ?_, ?_⟩
  · exact Metric.self_subset_thickening hrho _ (mem_singleton z)
  · exact KineticAleksandrov.Occupation.isScalarC12On_congr_open hV hv12 heq.symm

/-- Uniform actual higher families make a continuous strong-L2 root limit classical. -/
theorem scalarC12On_of_strongL2_limit_higher_families {d : ℕ}
    (U : Set (TimeVelocity d)) (hU : IsOpen U)
    (u : ℕ → TimeVelocity d → ℝ)
    (D : ∀ n, ParabolicWeakDerivativeFamily d (2 * (d + 4)) U (u n))
    (hu : ∀ n, ParabolicMemLpOn U 2 (u n))
    (v : TimeVelocity d → ℝ) (hv : ParabolicMemLpOn U 2 v)
    (hvcont : ContinuousOn v U)
    (hstrong : Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 (hv.toLp v)))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n, (D n).squaredL2Norm ≤ C ^ 2) :
    IsScalarC12On v U := by
  obtain ⟨E⟩ := exists_weakDerivativeFamily_of_tendsto_toLp
    U u D hu v hv hstrong C hC hb
  exact scalarC12On_of_continuousOn_higher_weak_family hU hvcont E

end HypoellipticAleksandrov.Parabolic.LocalHolder
