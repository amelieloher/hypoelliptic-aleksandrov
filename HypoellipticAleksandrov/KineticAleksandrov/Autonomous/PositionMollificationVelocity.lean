module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionMollificationBasic
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! # Actual velocity derivatives of the position-regularized barrier -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter BarrierRegularization
open scoped Topology

/-- A dominated source velocity jet passes through the position integral.
The derivative and majorant hypotheses here are discharged by the homogeneous source jets. -/
theorem position_convolution_velocity_hasDerivAt
    (eta : ℝ → ℝ) (heta : IsNonnegativeUnitSmoothMollifier eta)
    (f g : (ℝ × ℝ) → ℝ) (X : ℝ) (v : ℝ)
    (hf : LocallyIntegrable (fun Y => f (Y, v)) volume)
    (hg : Measurable g) (p C : ℝ) (hp : -1 < p)
    (hb : ∀ Y : ℝ, Y ≠ 0 → ∀ w : ℝ, |g (Y, w)| ≤ C * |Y| ^ p)
    (hd : ∀ Y : ℝ, Y ≠ 0 → ∀ w : ℝ,
      HasDerivAt (fun u => f (Y, u)) (g (Y, w)) w)
    (hfm : ∀ w : ℝ, Measurable (fun Y => f (Y, w))) :
    HasDerivAt (fun w => positionConvolution eta f (X, w))
      (positionConvolution eta g (X, v)) v := by
  have hbound := (position_kernel_integrable eta (fun Y => |Y| ^ p)
    heta.1.continuous heta.2.1 (bellman_abs_rpow_locallyIntegrable p hp) X).const_mul C
  unfold positionConvolution
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w Y => eta (X - Y) * f (Y, w))
    (F' := fun w Y => eta (X - Y) * g (Y, w))
    (s := univ) (bound := fun Y => C * (eta (X - Y) * |Y| ^ p)) (μ := volume)
    (by simp) ?_ (position_kernel_integrable eta _ heta.1.continuous heta.2.1 hf X)
    ?_ ?_ hbound ?_).2
  · exact Eventually.of_forall (fun w =>
      ((heta.1.continuous.measurable.comp (measurable_const.sub measurable_id)).mul
        (hfm w)).aestronglyMeasurable)
  · exact ((heta.1.continuous.measurable.comp (measurable_const.sub measurable_id)).mul
      (hg.comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable
  · filter_upwards [volume.ae_ne (0 : ℝ)] with Y hY w _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heta.2.2.1 (X - Y))]
    exact (mul_le_mul_of_nonneg_left (hb Y hY w) (heta.2.2.1 (X - Y))).trans_eq
      (by ring)
  · filter_upwards [volume.ae_ne (0 : ℝ)] with Y hY w _
    exact (hd Y hY w).const_mul (eta (X - Y))

/-- A uniformly dominated source velocity fiber has a continuous position integral. -/
theorem position_convolution_velocity_continuous
    (eta : ℝ → ℝ) (heta : IsNonnegativeUnitSmoothMollifier eta)
    (g : (ℝ × ℝ) → ℝ) (X : ℝ) (hg : Measurable g)
    (p C : ℝ) (hp : -1 < p)
    (hb : ∀ Y : ℝ, Y ≠ 0 → ∀ w : ℝ, |g (Y, w)| ≤ C * |Y| ^ p)
    (hc : ∀ Y : ℝ, Y ≠ 0 → Continuous (fun w => g (Y, w))) :
    Continuous (fun w => positionConvolution eta g (X, w)) := by
  have hbound := (position_kernel_integrable eta (fun Y => |Y| ^ p)
    heta.1.continuous heta.2.1 (bellman_abs_rpow_locallyIntegrable p hp) X).const_mul C
  apply continuous_iff_continuousAt.mpr
  intro v
  unfold positionConvolution
  apply continuousAt_of_dominated (bound := fun Y => C * (eta (X - Y) * |Y| ^ p))
  · exact Eventually.of_forall (fun w =>
      ((heta.1.continuous.measurable.comp (measurable_const.sub measurable_id)).mul
        (hg.comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable)
  · exact Eventually.of_forall (fun w => by
      filter_upwards [volume.ae_ne (0 : ℝ)] with Y hY
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heta.2.2.1 (X - Y))]
      exact (mul_le_mul_of_nonneg_left (hb Y hY w) (heta.2.2.1 (X - Y))).trans_eq
        (by ring))
  · exact hbound
  · filter_upwards [volume.ae_ne (0 : ℝ)] with Y hY
    exact (continuous_const.mul (hc Y hY)).continuousAt

/-- Both actual velocity derivatives commute with position convolution, including at v=0. -/
theorem barrier_position_convolution_velocity_jets {alpha : ℝ} {Phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha Phi) (ha : 0 < alpha) (ha1 : alpha < 1)
    (eta : ℝ → ℝ) (heta : IsNonnegativeUnitSmoothMollifier eta) (X v : ℝ) :
    HasDerivAt (fun w => positionConvolution eta (bellmanOriginExtension Phi) (X, w))
      (positionConvolution eta (bellmanDv Phi) (X, v)) v ∧
    HasDerivAt (fun w => positionConvolution eta (bellmanDv Phi) (X, w))
      (positionConvolution eta (bellmanDvv Phi) (X, v)) v := by
  obtain ⟨_, _, ⟨Cv, hCv, hbv⟩, ⟨Cvv, hCvv, hbvv⟩⟩ := h.origin_jet_bounds
  have hmv := measurable_of_continuousOn_compl_singleton (0, 0)
    (h.directional_contDiffOn (0, 1)).continuousOn
  have hmvv := measurable_of_continuousOn_compl_singleton (0, 0) h.dvv_continuousOn
  constructor
  · apply position_convolution_velocity_hasDerivAt eta heta _ _ X v
      ((h.origin_extension_continuous ha).comp
        (continuous_id.prodMk continuous_const)).locallyIntegrable
      hmv ((alpha - 1) / 3) Cv (by linarith)
      (fun Y hY w => barrier_position_fiber_bound (alpha - 1) (by linarith)
        _ Cv hCv hbv Y w hY)
    · intro Y hY w
      have hq : (Y, w) ∈ bellmanPuncturedSet := fun he => hY (congrArg Prod.fst he)
      have hd := (h.1.contDiffAt (bellmanPuncturedSet_isOpen.mem_nhds hq)).differentiableAt
        (by norm_num)
      exact (bellman_hasDerivAt_second hd).congr_of_eventuallyEq
        ((barrierExtension_eventuallyEq Phi hq).comp_tendsto
          ((continuous_const.prodMk continuous_id).tendsto w))
    · intro w
      exact (h.origin_extension_continuous ha).measurable.comp
        (measurable_id.prodMk measurable_const)
  · apply position_convolution_velocity_hasDerivAt eta heta _ _ X v
      (barrier_velocity_fibers_locallyIntegrable h ha ha1 v).1
      hmvv ((alpha - 2) / 3) Cvv (by linarith)
      (fun Y hY w => barrier_position_fiber_bound (alpha - 2) (by linarith)
        _ Cvv hCvv hbvv Y w hY)
    · intro Y hY w
      have hq : (Y, w) ∈ bellmanPuncturedSet := fun he => hY (congrArg Prod.fst he)
      have hd := ((h.directional_contDiffOn (0, 1)).contDiffAt
        (bellmanPuncturedSet_isOpen.mem_nhds hq)).differentiableAt (by norm_num)
      exact bellman_hasDerivAt_second hd
    · intro w
      exact hmv.comp (measurable_id.prodMk measurable_const)

/-- The position-regularized barrier is C² in velocity at every position. -/
theorem barrier_position_convolution_velocity_c2 {alpha : ℝ} {Phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha Phi) (ha : 0 < alpha) (ha1 : alpha < 1)
    (eta : ℝ → ℝ) (heta : IsNonnegativeUnitSmoothMollifier eta) (X : ℝ) :
    ContDiff ℝ 2 (fun v => positionConvolution eta (bellmanOriginExtension Phi) (X, v)) := by
  have hj := barrier_position_convolution_velocity_jets h ha ha1 eta heta X
  have he : deriv (fun v => positionConvolution eta (bellmanOriginExtension Phi) (X, v)) =
      (fun v => positionConvolution eta (bellmanDv Phi) (X, v)) := funext fun v => (hj v).1.deriv
  have he2 : deriv (fun v => positionConvolution eta (bellmanDv Phi) (X, v)) =
      (fun v => positionConvolution eta (bellmanDvv Phi) (X, v)) := funext fun v => (hj v).2.deriv
  obtain ⟨_, _, _, ⟨C, hC, hb⟩⟩ := h.origin_jet_bounds
  have hc : Continuous (fun v => positionConvolution eta (bellmanDvv Phi) (X, v)) := by
    apply position_convolution_velocity_continuous eta heta _ X
      (measurable_of_continuousOn_compl_singleton (0, 0) h.dvv_continuousOn)
      ((alpha - 2) / 3) C (by linarith)
      (fun Y hY w => barrier_position_fiber_bound (alpha - 2) (by linarith) _ C hC hb Y w hY)
    intro Y hY
    exact h.dvv_continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun w he => hY (congrArg Prod.fst he))
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun v => (hj v).1.differentiableAt, (by norm_num), ?_⟩
  rw [he, contDiff_one_iff_deriv, he2]
  exact ⟨fun v => (hj v).2.differentiableAt, hc⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
