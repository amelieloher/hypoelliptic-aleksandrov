module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.BoundarySaturationGeometry
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Tactic

/-! # Continuity of cylinder intersection volume along continuous centers -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set MeasureTheory Filter
open scoped Topology

/-- A strict comparison of continuous real functions is locally constant away from equality. -/
theorem eventually_lt_iff_of_ne {f g : ℝ → ℝ} {r : ℝ}
    (hf : ContinuousAt f r) (hg : ContinuousAt g r) (hne : f r ≠ g r) :
    ∀ᶠ s in 𝓝 r, f s < g s ↔ f r < g r := by
  by_cases h : f r < g r
  · filter_upwards [hf.eventually_lt hg h] with s hs
    exact ⟨fun _ => h, fun _ => hs⟩
  · have hgt : g r < f r := lt_of_le_of_ne (le_of_not_gt h) hne.symm
    filter_upwards [hg.eventually_lt hf hgt] with s hs
    exact ⟨fun hlt => (not_lt_of_ge hs.le hlt).elim, fun hlt => (h hlt).elim⟩

/-- A null equality fiber is avoided almost everywhere. -/
theorem ae_ne_of_null_fiber {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → ℝ) (c : ℝ) (h : μ {x | f x = c} = 0) : ∀ᵐ x ∂μ, f x ≠ c := by
  simpa only [ae_iff, not_not] using h

/-- Cylinder membership is locally constant in radius away from the four null faces. -/
theorem ae_eventually_mem_cylinder_iff {d : ℕ} (P : ℝ → KineticPoint d)
    (hP : Continuous P) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ Y ∂volume, ∀ᶠ s in 𝓝 r,
      Y ∈ backwardCylinder (P s) s ↔ Y ∈ backwardCylinder (P r) r := by
  have hvface : volume {Y : KineticPoint d |
      PDE.vecNormSq (Y.velocity-(P r).velocity) = r^2} = 0 :=
    volume_velocity_sphere_face (P r).velocity hr
  have hpface : volume {Y : KineticPoint d |
      PDE.vecNormSq (relativePosition (P r) Y) = (r^3)^2} = 0 := by
    simpa only [PDE.euclideanSphere, PDE.euclideanSqDist, mem_ofPred_eq, sub_zero] using
      volume_position_sphere_face (P r) (pow_pos hr 3)
  filter_upwards [ae_ne_of_null_fiber (fun Y : KineticPoint d => Y.time)
      ((P r).time-r^2) (volume_time_face _),
    ae_ne_of_null_fiber (fun Y : KineticPoint d => Y.time) (P r).time (volume_time_face _),
    ae_ne_of_null_fiber _ _ hvface, ae_ne_of_null_fiber _ _ hpface] with Y ht₁ ht₂ hv hp
  have ht : Continuous (fun s => (P s).time) := continuous_time.comp hP
  have hx : Continuous (fun s => (P s).position) := continuous_position.comp hP
  have hvp : Continuous (fun s => (P s).velocity) := continuous_velocity.comp hP
  have hrel : Continuous (fun s => relativePosition (P s) Y) :=
    (continuous_const.sub hx).sub ((continuous_const.sub ht).smul hvp)
  have e₁ := eventually_lt_iff_of_ne (ht.sub (continuous_id.pow 2)).continuousAt
    continuous_const.continuousAt ht₁.symm
  have e₂ := eventually_lt_iff_of_ne continuous_const.continuousAt ht.continuousAt ht₂
  have e₃ := eventually_lt_iff_of_ne
    (PDE.continuous_vecNormSq.comp (continuous_const.sub hvp)).continuousAt
    (continuous_id.pow 2).continuousAt hv
  have e₄ := eventually_lt_iff_of_ne (PDE.continuous_vecNormSq.comp hrel).continuousAt
    ((continuous_id.pow 3).pow 2).continuousAt hp
  filter_upwards [e₁, e₂, e₃, e₄] with s h₁ h₂ h₃ h₄
  simpa only [backwardCylinder, PDE.euclideanBall, PDE.euclideanSqDist, mem_ofPred_eq,
    sub_zero, Pi.sub_apply, Pi.pow_apply, Function.comp_apply, id_eq] using
      and_congr h₁ (and_congr h₂ (and_congr h₃ h₄))

/-- Intersection volume with any finite-volume set is continuous along continuous centers. -/
theorem continuousAt_cylinder_inter_volume {d : ℕ} (P : ℝ → KineticPoint d)
    (hP : Continuous P) {E : Set (KineticPoint d)} (hE : volume E ≠ ⊤)
    {r : ℝ} (hr : 0 < r) :
    ContinuousAt (fun s => (volume (E ∩ backwardCylinder (P s) s)).toReal) r := by
  change Tendsto _ (𝓝 r) (𝓝 _)
  let : IsFiniteMeasure (volume.restrict E) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hE.lt_top⟩
  have hlim := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure (𝓝 r)
    (μ := volume.restrict E) (isOpen_cylinder (P r) r).measurableSet
    (fun s => (isOpen_cylinder (P s) s).measurableSet)
    (ae_restrict_of_ae (ae_eventually_mem_cylinder_iff P hP hr))
  have hreal := (ENNReal.continuousAt_toReal (measure_ne_top
    (volume.restrict E) (backwardCylinder (P r) r))).tendsto.comp hlim
  simpa only [Measure.restrict_apply (isOpen_cylinder _ _).measurableSet, inter_comm,
    Function.comp_def]
    using hreal

/-- The saturation centers depend continuously on the radius. -/
theorem continuous_saturationCenter {d : ℕ} (X : KineticPoint d) :
    Continuous (saturationCenter X) := by
  apply KineticPoint.continuous_mk <;> fun_prop

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
