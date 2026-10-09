module

public import HypoellipticAleksandrov.Parabolic.ScalarDirichletData
public import PDEFoundation.Measure.RestrictedVolume
import HypoellipticAleksandrov.Parabolic.WeakDerivatives
import Mathlib.Topology.Order.Lattice
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! # Continuous promotion of almost-everywhere source bounds

The product almost-everywhere inequality is first tested on a measurable zero extension.
Continuity then gives the inequality at every interior point.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set

/-- A continuous envelope bounding almost every slice bounds every interior point. -/
theorem abs_le_of_continuousOn_of_ae_slices {d : ℕ}
    {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (a T : ℝ) (w b : TimeVelocity d → ℝ)
    (hbc : Continuous b)
    (hw : ContinuousOn w (scalarParabolicOpenCylinder a T Ω))
    (hb : ∀ᵐ t ∂volume.restrict (Ioo a T),
      ∀ᵐ y ∂PDE.volumeOn Ω, |w (t, y)| ≤ b (t, y)) :
    ∀ z ∈ scalarParabolicOpenCylinder a T Ω, |w z| ≤ b z := by
  classical
  let U := scalarParabolicOpenCylinder a T Ω
  have hU : MeasurableSet U := (isOpen_Ioo.prod hΩ).measurableSet
  let w₀ := U.piecewise w (fun _ => 0)
  have hw₀ : Measurable w₀ := hw.measurable_piecewise continuousOn_const hU
  have hbound : ∀ᵐ t ∂volume.restrict (Ioo a T),
      ∀ᵐ y ∂PDE.volumeOn Ω, |w₀ (t, y)| ≤ b (t, y) := by
    filter_upwards [hb, ae_restrict_mem measurableSet_Ioo] with t ht hti
    filter_upwards [ht, ae_restrict_mem hΩ.measurableSet] with y hy hyo
    change |U.piecewise w (fun _ => 0) (t, y)| ≤ _
    rw [piecewise_eq_of_mem U w (fun _ => 0) (show (t, y) ∈ U from ⟨hti, hyo⟩)]
    exact hy
  have hprod : (volume.restrict (Ioo a T)).prod (PDE.volumeOn Ω) =
      timeVelocityVolumeOn (Ioo a T ×ˢ Ω) := by
    rw [timeVelocityVolumeOn, volume_timeVelocity_eq_prod]
    exact Measure.prod_restrict (Ioo a T) Ω
  have hm : MeasurableSet {z : TimeVelocity d | |w₀ z| ≤ b z} :=
    measurableSet_le (continuous_abs.measurable.comp hw₀)
      hbc.measurable
  have hae := (Measure.ae_prod_iff_ae_ae hm).2 hbound
  rw [hprod] at hae
  have heq : (fun z : TimeVelocity d => min (|w z|) (b z)) =ᵐ[
      volume.restrict (scalarParabolicOpenCylinder a T Ω)] fun z => |w z| := by
    filter_upwards [hae, ae_restrict_mem hU] with z hz hzu
    change |U.piecewise w (fun _ => 0) z| ≤ _ at hz
    rw [piecewise_eq_of_mem U w (fun _ => 0) hzu] at hz
    exact min_eq_left hz
  have hmin := Measure.eqOn_open_of_ae_eq heq (isOpen_Ioo.prod hΩ)
    (hw.abs.inf hbc.continuousOn)
    hw.abs
  intro z hz
  exact min_eq_left_iff.mp (hmin hz)

/-- An almost-everywhere time bound holds pointwise for a continuous interior representative. -/
theorem abs_le_source_time_of_continuousOn_of_ae_slices {d : ℕ}
    {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (a T M : ℝ) (w : TimeVelocity d → ℝ)
    (hw : ContinuousOn w (scalarParabolicOpenCylinder a T Ω))
    (hb : ∀ᵐ t ∂volume.restrict (Ioo a T),
      ∀ᵐ y ∂PDE.volumeOn Ω, |w (t, y)| ≤ M * (T - t)) :
    ∀ z ∈ scalarParabolicOpenCylinder a T Ω, |w z| ≤ M * (T - z.1) :=
  abs_le_of_continuousOn_of_ae_slices hΩ a T w (fun z => M * (T - z.1))
    (continuous_const.mul (continuous_const.sub continuous_fst)) hw hb

end HypoellipticAleksandrov.Parabolic.LocalHolder
