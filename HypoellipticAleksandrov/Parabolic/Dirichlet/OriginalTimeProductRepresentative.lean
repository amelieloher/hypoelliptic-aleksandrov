module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeProductRepresentative
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGradientProductRepresentative

/-!
# Original-time product representatives

This module reflects the reverse-time scalar product representatives
to the literal original-time interval, without imposing an order on its
endpoints.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-! The reflection `r ↦ r₁ - r` sends the original-time restricted volume to
the corresponding reverse-time restricted volume. -/
private theorem originalTimeReflection_measurePreserving_toReverseTime (r₀ r₁ : ℝ) :
    MeasurePreserving (fun r : ℝ => r₁ - r)
      (volume.restrict (Set.Ioo r₀ r₁)) (reverseTimeVolume (r₁ - r₀)) := by
  have hreflection : MeasurePreserving (fun r : ℝ => r₁ - r)
      (volume : Measure ℝ) volume := by
    simpa only [Function.comp_def, sub_eq_add_neg] using
      (measurePreserving_add_left (volume : Measure ℝ) r₁).comp
        (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hpreimage : (fun r : ℝ => r₁ - r) ⁻¹' Set.Ioo 0 (r₁ - r₀) =
      Set.Ioo r₀ r₁ := by
    rw [preimage_const_sub_Ioo]
    congr 1 <;> ring
  rw [reverseTimeVolume, reverseTimeOpenInterval, ← hpreimage]
  exact hreflection.restrict_preimage isOpen_Ioo.measurableSet

/-! The original-time and spatial restricted volumes form the literal
time--velocity restricted volume on their product set. -/
private theorem originalTimeVolume_prod_volumeOn_eq_timeVelocityVolumeOn
    {d : ℕ} (r₀ r₁ : ℝ) (Ω : Set (PDE.Vec d)) :
    (volume.restrict (Set.Ioo r₀ r₁)).prod (PDE.volumeOn Ω) =
      timeVelocityVolumeOn (Set.Ioo r₀ r₁ ×ˢ Ω) := by
  rw [timeVelocityVolumeOn, volume_timeVelocity_eq_prod]
  simpa using Measure.prod_restrict (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (PDE.Vec d))) (Set.Ioo r₀ r₁) Ω

/-- A reverse-time spatial `L²` curve has an original-time joint scalar
representative whose spatial slices agree almost everywhere with its reflected
timewise values. -/
theorem exists_originalTimeL2V_value_product_representative
    {d : ℕ} {Ω : Set (PDE.Vec d)} (r₀ r₁ : ℝ) (hΩ : IsOpen Ω)
    (u : ReverseTimeL2V hΩ (r₁ - r₀)) :
    ∃ U : TimeVelocity d → ℝ,
      MemLp U (2 : ℝ≥0∞)
        (timeVelocityVolumeOn (Set.Ioo r₀ r₁ ×ˢ Ω)) ∧
      ∀ᵐ r ∂volume.restrict (Set.Ioo r₀ r₁),
        (fun y => U (r, y)) =ᵐ[PDE.volumeOn Ω]
          fun y => valueCLM hΩ (u (r₁ - r)) y := by
  obtain ⟨Urev, hU_memLp, hU_slice⟩ :=
    exists_reverseTimeL2V_value_product_representative hΩ (r₁ - r₀) u
  let htime := originalTimeReflection_measurePreserving_toReverseTime r₀ r₁
  let hproduct := htime.prod (MeasurePreserving.id (PDE.volumeOn Ω))
  rw [← reverseTimeVolume_prod_volumeOn_eq_timeVelocityVolumeOn (r₁ - r₀) Ω] at hU_memLp
  refine ⟨fun z => Urev (r₁ - z.1, z.2), ?_, ?_⟩
  · rw [← originalTimeVolume_prod_volumeOn_eq_timeVelocityVolumeOn r₀ r₁ Ω]
    simpa only [Function.comp_def, Prod.map_def, id_eq] using
      hU_memLp.comp_measurePreserving hproduct
  · filter_upwards [htime.quasiMeasurePreserving.ae hU_slice] with r hr
    exact hr

/-- The scalar coordinates of a reverse-time spatial `L²` gradient have
original-time joint representatives with a common almost-everywhere time-slice
event. -/
theorem exists_originalTimeL2V_gradient_coord_product_representatives
    {d : ℕ} {Ω : Set (PDE.Vec d)} (r₀ r₁ : ℝ) (hΩ : IsOpen Ω)
    (u : ReverseTimeL2V hΩ (r₁ - r₀)) :
    ∃ G : Fin d → TimeVelocity d → ℝ,
      (∀ j, MemLp (G j) (2 : ℝ≥0∞)
        (timeVelocityVolumeOn (Set.Ioo r₀ r₁ ×ˢ Ω))) ∧
      ∀ᵐ r ∂volume.restrict (Set.Ioo r₀ r₁), ∀ j,
        (fun y => G j (r, y)) =ᵐ[PDE.volumeOn Ω]
          fun y => gradientCLM hΩ (u (r₁ - r)) y j := by
  obtain ⟨Grev, hG_memLp, hG_slice⟩ :=
    exists_reverseTimeL2V_gradient_coord_product_representatives hΩ (r₁ - r₀) u
  let htime := originalTimeReflection_measurePreserving_toReverseTime r₀ r₁
  let hproduct := htime.prod (MeasurePreserving.id (PDE.volumeOn Ω))
  refine ⟨fun j z => Grev j (r₁ - z.1, z.2), ?_, ?_⟩
  · intro j
    rw [← reverseTimeVolume_prod_volumeOn_eq_timeVelocityVolumeOn (r₁ - r₀) Ω] at hG_memLp
    rw [← originalTimeVolume_prod_volumeOn_eq_timeVelocityVolumeOn r₀ r₁ Ω]
    simpa only [Function.comp_def, Prod.map_def, id_eq] using
      (hG_memLp j).comp_measurePreserving hproduct
  · filter_upwards [htime.quasiMeasurePreserving.ae hG_slice] with r hr
    intro j
    exact hr j

end HypoellipticAleksandrov.Parabolic.Dirichlet
