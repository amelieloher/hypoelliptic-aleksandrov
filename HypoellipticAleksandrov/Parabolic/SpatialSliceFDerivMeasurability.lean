module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialCoordinateShiftCarrierGeometry
public import HypoellipticAleksandrov.Parabolic.SpatialTranslationWeakDerivatives
public import HypoellipticAleksandrov.Parabolic.WeakDerivatives
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Measurability of fixed-time spatial derivatives

This module obtains joint almost-everywhere measurability of a literal spatial
directional derivative from joint measurability of the original function and
pointwise differentiability of its fixed-time spatial slices.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped Topology

/-- A jointly measurable function with differentiable spatial slices has a
measurable literal directional spatial derivative on a compactly contained
product carrier. -/
theorem aestronglyMeasurable_spatialSliceFDeriv_apply_on_prod
    {d : ℕ}
    {Iout Iin : Set ℝ}
    {O₀ O₁ : Set (PDE.Vec d)}
    (hI : Iin ⊆ Iout)
    (hTarget : NullMeasurableSet (Iin ×ˢ O₁)
      (volume : Measure (TimeVelocity d)))
    (hO₀ : IsOpen O₀)
    (hO₁compact : IsCompact (closure O₁))
    (hO₁O₀ : closure O₁ ⊆ O₀)
    (q : TimeVelocity d → ℝ)
    (hq : AEStronglyMeasurable q
      (timeVelocityVolumeOn (Iout ×ˢ O₀)))
    (hqDiff : ∀ r ∈ Iout, ∀ y ∈ O₀,
      DifferentiableAt ℝ (fun x => q (r, x)) y)
    (k : Fin d) :
    AEStronglyMeasurable
      (fun z =>
        (fderiv ℝ (fun y => q (z.1, y)) z.2)
          (PDE.basisVec k))
      (timeVelocityVolumeOn (Iin ×ˢ O₁)) := by
  obtain ⟨δ, hδ, hcarrier⟩ :=
    Dirichlet.IsCompact.exists_spatialCoordinateShiftCarrier_subset_open
      hO₁compact hO₀ hO₁O₀
  let a : ℕ → ℝ := fun n => δ / ((n + 2 : ℕ) : ℝ)
  have ha_pos (n : ℕ) : 0 < a n := by
    dsimp [a]
    positivity
  have ha_le (n : ℕ) : |a n| ≤ δ := by
    rw [abs_of_pos (ha_pos n)]
    dsimp [a]
    have hn : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ n + 2 by omega)
    exact div_le_self hδ.le hn
  have ha_tendsto : Tendsto a atTop (𝓝 0) := by
    simpa only [Function.comp_def, a] using (tendsto_const_div_atTop_nhds_zero_nat δ).comp
      (tendsto_add_atTop_nat 2)
  have ha_tendsto_ne : Tendsto a atTop (𝓝[≠] 0) := by
    apply (tendsto_nhdsWithin_iff).2
    refine ⟨ha_tendsto, ?_⟩
    filter_upwards with n
    simpa only [Function.comp_def, Set.mem_compl_iff, Set.mem_singleton_iff] using (ha_pos n).ne'
  let U : Set (TimeVelocity d) := Iout ×ˢ O₀
  let V : Set (TimeVelocity d) := Iin ×ˢ O₁
  have hVU : V ⊆ U := by
    intro z hz
    exact ⟨hI hz.1, hO₁O₀ (subset_closure hz.2)⟩
  have hshift (n : ℕ) : MapsTo (spatialShift k (a n)) V U := by
    intro z hz
    constructor
    · simpa only [Function.comp_def, spatialShift_fst] using hI hz.1
    · exact hcarrier
        (Dirichlet.mem_spatialCoordinateShiftCarrier_of_mem_of_abs_le
          (subset_closure hz.2) (ha_le n))
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (spatialDifferenceQuotient k (a n) q) (timeVelocityVolumeOn V) := by
    have ht : AEStronglyMeasurable (q ∘ spatialShift k (a n))
        (timeVelocityVolumeOn V) :=
      hq.comp_quasiMeasurePreserving
        ((spatialShift_measurePreserving k (a n)).quasiMeasurePreserving.restrict
          (hshift n))
    have ho : AEStronglyMeasurable q (timeVelocityVolumeOn V) :=
      hq.mono_measure (Measure.restrict_mono_set volume hVU)
    have hs := ht.sub ho
    convert hs.const_smul (a n)⁻¹ using 1
    funext z
    simp only [spatialDifferenceQuotient_apply, spatialTranslate_apply,
      Pi.smul_apply, Pi.sub_apply, Function.comp_def, smul_eq_mul]
    ring
  apply aestronglyMeasurable_of_tendsto_ae atTop hmeas
  filter_upwards [ae_restrict_mem₀ hTarget] with z hz
  have hzU : z ∈ U := hVU hz
  let g : ℝ → ℝ := fun h => q (z.1, z.2 + h • PDE.basisVec k)
  have hline : HasDerivAt (fun h : ℝ => z.2 + h • PDE.basisVec k)
      (PDE.basisVec k) 0 := by
    simpa only [one_smul] using ((hasDerivAt_id' (𝕜 := ℝ) 0).smul_const
      (PDE.basisVec k)).const_add z.2
  have hg : HasDerivAt g
      ((fderiv ℝ (fun y => q (z.1, y)) z.2) (PDE.basisVec k)) 0 := by
    have hout : HasFDerivAt (fun y => q (z.1, y))
        (fderiv ℝ (fun y => q (z.1, y)) z.2)
        (z.2 + (0 : ℝ) • PDE.basisVec k) := by
      simpa only [Function.comp_def, zero_smul, add_zero] using
        (hqDiff z.1 hzU.1 z.2 hzU.2).hasFDerivAt
    simpa only [Function.comp_def, g, Function.comp_def] using hout.comp_hasDerivAt 0 hline
  have hslope := hg.tendsto_slope_zero.comp ha_tendsto_ne
  apply hslope.congr'
  filter_upwards with n
  dsimp only [Function.comp_def, g]
  rw [spatialDifferenceQuotient_apply, spatialTranslate_apply, spatialShift_apply]
  simp only [zero_add, zero_smul, add_zero, div_eq_mul_inv, smul_eq_mul]
  ring

end HypoellipticAleksandrov.Parabolic
