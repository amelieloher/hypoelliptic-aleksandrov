module

public import HypoellipticAleksandrov.Geometry.KineticPointMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionProductNorm
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionGeometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! # Stationary shell norms on the fixed native cylinder -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory Set
open scoped ENNReal

/-- A stationary spatial source on the cylinder is bounded by its full spatial norm
and the exact finite time factor; the spatial carrier is not renormalized. -/
theorem construction_stationary_norm_le {d : ℕ} (T S : ℝ) (hS : 0 < S)
    (f : XV d → ℝ) (hf : Measurable f) (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    eLpNorm (fun P : KineticPoint d => f (P.position, P.velocity)) p
      (volume.restrict (backwardCylinder (⟨T, 0, 0⟩ : KineticPoint d) S)) ≤
      (volume (Ioo (T - S ^ 2) T)) ^ (1 / p.toReal) * eLpNorm f p volume := by
  let D : Set (ℝ × XV d) := Ioo (T - S ^ 2) T ×ˢ univ
  let e := KineticPoint.equivProd d
  have hD : MeasurableSet D := measurableSet_Ioo.prod MeasurableSet.univ
  have hsub : backwardCylinder (⟨T, 0, 0⟩ : KineticPoint d) S ⊆ e ⁻¹' D := by
    intro P hP
    have hh := (construction_mem_cylinder_iff T S hS P).mp hP
    exact ⟨⟨hh.1, hh.2.1⟩, mem_univ _⟩
  apply (eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hsub)).trans_eq
  have hmp := (KineticPoint.measurePreserving_equivProd d).restrict_preimage hD
  have he := eLpNorm_comp_measurePreserving (p := p)
    (hf.comp measurable_snd).aestronglyMeasurable.restrict hmp
  change eLpNorm ((fun z : ℝ × XV d => f z.2) ∘ e) p
    (volume.restrict (e ⁻¹' D)) = _
  apply he.trans
  rw [Measure.volume_eq_prod, ← Measure.restrict_prod_eq_prod_univ]
  simpa only [Function.comp_def, Measure.restrict_apply_univ] using
    construction_eLpNorm_snd (volume.restrict (Ioo (T - S ^ 2) T)) volume f hf p hp0 hpTop

/-- A profile-domain indicator gives the literal restricted stationary norm. -/
theorem construction_stationary_indicator_norm_le {d : ℕ} (T S : ℝ) (hS : 0 < S)
    (D : Set (XV d)) (hD : MeasurableSet D) (f : XV d → ℝ) (hf : Measurable f)
    (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    eLpNorm (fun P : KineticPoint d => D.indicator f (P.position, P.velocity)) p
      (volume.restrict (backwardCylinder (⟨T, 0, 0⟩ : KineticPoint d) S)) ≤
      (volume (Ioo (T - S ^ 2) T)) ^ (1 / p.toReal) *
        eLpNorm f p (volume.restrict D) := by
  simpa only [eLpNorm_indicator_eq_eLpNorm_restrict hD] using
    construction_stationary_norm_le T S hS (D.indicator f) (hf.indicator hD) p hp0 hpTop

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
