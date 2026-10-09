module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BelowFourDensityStatement
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! # Transfer of real densities and Lp bounds through positive measure domination -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter HypoellipticAleksandrov
open scoped ENNReal

/-- Kinetic volume is sigma finite through its literal product-coordinate equivalence. -/
theorem density_volume_sigmaFinite : SigmaFinite (volume : Measure Point) := by
  change SigmaFinite (Measure.map (KineticPoint.equivProd 1).symm volume)
  exact (KineticPoint.homeomorphProd 1).symm.measurableEmbedding.sigmaFinite_map

/-- A finite dominated measure inherits a nonnegative measurable density and its Lp norm. -/
theorem density_of_le_withDensity {X : Type*} [MeasurableSpace X]
    (m ν : Measure X) [SigmaFinite m] [IsFiniteMeasure ν]
    (f : X → ℝ) (_hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (p : ℝ≥0∞) (hfp : MemLp f p m)
    (hle : ν ≤ m.withDensity (fun x => ENNReal.ofReal (f x))) :
    ∃ g : X → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x) ∧
      ν = m.withDensity (fun x => ENNReal.ofReal (g x)) ∧
      MemLp g p m ∧ eLpNorm g p m ≤ eLpNorm f p m := by
  have hac : ν ≪ m := hle.absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)
  let g := fun x => (ν.rnDeriv m x).toReal
  have hgm : Measurable g := (Measure.measurable_rnDeriv ν m).ennreal_toReal
  have hrle : ∀ᵐ x ∂m, ν.rnDeriv m x ≤ ENNReal.ofReal (f x) := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀
      (Measure.measurable_rnDeriv ν m).aemeasurable
    intro E hE _
    have h := Measure.le_iff.1 hle E hE
    rw [← Measure.withDensity_rnDeriv_eq ν m hac, withDensity_apply _ hE,
      withDensity_apply _ hE] at h
    exact h
  have hgf : ∀ᵐ x ∂m, ‖g x‖ ≤ ‖f x‖ := by
    filter_upwards [hrle] with x hx
    simp only [Real.norm_eq_abs, abs_of_nonneg (hf0 x),
      abs_of_nonneg (show 0 ≤ g x from ENNReal.toReal_nonneg)]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hx).trans_eq
      (ENNReal.toReal_ofReal (hf0 x))
  have hgn := eLpNorm_mono_ae (p := p) hgm.aestronglyMeasurable hgf
  refine ⟨g, hgm, fun _ => ENNReal.toReal_nonneg, ?_,
    hgn.trans_lt hfp, hgn⟩
  rw [← Measure.withDensity_rnDeriv_eq ν m hac]
  apply withDensity_congr_ae
  filter_upwards [Measure.rnDeriv_lt_top ν m] with x hx
  exact (ENNReal.ofReal_toReal hx.ne).symm

/-- A restricted dominated measure inherits the local norm of the dominating density. -/
theorem density_restrict_of_le_withDensity {X : Type*} [MeasurableSpace X]
    (m ν : Measure X) [SigmaFinite m] [IsFiniteMeasure ν]
    (D Q : Set X) (hD : MeasurableSet D) (hQ : MeasurableSet Q)
    (f : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (p : ℝ≥0∞) (hfp : MemLp f p (m.restrict D))
    (hle : ν ≤ (m.restrict D).withDensity (fun x => ENNReal.ofReal (f x))) :
    ∃ g : X → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x) ∧
      ν.restrict Q = (m.restrict Q).withDensity (fun x => ENNReal.ofReal (g x)) ∧
      MemLp g p (m.restrict Q) ∧
      eLpNorm g p (m.restrict Q) ≤ eLpNorm f p (m.restrict D) := by
  let F := D.indicator f
  have hFm : Measurable F := hf.indicator hD
  have hF0 : ∀ x, 0 ≤ F x := fun x => indicator_nonneg (fun _ _ => hf0 _) x
  have hFp : MemLp F p m := (memLp_indicator_iff_restrict hD).2 hfp
  have hd : m.withDensity (fun x => ENNReal.ofReal (F x)) =
      (m.restrict D).withDensity (fun x => ENNReal.ofReal (f x)) := by
    rw [← withDensity_indicator hD]
    congr 1
    ext x
    by_cases hx : x ∈ D <;> simp [F, hx]
  obtain ⟨g, hgm, hg0, hgd, hgp, hgn⟩ :=
    density_of_le_withDensity m ν F hFm hF0 p hFp (hd.symm ▸ hle)
  refine ⟨g, hgm, hg0, ?_, hgp.restrict Q, ?_⟩
  · rw [hgd, restrict_withDensity hQ]
  · exact (eLpNorm_restrict_le g p m Q).trans
      (hgn.trans_eq (eLpNorm_indicator_eq_eLpNorm_restrict hD))

/-- Every forward cylinder lies inside its literal observation strip. -/
theorem cylinder_subset_density_strip (Z₀ : Point) (R : ℝ) (hR : 0 < R) :
    forwardCylinder Z₀ R hR ⊆
      {z | Z₀.time < z.time ∧ z.time < Z₀.time + R ^ 2 ∧
        z.velocity 0 ∈ (capacityCylinderInterval Z₀ R hR).carrier} := by
  intro z hz
  exact ⟨hz.1, hz.2.1, (capacityCylinderPole Z₀ z R hR hz).2.2⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
