module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.OccupationMeasure
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! # A dominated positive measure has a dominated real density

This measure-theoretic lemma transfers all occupation exponents at once from a
whole-space density to the killed interval occupation measure.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory Filter
open scoped ENNReal

/-- A finite measure dominated by a real density has a smaller real density. -/
theorem exists_real_density_of_le_withDensity {X : Type*} [MeasurableSpace X]
    (m ν : Measure X) [SigmaFinite m] [IsFiniteMeasure ν]
    (f : X → ℝ) (_hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hle : ν ≤ m.withDensity (fun x => ENNReal.ofReal (f x))) :
    ∃ g : X → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x) ∧ Integrable g m ∧
      (∀ᵐ x ∂m, g x ≤ f x) ∧
      (∀ φ : X → ℝ, (∫ x, φ x * g x ∂m) = ∫ x, φ x ∂ν) := by
  have hac : ν ≪ m := hle.absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)
  let g := fun x => (ν.rnDeriv m x).toReal
  have hrle : ∀ᵐ x ∂m, ν.rnDeriv m x ≤ ENNReal.ofReal (f x) := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀
      (Measure.measurable_rnDeriv ν m).aemeasurable
    intro E hE _
    have h := Measure.le_iff.1 hle E hE
    rw [← Measure.withDensity_rnDeriv_eq ν m hac, withDensity_apply _ hE,
      withDensity_apply _ hE] at h
    exact h
  refine ⟨g, (Measure.measurable_rnDeriv ν m).ennreal_toReal,
    fun _ => ENNReal.toReal_nonneg, ?_, ?_, ?_⟩
  · simpa only [integrableOn_univ] using
      Measure.integrableOn_toReal_rnDeriv (μ := ν) (ν := m) (measure_ne_top ν univ)
  · filter_upwards [hrle] with x hx
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hx).trans_eq
      (ENNReal.toReal_ofReal (hf0 x))
  · intro φ
    simpa only [mul_comm] using integral_toReal_rnDeriv_mul hac (f := φ)

end HypoellipticAleksandrov.KineticAleksandrov.Interval
