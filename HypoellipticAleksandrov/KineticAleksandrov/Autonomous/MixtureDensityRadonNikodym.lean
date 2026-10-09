module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! # Real densities of finite absolutely continuous measures

The measure lemma is independent of the analytic construction of a Green kernel,
so elaboration never unfolds that construction while checking Radon--Nikodym facts.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open MeasureTheory

/-- A finite absolutely continuous measure has a measurable nonnegative real density. -/
theorem mixture_real_density_of_absolutelyContinuous {X : Type*} [MeasurableSpace X]
    (mu m : Measure X) [IsFiniteMeasure mu] [SigmaFinite m] (hac : mu ≪ m) :
    ∃ g : X → ℝ, Measurable g ∧ (∀ p, 0 ≤ g p) ∧
      mu = m.withDensity (fun p => ENNReal.ofReal (g p)) := by
  refine ⟨fun p => (mu.rnDeriv m p).toReal,
    (Measure.measurable_rnDeriv mu m).ennreal_toReal,
    fun _ => ENNReal.toReal_nonneg, ?_⟩
  apply (Measure.withDensity_rnDeriv_eq mu m hac).symm.trans
  apply withDensity_congr_ae
  filter_upwards [Measure.rnDeriv_lt_top mu m] with p hp
  exact (ENNReal.ofReal_toReal hp.ne).symm

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
