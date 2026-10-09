module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Duhamel

/-! # Identification of Duhamel source slices with the supplied evolution operators -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set

/-- A bounded Borel spacetime source restricted to one absolute-time state slice. -/
def duhamelSlice {d : ℕ} (g : BoundedBorel (KineticPoint d)) (r : ℝ) :
    BoundedBorel (EvolutionAmbientState d) := by
  refine ⟨fun w => g ⟨r, w.1, w.2⟩, ?_, ?_⟩
  · convert g.measurable.comp ((KineticPoint.measurable_equivProd_symm d).comp
      (measurable_const.prodMk measurable_id)) using 1
    rfl
  · obtain ⟨C, hC, hg⟩ := g.exists_bound
    exact ⟨C, hC, fun w => hg ⟨r, w.1, w.2⟩⟩

/-- Each source-time kernel integral equals the supplied terminal evolution action. -/
theorem duhamelSourceIntegral_eq_evolution {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (hΩ : MeasurableSet Ω)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (g : BoundedBorel (KineticPoint d)) (σ r : ℝ) (hσr : σ ≤ r)
    (p : EvolutionState Ω γ σ) :
    duhamelSourceIntegral K g (evolutionQueryOfState Ω γ σ r hσr p) =
      S σ r hσr (terminalStateDatum (duhamelSlice g r)) p := by
  rw [hreal.2.1 σ r hσr p (terminalStateDatum (duhamelSlice g r))]
  unfold duhamelSourceIntegral
  rw [← K.map_fiberKernel_eq_master hΩ σ r hσr p]
  exact integral_map measurable_subtype_coe.aemeasurable
    (duhamelSlice g r).measurable.aestronglyMeasurable

/-- Integrating the supplied terminal operators gives the absolute-time Duhamel potential. -/
theorem duhamelPotential_eq_evolution_integral {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (hΩ : MeasurableSet Ω)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (g : BoundedBorel (KineticPoint d)) (σ τplus : ℝ)
    (p : EvolutionState Ω γ σ) :
    duhamelPotential K τplus g ⟨σ, p.1.1, p.1.2⟩ =
      ∫ r in Ioc σ τplus, if hσr : σ ≤ r then
        S σ r hσr (terminalStateDatum (duhamelSlice g r)) p else 0 := by
  classical
  unfold duhamelPotential
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro r
  dsimp only
  by_cases hr : σ ≤ r
  · rw [dite_eq_left hr]
    have hh : (KineticPoint.mk σ p.1.1 p.1.2).time ≤ r ∧
        (KineticPoint.mk σ p.1.1 p.1.2).position ∈
          movingDomain Ω γ (KineticPoint.mk σ p.1.1 p.1.2).time := ⟨hr, p.2.1⟩
    rw [duhamelIntegrand, dite_eq_left hh]
    exact duhamelSourceIntegral_eq_evolution hΩ B b S K hreal g σ r hr p
  · rw [dite_eq_right hr, duhamelIntegrand, dite_eq_right (fun h => hr h.1)]

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
