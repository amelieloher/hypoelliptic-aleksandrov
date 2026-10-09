module

public import HypoellipticAleksandrov.KineticAleksandrov.MovingKernel
public import Mathlib.MeasureTheory.Measure.Comap
import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-! # Recovering valid-fiber measures from supported ambient measures -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open Set MeasureTheory

/-- A supported ambient measure is exactly the pushforward of its valid-fiber comap. -/
theorem map_comap_evolutionState_eq {d : ℕ} {D : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (hD : MeasurableSet D) (s : ℝ)
    (μ : Measure (EvolutionAmbientState d))
    (hsupport : μ (evolutionStateSet D γ s)ᶜ = 0) :
    Measure.map (Subtype.val : EvolutionState D γ s → EvolutionAmbientState d)
      (μ.comap Subtype.val) = μ := by
  have he := MeasurableEmbedding.subtype_coe (measurableSet_evolutionStateSet (γ := γ) hD s)
  rw [he.map_comap, Subtype.range_coe]
  apply Measure.restrict_eq_self_of_ae_mem
  exact ae_iff.mpr hsupport

/-- The valid-fiber comap of a finite supported ambient measure has the same real mass. -/
theorem comap_evolutionState_real_univ {d : ℕ} {D : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (hD : MeasurableSet D) (s : ℝ)
    (μ : Measure (EvolutionAmbientState d)) [IsFiniteMeasure μ]
    (hsupport : μ (evolutionStateSet D γ s)ᶜ = 0) :
    (μ.comap (Subtype.val : EvolutionState D γ s → EvolutionAmbientState d)).real univ =
      μ.real univ := by
  have he := congrArg (fun ν : Measure (EvolutionAmbientState d) => ν.real univ)
    (map_comap_evolutionState_eq hD s μ hsupport)
  simpa only [map_measureReal_apply_of_aemeasurable
    measurable_subtype_coe.aemeasurable MeasurableSet.univ,
    preimage_univ] using he

end HypoellipticAleksandrov.KineticAleksandrov.Decay
