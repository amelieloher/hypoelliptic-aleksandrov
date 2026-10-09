module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.FourierKernels
import Mathlib.MeasureTheory.Measure.Map

/-! # Translation independence of displacement Fourier measures -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

/-- Ambient position translation is Borel. -/
theorem measurable_evolutionAmbientStateShift {d : ℕ} (h : PDE.Vec d) :
    Measurable (evolutionAmbientStateShift h) := by
  exact measurable_fst.prodMk (measurable_snd.add_const h)

/-- Translation on the terminal state subtype is Borel. -/
theorem measurable_evolutionStateShift {d : ℕ} (Ω : Set (PDE.Vec d))
    (γ : ℝ → PDE.Vec d) (σ : ℝ) (h : PDE.Vec d) :
    Measurable (evolutionStateShift Ω γ σ h) :=
  ((measurable_evolutionAmbientStateShift h).comp measurable_subtype_coe).subtype_mk

/-- Fiber covariance pushes forward to the ambient master measures. -/
theorem master_translation {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (hΩ : MeasurableSet Ω) (K : MovingFiberKernel Ω γ)
    (hcov : IsTranslationCovariantEvolution Ω γ hΩ K)
    (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ) (h : PDE.Vec d) :
    Measure.map (evolutionAmbientStateShift h)
        (K.master (evolutionQueryOfState Ω γ σ τ hστ p)) =
      K.master (evolutionQueryOfState Ω γ σ τ hστ (evolutionStateShift Ω γ σ h p)) := by
  rw [← K.map_fiberKernel_eq_master hΩ σ τ hστ p,
    Measure.map_map (measurable_evolutionAmbientStateShift h) measurable_subtype_coe]
  have hc := congrArg
    (Measure.map (Subtype.val : EvolutionState Ω γ τ → EvolutionAmbientState d))
    (hcov σ τ hστ h p)
  rw [Measure.map_map measurable_subtype_coe
    (measurable_evolutionStateShift Ω γ τ h), K.map_fiberKernel_eq_master] at hc
  exact hc

/-- Translating both positions leaves the displacement Fourier phase unchanged. -/
theorem fourierPhase_shift {d : ℕ} (ξ z h : PDE.Vec d) (w : EvolutionAmbientState d) :
    fourierPhase ξ (z + h) (evolutionAmbientStateShift h w) = fourierPhase ξ z w := by
  simp only [fourierPhase, evolutionAmbientStateShift, add_sub_add_right_eq_sub]

/-- The Fourier projection is independent of simultaneous starting-position translation. -/
theorem fourierProjection_translation {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (hΩ : MeasurableSet Ω) (K : MovingFiberKernel Ω γ)
    (hcov : IsTranslationCovariantEvolution Ω γ hΩ K)
    (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ) (h ξ : PDE.Vec d) :
    fourierProjection K
      (evolutionQueryOfState Ω γ σ τ hστ (evolutionStateShift Ω γ σ h p)) ξ =
    fourierProjection K (evolutionQueryOfState Ω γ σ τ hστ p) ξ := by
  apply VectorMeasure.ext
  intro E hE
  rw [fourierProjection_spec K _ ξ E hE, fourierProjection_spec K _ ξ E hE,
    ← master_translation hΩ K hcov σ τ hστ p h]
  rw [← integral_indicator (hE.prod MeasurableSet.univ),
    ← integral_indicator (hE.prod MeasurableSet.univ)]
  rw [integral_map (measurable_evolutionAmbientStateShift h).aemeasurable
    (((continuous_fourierPhase ξ _).measurable.indicator
      (hE.prod MeasurableSet.univ)).aestronglyMeasurable)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro w
  change (E ×ˢ univ).indicator (fourierPhase ξ (p.1.2 + h))
    (evolutionAmbientStateShift h w) = (E ×ˢ univ).indicator (fourierPhase ξ p.1.2) w
  by_cases hw : w.1 ∈ E
  · rw [indicator_of_mem (by exact ⟨hw, mem_univ _⟩),
      indicator_of_mem (by exact ⟨hw, mem_univ _⟩), fourierPhase_shift]
  · rw [indicator_of_notMem (by exact fun hw' => hw hw'.1),
      indicator_of_notMem (by exact fun hw' => hw hw'.1)]

/-- Starting position does not affect the whole-space Fourier kernel. -/
theorem fourierKernel_eq_startingPosition {d : ℕ}
    (K : MovingFiberKernel (wholeSpace d) (fun _ => 0))
    (hcov : IsTranslationCovariantEvolution (wholeSpace d) (fun _ => 0)
      MeasurableSet.univ K)
    (σ τ : ℝ) (hστ : σ ≤ τ) (ξ v z : PDE.Vec d) :
    fourierProjection K (wholeSpaceQuery σ τ hστ v z) ξ =
      fourierKernel K σ τ hστ ξ v := by
  let p : EvolutionState (wholeSpace d) (fun _ => 0) σ :=
    ⟨(v, 0), (wholeSpaceQuery σ τ hστ v 0).property.2⟩
  have hq : evolutionQueryOfState (wholeSpace d) (fun _ => 0) σ τ hστ
      (evolutionStateShift (wholeSpace d) (fun _ => 0) σ z p) =
      wholeSpaceQuery σ τ hστ v z := by
    apply Subtype.ext
    simp only [evolutionQueryOfState, evolutionStateShift, evolutionAmbientStateShift,
      wholeSpaceQuery, p, zero_add]
  have hp : evolutionQueryOfState (wholeSpace d) (fun _ => 0) σ τ hστ p =
      wholeSpaceQuery σ τ hστ v 0 := rfl
  have ht := fourierProjection_translation MeasurableSet.univ K hcov σ τ hστ p z ξ
  exact (congrArg (fun q => fourierProjection K q ξ) hq).symm.trans
    (ht.trans (congrArg (fun q => fourierProjection K q ξ) hp))

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
