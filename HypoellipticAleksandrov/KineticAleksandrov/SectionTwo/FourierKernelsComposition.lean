module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.FourierKernelsTranslation
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! # Fourier phase factorization and Chapman--Kolmogorov integration -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

/-- A derived fiber kernel is finite uniformly, by its sub-Markov mass bound. -/
instance fiberKernel_isFiniteKernel {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω)
    (σ τ : ℝ) (hστ : σ ≤ τ) : ProbabilityTheory.IsFiniteKernel (K.fiberKernel hΩ σ τ hστ) :=
  ⟨1, ENNReal.one_lt_top, K.fiberKernel_mass_le_one hΩ σ τ hστ⟩

/-- Integrals against the ambient master measure equal integrals against the derived fiber. -/
theorem master_integral_eq_fiber {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω)
    (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ)
    (f : EvolutionAmbientState d → ℂ) (hf : Measurable f) :
    (∫ w, f w ∂K.master (evolutionQueryOfState Ω γ σ τ hστ p)) =
      ∫ w, f w.1 ∂K.fiberKernel hΩ σ τ hστ p := by
  rw [← K.map_fiberKernel_eq_master hΩ σ τ hστ p]
  exact integral_map measurable_subtype_coe.aemeasurable hf.aestronglyMeasurable

/-- Fourier phases factor at the intermediate position, with the source sign convention. -/
theorem fourierPhase_factor {d : ℕ} (ξ z : PDE.Vec d)
    (w w' : EvolutionAmbientState d) :
    fourierPhase ξ z w' = fourierPhase ξ z w * fourierPhase ξ w.2 w' := by
  have hd : PDE.vecDot ξ (w'.2 - z) =
      PDE.vecDot ξ (w.2 - z) + PDE.vecDot ξ (w'.2 - w.2) := by
    unfold PDE.vecDot
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply]
    ring
  unfold fourierPhase
  rw [hd, Complex.ofReal_add, mul_add, Complex.exp_add]

/-- Chapman--Kolmogorov gives iterated integration of every bounded Borel complex datum. -/
theorem master_integral_composition {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω)
    (hcomp : K.HasComposition hΩ) (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ)
    (p : EvolutionState Ω γ σ) (f : EvolutionAmbientState d → ℂ)
    (hf : Measurable f) (hbound : ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C) :
    (∫ w, f w ∂K.master (evolutionQueryOfState Ω γ σ τ (hσr.trans hrτ) p)) =
      ∫ w, (∫ w', f w' ∂K.master (evolutionQueryOfState Ω γ r τ hrτ w))
        ∂K.fiberKernel hΩ σ r hσr p := by
  rw [master_integral_eq_fiber K hΩ σ τ (hσr.trans hrτ) p f hf,
    hcomp σ r τ hσr hrτ]
  have hi : Integrable (fun w : EvolutionState Ω γ τ => f w.1)
      ((K.fiberKernel hΩ r τ hrτ ∘ₖ K.fiberKernel hΩ σ r hσr) p) := by
    obtain ⟨C, hC⟩ := hbound
    exact Integrable.mono' (integrable_const C)
      (hf.comp measurable_subtype_coe).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun w => hC w.1))
  rw [ProbabilityTheory.Kernel.integral_comp hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun w =>
    (master_integral_eq_fiber K hΩ r τ hrτ w f hf).symm

/-- Every Fourier kernel value has norm at most one, uniformly in the Borel set. -/
theorem fourierKernel_apply_norm_le_one {d : ℕ}
    (K : MovingFiberKernel (wholeSpace d) (fun _ => 0))
    (σ τ : ℝ) (hστ : σ ≤ τ) (ξ v : PDE.Vec d) (E : Set (PDE.Vec d)) :
    ‖fourierKernel K σ τ hστ ξ v E‖ ≤ 1 := by
  have he : (fourierKernel K σ τ hστ ξ v).variation E ≤ 1 :=
    (measure_mono (subset_univ E)).trans
      (fourierKernel_totalVariation_le_one K σ τ hστ ξ v)
  have hn := VectorMeasure.norm_measure_le_variation
    (μ := fourierKernel K σ τ hστ ξ v) (ne_of_lt (he.trans_lt ENNReal.one_lt_top))
  exact hn.trans (by simpa only [Measure.real, ENNReal.toReal_one] using
    ENNReal.toReal_mono ENNReal.one_ne_top he)

/-- The Fourier kernel obeys temporal composition with complex multiplication pairing. -/
theorem fourierKernel_composition {d : ℕ}
    (K : MovingFiberKernel (wholeSpace d) (fun _ => 0))
    (hcomp : K.HasComposition MeasurableSet.univ)
    (hcov : IsTranslationCovariantEvolution (wholeSpace d) (fun _ => 0)
      MeasurableSet.univ K)
    (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ) (ξ v : PDE.Vec d)
    (E : Set (PDE.Vec d)) (hE : MeasurableSet E) :
    fourierKernel K σ τ (hσr.trans hrτ) ξ v E =
      ∫ᵛ v', fourierKernel K r τ hrτ ξ v' E
        ∂[ContinuousLinearMap.mul ℝ ℂ; fourierKernel K σ r hσr ξ v] := by
  let p : EvolutionState (wholeSpace d) (fun _ => 0) σ :=
    ⟨(v, 0), (wholeSpaceQuery σ r hσr v 0).property.2⟩
  let f := fun v' => fourierKernel K r τ hrτ ξ v' E
  let g := (E ×ˢ univ).indicator (fourierPhase ξ (0 : PDE.Vec d))
  have hf : Measurable f := measurable_fourierKernel_apply K r τ hrτ ξ E hE
  have hg : Measurable g := (continuous_fourierPhase ξ 0).measurable.indicator
    (hE.prod MeasurableSet.univ)
  have hgb : ∃ C : ℝ, ∀ w, ‖g w‖ ≤ C := by
    refine ⟨1, fun w => ?_⟩
    by_cases hw : w ∈ E ×ˢ univ
    · simpa only [g, indicator_of_mem hw] using (norm_fourierPhase ξ 0 w).le
    · simp only [g, indicator_of_notMem hw, norm_zero, zero_le_one]
  have hfb : ∃ C : ℝ, ∀ v', ‖f v'‖ ≤ C :=
    ⟨1, fun v' => fourierKernel_apply_norm_le_one K r τ hrτ ξ v' E⟩
  rw [fourierProjection_integral_complex K _ ξ _
    (fourierKernel_spec K σ r hσr ξ v) f hf hfb]
  change _ = ∫ w, f w.1 * fourierPhase ξ 0 w
    ∂K.master (evolutionQueryOfState (wholeSpace d) (fun _ => 0) σ r hσr p)
  rw [fourierKernel_spec K σ τ (hσr.trans hrτ) ξ v E hE,
    ← integral_indicator (hE.prod MeasurableSet.univ)]
  change (∫ w, g w ∂K.master
    (evolutionQueryOfState (wholeSpace d) (fun _ => 0) σ τ (hσr.trans hrτ) p)) = _
  rw [master_integral_composition K MeasurableSet.univ hcomp σ r τ hσr hrτ p g hg hgb,
    master_integral_eq_fiber K MeasurableSet.univ σ r hσr p
      (fun w => f w.1 * fourierPhase ξ 0 w)
      ((hf.comp measurable_fst).mul (continuous_fourierPhase ξ 0).measurable)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro w
  change (∫ w', g w' ∂K.master (wholeSpaceQuery r τ hrτ w.1.1 w.1.2)) =
    fourierKernel K r τ hrτ ξ w.1.1 E * fourierPhase ξ 0 w.1
  rw [← fourierKernel_eq_startingPosition K hcov r τ hrτ ξ w.1.1 w.1.2,
    fourierProjection_spec K _ ξ E hE,
    ← integral_indicator (hE.prod MeasurableSet.univ), ← integral_mul_const]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro w'
  by_cases hw' : w'.1 ∈ E
  · simp only [g, indicator_of_mem (show w' ∈ E ×ˢ univ from ⟨hw', mem_univ _⟩)]
    rw [fourierPhase_factor ξ 0 w.1 w', mul_comm]
    rfl
  · simp only [g, indicator_of_notMem
      (show w' ∉ E ×ˢ univ from fun hw => hw' hw.1), zero_mul]

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
