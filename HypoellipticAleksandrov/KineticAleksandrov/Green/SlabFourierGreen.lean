module

public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierOccupation
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.FourierKernelsVariation
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Green-measure integral calculus on the slab

* `firstMarginal_startingPosition`: the velocity marginal of the master kernel does not depend
  on the starting transported coordinate (translation covariance).
* `green_integral`: for a bounded complex Borel `f` supported in the slab `T < τ < 2T`,
  `∫ f dΓ = ∫_τ ∫_μ ∫_{master(σ₀→σ₀+τ)} f(τ,·)`.  The Green measure is identified with the explicit
  kernel-product measure by uniqueness (`existsUnique_greenMeasure`).
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Green

open MeasureTheory Set
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal NNReal ProbabilityTheory

/-- The first marginal of the master kernel is independent of the starting `z` (case W). -/
theorem firstMarginal_startingPosition {d : ℕ}
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hcov : IsTranslationCovariantEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ K)
    (σ τ : ℝ) (hστ : σ ≤ τ) (v z : PDE.Vec d) :
    K.firstMarginal (wholeSpaceQuery σ τ hστ v z) =
      K.firstMarginal (wholeSpaceQuery σ τ hστ v 0) := by
  let p : EvolutionState (wholeSpace d) (fun _ => 0) σ :=
    ⟨(v, 0), (wholeSpaceQuery σ τ hστ v 0).property.2⟩
  have hq : evolutionQueryOfState (wholeSpace d) (fun _ => 0) σ τ hστ
      (evolutionStateShift (wholeSpace d) (fun _ => 0) σ z p) = wholeSpaceQuery σ τ hστ v z := by
    apply Subtype.ext
    simp only [evolutionQueryOfState, evolutionStateShift, evolutionAmbientStateShift,
      wholeSpaceQuery, p, zero_add]
  have hp : evolutionQueryOfState (wholeSpace d) (fun _ => 0) σ τ hστ p =
      wholeSpaceQuery σ τ hστ v 0 := rfl
  have hmt := master_translation (Ω := wholeSpace d) (γ := fun _ => 0) MeasurableSet.univ K hcov
    σ τ hστ p z
  rw [hq] at hmt
  rw [hp] at hmt
  unfold MovingFiberKernel.firstMarginal
  rw [ProbabilityTheory.Kernel.fst_apply, ProbabilityTheory.Kernel.fst_apply, ← hmt,
    Measure.map_map measurable_fst (measurable_evolutionAmbientStateShift z)]
  rfl

/-- A Green measure is the explicit kernel-product measure. -/
theorem green_eq_compProd {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    (K : MovingFiberKernel Ω γ) (σ₀ : ℝ) (μ : Measure (EvolutionState Ω γ σ₀))
    [IsFiniteMeasure μ] (Γ : Measure (ElapsedTime ⊤ × EvolutionAmbientState d))
    (hΓ : IsGreenMeasure K σ₀ ⊤ μ Γ) :
    Γ = (((μ.prod (elapsedVolume ⊤)).compProd (elapsedKernel K σ₀ ⊤)).map
      (fun q => (q.1.2, q.2))) :=
  (existsUnique_greenMeasure K σ₀ ⊤ (by simp) μ).unique hΓ (compProd_isGreenMeasure K σ₀ ⊤ μ)


/-- A bounded Borel function supported in the slab is integrable against a Green measure. -/
theorem integrable_green_slab {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    (K : MovingFiberKernel Ω γ) (σ₀ : ℝ) (μ : Measure (EvolutionState Ω γ σ₀))
    [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier d)) (hΓ : IsGreenMeasure K σ₀ ⊤ μ Γ)
    {T : ℝ} (hT : 0 < T) (f : GreenCarrier d → ℂ) (hf : Measurable f)
    (hfb : ∀ p, ‖f p‖ ≤ 1) (hsupp : ∀ p, p ∉ slabSet T → f p = 0) : Integrable f Γ := by
  have hfin : Γ (slabSet (d := d) T) < ⊤ :=
    (green_slab_le K σ₀ μ Γ hΓ hT).trans_lt
      (ENNReal.mul_lt_top (measure_lt_top _ _) ENNReal.ofReal_lt_top)
  have hi : Integrable ((slabSet (d := d) T).indicator (fun _ => (1 : ℝ))) Γ :=
    (integrable_indicator_iff (measurableSet_slabSet T)).2 (integrableOn_const hfin.ne)
  refine Integrable.mono' hi hf.aestronglyMeasurable (Filter.Eventually.of_forall (fun p => ?_))
  by_cases hp : p ∈ slabSet T
  · simpa [Set.indicator_of_mem hp] using hfb p
  · simp [hsupp p hp, Set.indicator_of_notMem hp]


/-- **Green integral calculus.**  For bounded complex Borel `f` supported in the slab,
`∫ f dΓ = ∫_τ ∫_μ ∫_{master (σ₀ → σ₀ + τ)} f(τ, ·)`. -/
theorem green_integral {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    (K : MovingFiberKernel Ω γ) (σ₀ : ℝ) (μ : Measure (EvolutionState Ω γ σ₀))
    [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier d)) (hΓ : IsGreenMeasure K σ₀ ⊤ μ Γ)
    {T : ℝ} (hT : 0 < T) (f : GreenCarrier d → ℂ) (hf : Measurable f)
    (hfb : ∀ p, ‖f p‖ ≤ 1) (hsupp : ∀ p, p ∉ slabSet T → f p = 0) :
    ∫ p, f p ∂Γ = ∫ τ, (∫ p, (∫ w, f (τ, w) ∂K.master (elapsedQuery σ₀ p τ)) ∂μ)
      ∂elapsedVolume ⊤ := by
  have hint := integrable_green_slab K σ₀ μ Γ hΓ hT f hf hfb hsupp
  have hι : Measurable (fun q : (EvolutionState Ω γ σ₀ × ElapsedTime ⊤) × EvolutionAmbientState d =>
      (q.1.2, q.2)) := by fun_prop
  set Ξ := (μ.prod (elapsedVolume ⊤)).compProd (elapsedKernel K σ₀ ⊤) with hΞ
  have hΓeq := green_eq_compProd K σ₀ μ Γ hΓ
  rw [hΓeq] at hint ⊢
  rw [integral_map hι.aemeasurable hf.aestronglyMeasurable]
  have hint' : Integrable (fun q : (EvolutionState Ω γ σ₀ × ElapsedTime ⊤) ×
      EvolutionAmbientState d => f (q.1.2, q.2)) Ξ :=
    (integrable_map_measure hf.aestronglyMeasurable hι.aemeasurable).1 hint
  have hfk : ProbabilityTheory.IsFiniteKernel (elapsedKernel K σ₀ ⊤) := by
    unfold elapsedKernel; infer_instance
  rw [Measure.integral_compProd hint']
  -- inner function on the product of source states and elapsed times
  set G : EvolutionState Ω γ σ₀ × ElapsedTime ⊤ → ℂ :=
    fun a => ∫ w, f (a.2, w) ∂elapsedKernel K σ₀ ⊤ a with hG
  have hGm : StronglyMeasurable G := by
    have h1 : StronglyMeasurable (fun q : (EvolutionState Ω γ σ₀ × ElapsedTime ⊤) ×
        EvolutionAmbientState d => f (q.1.2, q.2)) := (hf.comp hι).stronglyMeasurable
    exact h1.integral_kernel_prod_right' (κ := elapsedKernel K σ₀ ⊤)
  have hGb : ∀ a, ‖G a‖ ≤ (slabTimeSet T).indicator (fun _ => (1 : ℝ)) a.2 := by
    intro a
    by_cases ha : a.2 ∈ slabTimeSet T
    · rw [Set.indicator_of_mem ha]
      calc ‖G a‖ ≤ ∫ w, ‖f (a.2, w)‖ ∂elapsedKernel K σ₀ ⊤ a := norm_integral_le_integral_norm _
        _ ≤ ∫ w, (1 : ℝ) ∂elapsedKernel K σ₀ ⊤ a :=
            integral_mono_of_nonneg (Filter.Eventually.of_forall (fun w => norm_nonneg _))
              (integrable_const _) (Filter.Eventually.of_forall (fun w => hfb _))
        _ ≤ 1 := by
            have : elapsedKernel K σ₀ ⊤ a univ ≤ 1 := K.mass_le_one _
            simp only [integral_const, smul_eq_mul, mul_one, measureReal_def]
            exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
    · rw [Set.indicator_of_notMem ha]
      have : ∀ w, f (a.2, w) = 0 := fun w => hsupp _ (fun h => ha h)
      simp [hG, this]
  have hGi : Integrable G (μ.prod (elapsedVolume ⊤)) := by
    have hfinT : (μ.prod (elapsedVolume ⊤)) (univ ×ˢ slabTimeSet T) < ⊤ := by
      rw [Measure.prod_prod, elapsedVolume_slabTimeSet hT]
      exact ENNReal.mul_lt_top (measure_lt_top _ _) ENNReal.ofReal_lt_top
    have hi : Integrable (fun a : EvolutionState Ω γ σ₀ × ElapsedTime ⊤ =>
        (slabTimeSet T).indicator (fun _ => (1 : ℝ)) a.2) (μ.prod (elapsedVolume ⊤)) := by
      have : (fun a : EvolutionState Ω γ σ₀ × ElapsedTime ⊤ =>
          (slabTimeSet T).indicator (fun _ => (1 : ℝ)) a.2) =
          (univ ×ˢ slabTimeSet T : Set _).indicator (fun _ => (1 : ℝ)) := by
        funext a; by_cases ha : a.2 ∈ slabTimeSet T <;> simp [Set.indicator, ha]
      rw [this]
      exact (integrable_indicator_iff (MeasurableSet.univ.prod (measurableSet_slabTimeSet T))).2
        (integrableOn_const hfinT.ne)
    exact Integrable.mono' hi hGm.aestronglyMeasurable (Filter.Eventually.of_forall hGb)
  rw [integral_prod_symm G hGi]
  rfl

end HypoellipticAleksandrov.KineticAleksandrov.Green
