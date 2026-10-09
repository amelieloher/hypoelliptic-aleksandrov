module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Elapsed
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-! # Green measures from measurable kernel integration -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

/-- Source Green action, with elapsed time and (v,z) kept in that order. -/
def IsGreenMeasure {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    (K : MovingFiberKernel Ω γ) (σ₀ : ℝ) (S : ℝ≥0∞)
    (μ : Measure (EvolutionState Ω γ σ₀))
    (Γ : Measure (ElapsedTime S × EvolutionAmbientState d)) : Prop :=
  ∀ F : ElapsedTime S × EvolutionAmbientState d → ℝ≥0∞, Measurable F →
    (∫⁻ q, F q ∂Γ) =
      ∫⁻ p, ∫⁻ τ, ∫⁻ w, F (τ, w) ∂K.master (elapsedQuery σ₀ p τ)
        ∂elapsedVolume S ∂μ


/-- The master kernel is finite by its existing uniform mass bound. -/
instance master_isFiniteKernel {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    (K : MovingFiberKernel Ω γ) : ProbabilityTheory.IsFiniteKernel K.master :=
  ⟨1, ENNReal.one_lt_top, K.mass_le_one⟩

/-- The elapsed-query map is measurable on the fixed source fiber. -/
theorem measurable_elapsedQuery {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    (σ₀ : ℝ) (S : ℝ≥0∞) :
    Measurable (fun q : EvolutionState Ω γ σ₀ × ElapsedTime S => elapsedQuery σ₀ q.1 q.2) := by
  apply Measurable.subtype_mk
  change Measurable (fun q : EvolutionState Ω γ σ₀ × ElapsedTime S =>
    (σ₀, (σ₀ + q.2.1, q.1.1)))
  fun_prop

/-- The literal master-kernel pullback at elapsed queries. -/
def elapsedKernel {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    (K : MovingFiberKernel Ω γ) (σ₀ : ℝ) (S : ℝ≥0∞) :
    ProbabilityTheory.Kernel (EvolutionState Ω γ σ₀ × ElapsedTime S)
      (EvolutionAmbientState d) :=
  K.master.comap (fun q => elapsedQuery σ₀ q.1 q.2) (measurable_elapsedQuery σ₀ S)

/-- The explicit product-kernel measure satisfies the Green characterization. -/
theorem compProd_isGreenMeasure {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    (K : MovingFiberKernel Ω γ) (σ₀ : ℝ) (S : ℝ≥0∞)
    (μ : Measure (EvolutionState Ω γ σ₀)) [IsFiniteMeasure μ] :
    IsGreenMeasure K σ₀ S μ
      (((μ.prod (elapsedVolume S)).compProd (elapsedKernel K σ₀ S)).map
        (fun q => (q.1.2, q.2))) := by
  intro F hF
  have hm : Measurable (fun q : (EvolutionState Ω γ σ₀ × ElapsedTime S) ×
      EvolutionAmbientState d => (q.1.2, q.2)) := by fun_prop
  have : ProbabilityTheory.IsFiniteKernel (elapsedKernel K σ₀ S) := by
    unfold elapsedKernel
    infer_instance
  rw [lintegral_map hF hm]
  calc
    _ = ∫⁻ a, ∫⁻ w, F (a.2, w) ∂elapsedKernel K σ₀ S a
        ∂μ.prod (elapsedVolume S) :=
      Measure.lintegral_compProd (μ := μ.prod (elapsedVolume S))
        (κ := elapsedKernel K σ₀ S) (hF.comp hm)
    _ = _ := by
      exact lintegral_prod _
        ((hF.comp hm).lintegral_kernel_prod_right'.aemeasurable)

/-- Unique Green measure for a finite source measure and positive horizon. -/
theorem existsUnique_greenMeasure {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ)
    (σ₀ : ℝ) (S : ℝ≥0∞) (hS : 0 < S)
    (μ : Measure (EvolutionState Ω γ σ₀)) [IsFiniteMeasure μ] :
    ∃! Γ : Measure (ElapsedTime S × EvolutionAmbientState d),
      IsGreenMeasure K σ₀ S μ Γ := by
  refine ⟨_, compProd_isGreenMeasure K σ₀ S μ, ?_⟩
  intro Γ hΓ
  apply Measure.ext_of_lintegral
  intro F hF
  exact (hΓ F hF).trans ((compProd_isGreenMeasure K σ₀ S μ F hF).symm)


/-- Green measure chosen only from the proved existence and uniqueness theorem. -/
def greenMeasure {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    (K : MovingFiberKernel Ω γ) (σ₀ : ℝ) (S : ℝ≥0∞) (hS : 0 < S)
    (μ : Measure (EvolutionState Ω γ σ₀)) [IsFiniteMeasure μ] :
    Measure (ElapsedTime S × EvolutionAmbientState d) :=
  (existsUnique_greenMeasure K σ₀ S hS μ).exists.choose

/-- The defining Green action accompanies the unique-choice measure. -/
theorem greenMeasure_spec {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    (K : MovingFiberKernel Ω γ) (σ₀ : ℝ) (S : ℝ≥0∞) (hS : 0 < S)
    (μ : Measure (EvolutionState Ω γ σ₀)) [IsFiniteMeasure μ] :
    IsGreenMeasure K σ₀ S μ (greenMeasure K σ₀ S hS μ) :=
  (existsUnique_greenMeasure K σ₀ S hS μ).exists.choose_spec

/-- Set-wise Green mass controls slabs and infinite-horizon local mass. -/
theorem greenMeasure_timeMarginal_le {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ) (σ₀ : ℝ) (S : ℝ≥0∞)
    (μ : Measure (EvolutionState Ω γ σ₀)) [IsFiniteMeasure μ]
    (Γ : Measure (ElapsedTime S × EvolutionAmbientState d))
    (hΓ : IsGreenMeasure K σ₀ S μ Γ) (A : Set (ElapsedTime S))
    (hA : MeasurableSet A) : Γ (Prod.fst ⁻¹' A) ≤ μ univ * elapsedVolume S A := by
  have hpre : MeasurableSet ((Prod.fst : ElapsedTime S × EvolutionAmbientState d →
      ElapsedTime S) ⁻¹' A) := measurable_fst hA
  rw [← lintegral_indicator_one hpre]
  rw [hΓ ((Prod.fst ⁻¹' A).indicator 1) (measurable_one.indicator hpre)]
  calc
    _ ≤ ∫⁻ p, ∫⁻ τ, A.indicator (fun _ => (1 : ℝ≥0∞)) τ ∂elapsedVolume S ∂μ := by
      apply lintegral_mono
      intro p
      apply lintegral_mono
      intro τ
      by_cases ht : τ ∈ A
      · simp only [Set.indicator_of_mem ht]
        simpa only [Set.indicator, mem_preimage, ht, ↓reduceIte, Pi.one_apply,
          lintegral_one] using K.mass_le_one (elapsedQuery σ₀ p τ)
      · simp only [Set.indicator, mem_preimage, ht, ↓reduceIte, lintegral_zero, le_refl]
    _ = μ univ * elapsedVolume S A := by
      have he : (∫⁻ τ, A.indicator (fun _ => (1 : ℝ≥0∞)) τ ∂elapsedVolume S) =
          elapsedVolume S A := lintegral_indicator_one hA
      rw [he, lintegral_const]
      exact mul_comm _ _


/-- Restricting the horizon commutes with the Green action, without renormalization. -/
theorem greenMeasure_horizonRestriction {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ) (σ₀ : ℝ)
    (T S : ℝ≥0∞) (hTS : T ≤ S)
    (μ : Measure (EvolutionState Ω γ σ₀)) [IsFiniteMeasure μ]
    (ΓT : Measure (ElapsedTime T × EvolutionAmbientState d))
    (ΓS : Measure (ElapsedTime S × EvolutionAmbientState d))
    (hT : IsGreenMeasure K σ₀ T μ ΓT) (hS : IsGreenMeasure K σ₀ S μ ΓS) :
    ΓT.map (fun q => (elapsedInclusion hTS q.1, q.2)) =
      ΓS.restrict {q | ENNReal.ofReal q.1.1 < T} := by
  apply Measure.ext_of_lintegral
  intro F hF
  have hmap : Measurable (fun q : ElapsedTime T × EvolutionAmbientState d =>
      (elapsedInclusion hTS q.1, q.2)) :=
    ((measurable_elapsedInclusion hTS).comp measurable_fst).prodMk measurable_snd
  have htime : MeasurableSet {τ : ElapsedTime S | ENNReal.ofReal τ.1 < T} :=
    (ENNReal.measurable_ofReal.comp measurable_subtype_coe) measurableSet_Iio
  have hset : MeasurableSet {q : ElapsedTime S × EvolutionAmbientState d |
      ENNReal.ofReal q.1.1 < T} := htime.preimage measurable_fst
  rw [lintegral_map hF hmap, ← lintegral_indicator hset]
  rw [hS _ (hF.indicator hset)]
  calc
    _ = ∫⁻ p, ∫⁻ τ, ∫⁻ w, F (elapsedInclusion hTS τ, w)
        ∂K.master (elapsedQuery σ₀ p τ) ∂elapsedVolume T ∂μ := hT _ (hF.comp hmap)
    _ = ∫⁻ p, ∫⁻ τ in {τ : ElapsedTime S | ENNReal.ofReal τ.1 < T},
        ∫⁻ w, F (τ, w) ∂K.master (elapsedQuery σ₀ p τ) ∂elapsedVolume S ∂μ := by
      apply lintegral_congr
      intro p
      have Hm : Measurable (fun τ : ElapsedTime S =>
          ∫⁻ w, F (τ, w) ∂K.master (elapsedQuery σ₀ p τ)) := by
        have hm : Measurable (fun q : (EvolutionState Ω γ σ₀ × ElapsedTime S) ×
            EvolutionAmbientState d => F (q.1.2, q.2)) :=
          hF.comp (measurable_fst.snd.prodMk measurable_snd)
        have : ProbabilityTheory.IsFiniteKernel (elapsedKernel K σ₀ S) := by
          unfold elapsedKernel
          infer_instance
        exact (hm.lintegral_kernel_prod_right' (κ := elapsedKernel K σ₀ S)).comp
          (measurable_const.prodMk measurable_id)
      rw [← elapsedInclusion_map hTS, lintegral_map Hm (measurable_elapsedInclusion hTS)]
      rfl
    _ = _ := by
      apply lintegral_congr
      intro p
      rw [← lintegral_indicator htime]
      apply lintegral_congr
      intro τ
      by_cases ht : ENNReal.ofReal τ.1 < T
      · simp only [Set.indicator, mem_ofPred_eq, ht, ↓reduceIte]
      · simp only [Set.indicator, mem_ofPred_eq, ht, ↓reduceIte, lintegral_zero]


/-- Finite-horizon mass bound uses the initial mass and the unnormalized time length. -/
theorem greenMeasure_mass_le {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ)
    (σ₀ S : ℝ) (hS : 0 < S)
    (μ : Measure (EvolutionState Ω γ σ₀)) [IsFiniteMeasure μ]
    (Γ : Measure (ElapsedTime (ENNReal.ofReal S) × EvolutionAmbientState d))
    (hΓ : IsGreenMeasure K σ₀ (ENNReal.ofReal S) μ Γ) :
    Γ Set.univ ≤ μ Set.univ * ENNReal.ofReal S := by
  simpa only [preimage_univ, elapsedVolume_univ S hS] using
    greenMeasure_timeMarginal_le K σ₀ (ENNReal.ofReal S) μ Γ hΓ univ MeasurableSet.univ


end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
