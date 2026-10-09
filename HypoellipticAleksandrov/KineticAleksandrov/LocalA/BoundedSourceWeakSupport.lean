module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceWeakMeasure

/-! # Support of the weak source-action measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set
open scoped ENNReal ProbabilityTheory
variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- The past moving cylinder in product coordinates used by the source-action measure. -/
def boundedSourcePast (Ω : Set (PDE.Vec d)) (γ : ℝ → PDE.Vec d) (T : ℝ) :
    Set (ℝ × EvolutionAmbientState d) :=
  {q | q.1 < T ∧ q.2.1 ∈ movingDomain Ω γ q.1}

/-- The source past set is Borel. -/
theorem measurableSet_boundedSourcePast (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (T : ℝ) : MeasurableSet (boundedSourcePast Ω γ T) := by
  have ht : MeasurableSet {q : ℝ × EvolutionAmbientState d | q.1 < T} :=
    measurableSet_lt measurable_fst measurable_const
  have hp : MeasurableSet {q : ℝ × EvolutionAmbientState d | q.2.1 - γ q.1 ∈ Ω} :=
    hΩ.preimage (measurable_snd.fst.sub (hγ.measurable.comp measurable_fst))
  convert ht.inter hp using 1
  ext q
  simp only [boundedSourcePast, mem_ofPred_eq, mem_inter_iff, movingDomain,
    PDE.mem_translateSet_iff_sub_mem]

/-- An open moving domain gives an open past cylinder in product coordinates. -/
theorem isOpen_boundedSourcePast (hΩ : IsOpen Ω) (hγ : Continuous γ) (T : ℝ) :
    IsOpen (boundedSourcePast Ω γ T) := by
  have ht : IsOpen {q : ℝ × EvolutionAmbientState d | q.1 < T} :=
    isOpen_lt continuous_fst continuous_const
  have hp : IsOpen {q : ℝ × EvolutionAmbientState d | q.2.1 - γ q.1 ∈ Ω} :=
    hΩ.preimage (continuous_snd.fst.sub (hγ.comp continuous_fst))
  convert ht.inter hp using 1
  ext q
  simp only [boundedSourcePast, mem_ofPred_eq, mem_inter_iff, movingDomain,
    PDE.mem_translateSet_iff_sub_mem]

/-- The source-action measure retains the terminal support of the master kernel. -/
theorem boundedSourceActionMeasure_compl_past (K : MovingFiberKernel Ω γ)
    (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (ν : Measure (KineticPoint d)) [IsFiniteMeasure ν] (a T : ℝ) :
    boundedSourceActionMeasure K ν a T (boundedSourcePast Ω γ T)ᶜ = 0 := by
  let ρ := ν.prod (volume.restrict (Ioo a T))
  let η := ρ.comap ((↑) : BoundedSourcePair Ω γ → KineticPoint d × ℝ)
  let κ := boundedSourcePairKernel K
  have : ProbabilityTheory.IsFiniteKernel κ := by
    dsimp only [κ, boundedSourcePairKernel]
    infer_instance
  have hD := measurableSet_boundedSourcePairSet hΩ hγ
  have hU := measurableSet_boundedSourcePast hΩ hγ T
  have hr : ∀ᵐ q ∂ρ, q.2 ∈ Ioo a T :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_Ioo.preimage measurable_snd)).2
      (Filter.Eventually.of_forall fun _ => ae_restrict_mem measurableSet_Ioo)
  have hrη : ∀ᵐ q ∂η, q.1.2 ∈ Ioo a T := by
    have hmapped : ∀ᵐ q ∂Measure.map Subtype.val η, q.2 ∈ Ioo a T := by
      dsimp only [η]
      rw [map_comap_subtype_coe hD]
      exact ae_restrict_of_ae hr
    exact ae_of_ae_map (p := fun q : KineticPoint d × ℝ => q.2 ∈ Ioo a T)
      measurable_subtype_coe.aemeasurable hmapped
  have houtput : ∀ᵐ q ∂η.compProd κ,
      boundedSourceOutput q ∈ boundedSourcePast Ω γ T := by
    apply (Measure.ae_compProd_iff (hU.preimage measurable_boundedSourceOutput)).2
    filter_upwards [hrη] with q hq
    have hstate : ∀ᵐ w ∂κ q,
        w ∈ evolutionStateSet Ω γ q.1.2 := by
      change ∀ᵐ w ∂K.master (boundedSourcePairQuery q),
        w ∈ evolutionStateSet Ω γ q.1.2
      rw [← K.terminal_support (boundedSourcePairQuery q)]
      exact ae_restrict_mem (measurableSet_evolutionStateSet hΩ _)
    filter_upwards [hstate] with w hw
    exact ⟨hq.2, hw.1⟩
  change (Measure.map boundedSourceOutput (η.compProd κ)) _ = 0
  rw [measure_eq_zero_iff_ae_notMem]
  simpa only [Set.mem_compl_iff, not_not] using
    (ae_map_iff (p := fun q => q ∈ boundedSourcePast Ω γ T)
      measurable_boundedSourceOutput.aemeasurable hU).2 houtput

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
