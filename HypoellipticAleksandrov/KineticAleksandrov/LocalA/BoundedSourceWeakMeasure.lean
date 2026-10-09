module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceApprox
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Prod

/-! # Source measures for bounded-source weak testing

A finite measure of starting points and a finite source-time window are transported
through the valid-query master kernel. This is a literal composition-product measure;
no distributional identity is postulated in its definition.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set
open scoped ENNReal ProbabilityTheory
variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- Starting-point/source-time pairs on which the existing master query is valid. -/
def boundedSourcePairSet (Ω : Set (PDE.Vec d)) (γ : ℝ → PDE.Vec d) :
    Set (KineticPoint d × ℝ) :=
  {q | q.1.time ≤ q.2 ∧ q.1.position ∈ movingDomain Ω γ q.1.time}

/-- The valid-pair carrier excludes invalid kernel queries. -/
abbrev BoundedSourcePair (Ω : Set (PDE.Vec d)) (γ : ℝ → PDE.Vec d) :=
  {q : KineticPoint d × ℝ // q ∈ boundedSourcePairSet Ω γ}

/-- The valid pair set is Borel. -/
theorem measurableSet_boundedSourcePairSet (hΩ : MeasurableSet Ω) (hγ : Continuous γ) :
    MeasurableSet (boundedSourcePairSet Ω γ) := by
  have ht : MeasurableSet {q : KineticPoint d × ℝ | q.1.time ≤ q.2} :=
    measurableSet_le (continuous_time.measurable.comp measurable_fst) measurable_snd
  have hp : MeasurableSet {q : KineticPoint d × ℝ | q.1.position - γ q.1.time ∈ Ω} :=
    hΩ.preimage ((continuous_position.measurable.comp measurable_fst).sub
      (hγ.measurable.comp (continuous_time.measurable.comp measurable_fst)))
  convert ht.inter hp using 1
  ext q
  simp only [boundedSourcePairSet, mem_ofPred_eq, mem_inter_iff, movingDomain,
    PDE.mem_translateSet_iff_sub_mem]

/-- Turn a valid starting-point/source-time pair into the existing query carrier. -/
def boundedSourcePairQuery (q : BoundedSourcePair Ω γ) : EvolutionQuery Ω γ :=
  ⟨(q.1.1.time, (q.1.2, (q.1.1.position, q.1.1.velocity))), q.2.1, q.2.2, mem_univ _⟩

/-- The query conversion is jointly measurable in starting point and source time. -/
theorem measurable_boundedSourcePairQuery : Measurable (@boundedSourcePairQuery d Ω γ) := by
  apply Measurable.subtype_mk
  exact (continuous_time.measurable.comp measurable_subtype_coe.fst).prodMk
    (measurable_subtype_coe.snd.prodMk
      ((continuous_position.measurable.comp measurable_subtype_coe.fst).prodMk
        (continuous_velocity.measurable.comp measurable_subtype_coe.fst)))

/-- The master kernel pulled back to valid starting-point/source-time pairs. -/
def boundedSourcePairKernel (K : MovingFiberKernel Ω γ) :
    ProbabilityTheory.Kernel (BoundedSourcePair Ω γ) (EvolutionAmbientState d) :=
  K.master.comap boundedSourcePairQuery measurable_boundedSourcePairQuery

/-- The joint source output is packed in (time, diffused, transported) coordinate order. -/
def boundedSourceOutput (q : BoundedSourcePair Ω γ × EvolutionAmbientState d) :
    ℝ × EvolutionAmbientState d := (q.1.1.2, q.2)

/-- Packing source output is measurable. -/
theorem measurable_boundedSourceOutput : Measurable (@boundedSourceOutput d Ω γ) :=
  (measurable_subtype_coe.snd.comp measurable_fst).prodMk measurable_snd

/-- Positive starting mass transported through the Duhamel source-time kernel. -/
def boundedSourceActionMeasure (K : MovingFiberKernel Ω γ)
    (ν : Measure (KineticPoint d)) (a T : ℝ) : Measure (ℝ × EvolutionAmbientState d) :=
  (((ν.prod (volume.restrict (Ioo a T))).comap
    ((↑) : BoundedSourcePair Ω γ → KineticPoint d × ℝ)).compProd
      (boundedSourcePairKernel K)).map boundedSourceOutput

/-- A finite starting measure and finite time window produce a finite source measure. -/
instance boundedSourceActionMeasure_isFinite (K : MovingFiberKernel Ω γ)
    (ν : Measure (KineticPoint d)) [IsFiniteMeasure ν] (a T : ℝ) :
    IsFiniteMeasure (boundedSourceActionMeasure K ν a T) := by
  have : ProbabilityTheory.IsFiniteKernel (boundedSourcePairKernel K) := by
    unfold boundedSourcePairKernel
    infer_instance
  unfold boundedSourceActionMeasure
  infer_instance

/-- A bounded real Borel function is integrable against a finite measure. -/
theorem integrable_bounded_real {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (f : E → ℝ) (hf : Measurable f)
    (M : ℝ) (hb : ∀ x, |f x| ≤ M) : Integrable f μ := by
  refine ⟨hf.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := M) ?_⟩
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]
    exact hb x

/-- The source-action measure reproduces the jointly measurable Duhamel integral. -/
theorem integral_boundedSourceActionMeasure (K : MovingFiberKernel Ω γ)
    (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (ν : Measure (KineticPoint d)) [IsFiniteMeasure ν] (a T : ℝ)
    (g : KineticPoint d → ℝ) (hg : Measurable g)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ p, |g p| ≤ M) :
    (∫ q, g ⟨q.1, q.2.1, q.2.2⟩ ∂boundedSourceActionMeasure K ν a T) =
      ∫ p, (∫ r in Ioo a T, duhamelIntegrand K g p r) ∂ν := by
  let ρ := ν.prod (volume.restrict (Ioo a T))
  let η := ρ.comap ((↑) : BoundedSourcePair Ω γ → KineticPoint d × ℝ)
  let κ := boundedSourcePairKernel K
  have : ProbabilityTheory.IsFiniteKernel κ := by
    dsimp only [κ, boundedSourcePairKernel]
    infer_instance
  let f : ℝ × EvolutionAmbientState d → ℝ := fun q => g ⟨q.1, q.2.1, q.2.2⟩
  have hf : Measurable f :=
    hg.comp ((KineticPoint.measurable_equivProd_symm d).comp
      (measurable_fst.prodMk (measurable_snd.fst.prodMk measurable_snd.snd)))
  have hF : Integrable (f ∘ boundedSourceOutput) (η.compProd κ) :=
    integrable_bounded_real _ _ (hf.comp measurable_boundedSourceOutput) M (fun q => hb _)
  have hm := measurable_duhamelIntegrand K hΩ hγ g hg
  have hi : Integrable (fun q : KineticPoint d × ℝ => duhamelIntegrand K g q.1 q.2) ρ :=
    integrable_bounded_real _ _ hm M
      (fun q => abs_duhamelIntegrand_le K g M hM hb q.1 q.2)
  have hD := measurableSet_boundedSourcePairSet hΩ hγ
  have hcoe : (fun q : BoundedSourcePair Ω γ =>
      ∫ w, f (boundedSourceOutput (q,w)) ∂κ q) =
      fun q => duhamelIntegrand K g q.1.1 q.1.2 := by
    funext q
    dsimp only [κ, boundedSourcePairKernel, ProbabilityTheory.Kernel.comap_apply,
      f, boundedSourceOutput, boundedSourcePairQuery]
    unfold duhamelIntegrand
    have hq : q.1.1.time ≤ q.1.2 ∧
        q.1.1.position ∈ movingDomain Ω γ q.1.1.time := q.2
    rw [dite_eq_left hq]
    rfl
  have hind : (boundedSourcePairSet Ω γ).indicator
      (fun q : KineticPoint d × ℝ => duhamelIntegrand K g q.1 q.2) =
      fun q => duhamelIntegrand K g q.1 q.2 := by
    funext q
    by_cases hq : q ∈ boundedSourcePairSet Ω γ
    · exact indicator_of_mem hq _
    · rw [indicator_of_notMem hq]
      unfold duhamelIntegrand
      change ¬(q.1.time ≤ q.2 ∧ q.1.position ∈ movingDomain Ω γ q.1.time) at hq
      rw [dite_eq_right hq]
  change (∫ q, f q ∂(η.compProd κ).map boundedSourceOutput) = _
  rw [integral_map measurable_boundedSourceOutput.aemeasurable hf.aestronglyMeasurable]
  change (∫ q, (f ∘ boundedSourceOutput) q ∂η.compProd κ) = _
  rw [Measure.integral_compProd hF]
  simp only [Function.comp_apply]
  rw [hcoe]
  have hsub := integral_subtype_comap (μ := ρ) hD
    (fun q : KineticPoint d × ℝ => duhamelIntegrand K g q.1 q.2)
  rw [hsub, ← integral_indicator hD, hind]
  exact integral_prod _ hi

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
