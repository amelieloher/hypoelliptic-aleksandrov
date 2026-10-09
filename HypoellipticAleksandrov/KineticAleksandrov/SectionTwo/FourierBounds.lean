module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Fourier
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

/-! # Variation and support of Fourier projection -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

/-- Variation is dominated by the source velocity marginal. -/
theorem fourierProjection_variation_le {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ)
    (q : EvolutionQuery Ω γ) (ξ : PDE.Vec d)
    (ν : ComplexMeasure (PDE.Vec d)) (hν : IsFourierProjection K q ξ ν) :
    ν.variation ≤ K.firstMarginal q := by
  rw [fourierProjection_eq_densityMap K q ξ ν hν]
  calc
    _ ≤ (((K.master q).withDensityᵥ (fourierPhase ξ q.1.2.2.2)).variation).map Prod.fst :=
      VectorMeasure.variation_map_le
    _ = (K.master q).map Prod.fst := by
      rw [Measure.variation_withDensityᵥ (fourierPhase_integrable K q ξ _)]
      have hphase : (fun w => ‖fourierPhase ξ q.1.2.2.2 w‖ₑ) = 1 := by
        funext w
        rw [← ofReal_norm, norm_fourierPhase]
        norm_num
      rw [hphase, withDensity_one]
    _ = K.firstMarginal q := by
      rw [MovingFiberKernel.firstMarginal, ProbabilityTheory.Kernel.fst_apply]

/-- Total variation on the whole carrier, before any conversion to real. -/
abbrev totalVariationNorm {d : ℕ} (ν : ComplexMeasure (PDE.Vec d)) : ℝ≥0∞ :=
  ν.variation Set.univ

/-- The projected measure has total variation at most one. -/
theorem fourierProjection_totalVariation_le_one {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ)
    (q : EvolutionQuery Ω γ) (ξ : PDE.Vec d)
    (ν : ComplexMeasure (PDE.Vec d)) (hν : IsFourierProjection K q ξ ν) :
    totalVariationNorm ν ≤ 1 := by
  apply (Measure.le_iff.1 (fourierProjection_variation_le K q ξ ν hν) univ
    MeasurableSet.univ).trans
  rw [MovingFiberKernel.firstMarginal, ProbabilityTheory.Kernel.fst_apply,
    Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ]
  exact K.mass_le_one q

/-- Ambient Fourier measures vanish off the actual terminal diffused fiber. -/
theorem fourierProjection_support {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (hΩ : MeasurableSet Ω) (K : MovingFiberKernel Ω γ)
    (q : EvolutionQuery Ω γ) (ξ : PDE.Vec d) (ν : ComplexMeasure (PDE.Vec d))
    (hν : IsFourierProjection K q ξ ν) (E : Set (PDE.Vec d)) (hE : MeasurableSet E) :
    ν E = ν (E ∩ movingDomain Ω γ q.1.2.1) := by
  have hD := measurableSet_movingDomain (γ := γ) hΩ q.1.2.1
  rw [hν E hE, hν (E ∩ movingDomain Ω γ q.1.2.1) (hE.inter hD)]
  have hmem : ∀ᵐ w ∂K.master q, w ∈ evolutionStateSet Ω γ q.1.2.1 := by
    rw [← K.terminal_support q]
    exact ae_restrict_mem (measurableSet_evolutionStateSet hΩ q.1.2.1)
  apply setIntegral_congr_set
  filter_upwards [hmem] with w hw
  simp only [mem_prod, mem_inter_iff, mem_univ, and_true]
  apply propext
  exact ⟨fun h => ⟨h, hw.1⟩, fun h => h.1⟩


/-- The supported ambient Fourier measure has exactly one terminal-subtype lift. -/
theorem existsUnique_fourierProjection_subtype {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (hΩ : MeasurableSet Ω) (K : MovingFiberKernel Ω γ)
    (q : EvolutionQuery Ω γ) (ξ : PDE.Vec d) (ν : ComplexMeasure (PDE.Vec d))
    (hν : IsFourierProjection K q ξ ν) :
    ∃! νfiber : ComplexMeasure (EvolutionPosition Ω γ q.1.2.1),
      νfiber.map Subtype.val = ν := by
  let D := movingDomain Ω γ q.1.2.1
  have hD : MeasurableSet D := measurableSet_movingDomain (γ := γ) hΩ q.1.2.1
  let e := MeasurableEmbedding.subtype_coe hD
  let νfiber : ComplexMeasure (EvolutionPosition Ω γ q.1.2.1) :=
    { measureOf' := fun E => ν (Subtype.val '' E)
      empty' := by simp only [image_empty, VectorMeasure.empty]
      not_measurable' := fun E hE => ν.not_measurable (fun h => hE (e.measurableSet_image.mp h))
      m_iUnion' := fun E hE hd => by
        simpa only [image_iUnion] using ν.m_iUnion
          (fun i => e.measurableSet_image.mpr (hE i))
          (fun i j hij => Set.disjoint_image_of_injective e.injective (hd hij)) }
  have hmap : νfiber.map Subtype.val = ν := by
    apply VectorMeasure.ext
    intro E hE
    rw [VectorMeasure.map_apply _ measurable_subtype_coe hE]
    change ν (Subtype.val '' (Subtype.val ⁻¹' E)) = ν E
    rw [image_preimage_eq_inter_range, Subtype.range_coe]
    exact (fourierProjection_support hΩ K q ξ ν hν E hE).symm
  refine ⟨νfiber, hmap, ?_⟩
  intro ν' hν'
  apply VectorMeasure.ext
  intro E hE
  have hh := congrArg (fun v : ComplexMeasure (PDE.Vec d) => v (Subtype.val '' E)) hν'
  rw [VectorMeasure.map_apply _ measurable_subtype_coe (e.measurableSet_image.mpr hE),
    e.injective.preimage_image] at hh
  exact hh


/-- The zero frequency is the positive velocity marginal. -/
theorem fourierProjection_zero {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ)
    (q : EvolutionQuery Ω γ) (ν : ComplexMeasure (PDE.Vec d))
    (hν : IsFourierProjection K q 0 ν) (E : Set (PDE.Vec d))
    (hE : MeasurableSet E) : ν E = ((K.firstMarginal q E).toReal : ℂ) := by
  have hz : fourierPhase (0 : PDE.Vec d) q.1.2.2.2 = fun _ => (1 : ℂ) := by
    funext w
    simp only [fourierPhase, PDE.vecDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
      Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [hν E hE, hz]
  change _ = (((Measure.map Prod.fst (K.master q)) E).toReal : ℂ)
  rw [Measure.map_apply measurable_fst hE]
  have hset : (Prod.fst : EvolutionAmbientState d → PDE.Vec d) ⁻¹' E = E ×ˢ univ := by
    ext w
    simp only [mem_preimage, mem_prod, mem_univ, and_true]
  rw [hset]
  simp only [setIntegral_const, measureReal_def, Complex.real_smul, mul_one]

/-- A full zero-mode equality usable for vector-measure rewriting. -/
theorem fourierProjection_zero_measure {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ) (q : EvolutionQuery Ω γ)
    (ν : ComplexMeasure (PDE.Vec d)) (hν : IsFourierProjection K q 0 ν) :
    ν = (K.firstMarginal q).withDensityᵥ (fun _ => (1 : ℂ)) := by
  have hm : IsFiniteMeasure (K.firstMarginal q) := by
    change IsFiniteMeasure ((K.master q).map Prod.fst)
    infer_instance
  apply VectorMeasure.ext
  intro E hE
  rw [fourierProjection_zero K q ν hν E hE, withDensityᵥ_apply (integrable_const (1 : ℂ)) hE]
  simp only [setIntegral_const, measureReal_def, Complex.real_smul, mul_one]



end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
