module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.FourierKernels
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

/-! # Fourier contraction for the positive full-minus-killed defect

The defect is the literal positive difference of the ambient terminal measures.
Its Fourier variation is at most its mass because the displacement phase has modulus one.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo
open scoped ENNReal

/-- Fourier variation of a smaller terminal measure is bounded by full Fourier
variation plus the lost mass. Query coordinates, including the physical position,
are retained exactly. -/
theorem killedFourier_variation_le_full_add_loss {d : ℕ}
    {D D' : Set (PDE.Vec d)} {γ γ' : ℝ → PDE.Vec d}
    (Kb : MovingFiberKernel D γ) (Kf : MovingFiberKernel D' γ')
    (qb : EvolutionQuery D γ) (qf : EvolutionQuery D' γ')
    (hq : qb.1 = qf.1) (hdom : Kb.master qb ≤ Kf.master qf) (ξ : PDE.Vec d) :
    ((fourierProjection Kb qb ξ).variation univ).toReal ≤
      ((fourierProjection Kf qf ξ).variation univ).toReal + 1 -
        (Kb.master qb).real univ := by
  let μ := Kf.master qf
  let ν := Kb.master qb
  let ρ := μ - ν
  let φ := fourierPhase ξ qb.1.2.2.2
  let η := (ρ.withDensityᵥ φ).map Prod.fst
  have hρ : Integrable φ ρ :=
    Integrable.mono' (integrable_const (1 : ℝ))
      (continuous_fourierPhase ξ _).measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun w => (norm_fourierPhase ξ _ w).le))
  have hν := fourierPhase_integrable Kb qb ξ qb.1.2.2.2
  have hμ := fourierPhase_integrable Kf qf ξ qb.1.2.2.2
  have hsplit : ρ + ν = μ := Measure.sub_add_cancel_of_le hdom
  have hdensity : μ.withDensityᵥ φ = ρ.withDensityᵥ φ + ν.withDensityᵥ φ := by
    apply VectorMeasure.ext
    intro E hE
    rw [withDensityᵥ_apply hμ hE, _root_.add_apply,
      withDensityᵥ_apply hρ hE, withDensityᵥ_apply hν hE]
    change (∫ w in E, φ w ∂μ) = (∫ w in E, φ w ∂ρ) + ∫ w in E, φ w ∂ν
    rw [← hsplit, Measure.restrict_add,
      integral_add_measure hρ.integrableOn hν.integrableOn]
  have hf : fourierProjection Kf qf ξ = η + fourierProjection Kb qb ξ := by
    rw [fourierProjection_eq_densityMap Kf qf ξ _ (fourierProjection_spec Kf qf ξ),
      fourierProjection_eq_densityMap Kb qb ξ _ (fourierProjection_spec Kb qb ξ)]
    rw [← hq]
    change (μ.withDensityᵥ φ).map Prod.fst = η + (ν.withDensityᵥ φ).map Prod.fst
    rw [hdensity, VectorMeasure.map_add]
  have hηvar : η.variation ≤ ρ.map Prod.fst := by
    apply VectorMeasure.variation_map_le.trans
    rw [Measure.variation_withDensityᵥ hρ]
    have hp : (fun w => ‖φ w‖ₑ) = 1 := by
      funext w
      rw [← ofReal_norm, norm_fourierPhase]
      norm_num
    rw [hp, withDensity_one]
  have hη : η.variation univ ≤ ρ univ := by
    have h := Measure.le_iff.mp hηvar univ MeasurableSet.univ
    rwa [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ] at h
  have hηfin : η.variation univ ≠ ⊤ := ne_of_lt (hη.trans_lt (measure_lt_top ρ univ))
  have hfvar := fourierProjection_totalVariation_le_one Kf qf ξ _
    (fourierProjection_spec Kf qf ξ)
  have hff : (fourierProjection Kf qf ξ).variation univ ≠ ⊤ :=
    ne_of_lt (hfvar.trans_lt ENNReal.one_lt_top)
  have htriangle : (fourierProjection Kb qb ξ).variation univ ≤
      (fourierProjection Kf qf ξ).variation univ + η.variation univ := by
    have he : fourierProjection Kb qb ξ = fourierProjection Kf qf ξ - η := by
      rw [hf]
      abel
    rw [he]
    exact Measure.le_iff.mp VectorMeasure.variation_sub_le univ MeasurableSet.univ
  have ht := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hff, hηfin⟩) htriangle
  rw [ENNReal.toReal_add hff hηfin] at ht
  have hd : (ρ univ).toReal = μ.real univ - ν.real univ := by
    rw [Measure.sub_apply MeasurableSet.univ hdom]
    exact ENNReal.toReal_sub_of_le (Measure.le_iff.mp hdom univ MeasurableSet.univ)
      (measure_ne_top μ univ)
  have hr := ENNReal.toReal_mono (measure_ne_top ρ univ) hη
  have hm : μ.real univ ≤ 1 := by
    change (Kf.master qf univ).toReal ≤ 1
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top
      (Kf.mass_le_one qf)
  rw [hd] at hr
  change _ ≤ _ + 1 - ν.real univ
  linarith only [ht, hr, hm]

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
