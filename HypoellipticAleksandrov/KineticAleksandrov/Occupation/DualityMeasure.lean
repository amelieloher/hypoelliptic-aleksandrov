module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationDensity
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The projected unit-time occupation measure

This is the velocity marginal of the Section 2 product-kernel Green construction,
with initial state `(v,0)` and positive elapsed times strictly below one. Its defining
bounded-test integral is exactly the right-hand side of `IsOccupationDensity`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set SectionTwo
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open scoped ENNReal ProbabilityTheory

variable {d : ℕ}

/-- Unit elapsed-time Lebesgue measure is finite. -/
instance unitElapsedVolume_finite : IsFiniteMeasure (elapsedVolume (ENNReal.ofReal (1 : ℝ))) := ⟨by
  rw [elapsedVolume_univ 1 zero_lt_one]
  exact ENNReal.ofReal_lt_top⟩

/-- Pull back the first marginal along the literal unit-time occupation queries. -/
def unitOccupationKernel (K : WholeKernel d) :
    ProbabilityTheory.Kernel (PDE.Vec d × ElapsedTime (ENNReal.ofReal (1 : ℝ))) (PDE.Vec d) :=
  K.firstMarginal.comap (fun q => wholeSpaceQuery 0 q.2.1 q.2.2.1.le q.1 0) (by
    apply Measurable.subtype_mk
    change Measurable (fun q : PDE.Vec d × ElapsedTime (ENNReal.ofReal (1 : ℝ)) =>
      (0, (q.2.1, (q.1, 0))))
    fun_prop)

/-- The pulled-back velocity kernel is finite. -/
instance unitOccupationKernel_finite (K : WholeKernel d) :
    ProbabilityTheory.IsFiniteKernel (unitOccupationKernel K) := by
  unfold unitOccupationKernel MovingFiberKernel.firstMarginal
  infer_instance

/-- The pulled-back kernel remains a subprobability kernel. -/
theorem unitOccupationKernel_mass_le (K : WholeKernel d)
    (q : PDE.Vec d × ElapsedTime (ENNReal.ofReal (1 : ℝ))) :
    unitOccupationKernel K q univ ≤ 1 := by
  change K.firstMarginal (wholeSpaceQuery 0 q.2.1 q.2.2.1.le q.1 0) univ ≤ 1
  rw [K.firstMarginal_apply _ _ MeasurableSet.univ]
  simpa using K.mass_le_one (wholeSpaceQuery 0 q.2.1 q.2.2.1.le q.1 0)

/-- The product-kernel measure has mass at most the initial mass. -/
theorem unitOccupationProduct_mass_le (K : WholeKernel d) (ρ : Measure (PDE.Vec d))
    [IsFiniteMeasure ρ] :
    ((ρ.prod (elapsedVolume (ENNReal.ofReal (1 : ℝ)))).compProd
      (unitOccupationKernel K)) univ ≤ ρ univ := by
  rw [Measure.compProd_apply MeasurableSet.univ]
  calc
    _ ≤ ∫⁻ q, (1 : ℝ≥0∞) ∂ρ.prod (elapsedVolume (ENNReal.ofReal (1 : ℝ))) :=
      lintegral_mono fun q => by simpa using unitOccupationKernel_mass_le K q
    _ = ρ univ := by
      rw [lintegral_const, one_mul, ← univ_prod_univ, Measure.prod_prod]
      have he : elapsedVolume (ENNReal.ofReal (1 : ℝ)) univ = 1 := by
        rw [elapsedVolume_univ (1 : ℝ) zero_lt_one, ENNReal.ofReal_one]
      rw [he, mul_one]

/-- The unprojected product-kernel occupation measure is finite. -/
instance unitOccupationProduct_finite (K : WholeKernel d) (ρ : Measure (PDE.Vec d))
    [IsFiniteMeasure ρ] :
    IsFiniteMeasure ((ρ.prod (elapsedVolume (ENNReal.ofReal (1 : ℝ)))).compProd
      (unitOccupationKernel K)) :=
  ⟨(unitOccupationProduct_mass_le K ρ).trans_lt (measure_lt_top ρ univ)⟩

/-- The unit-time occupation measure, with time and velocity in source order. -/
def unitOccupationMeasure (K : WholeKernel d) (ρ : Measure (PDE.Vec d)) :
    Measure (TimeVelocity d) :=
  ((ρ.prod (elapsedVolume (ENNReal.ofReal (1 : ℝ)))).compProd (unitOccupationKernel K)).map
    (fun q => (q.1.2.1, q.2))

/-- The projected occupation measure is finite for finite initial measures. -/
instance unitOccupationMeasure_finite (K : WholeKernel d) (ρ : Measure (PDE.Vec d))
    [IsFiniteMeasure ρ] : IsFiniteMeasure (unitOccupationMeasure K ρ) := by
  unfold unitOccupationMeasure
  infer_instance

/-- Unit-time occupation mass is at most the initial mass. -/
theorem unitOccupationMeasure_mass_le (K : WholeKernel d) (ρ : Measure (PDE.Vec d))
    [IsFiniteMeasure ρ] : unitOccupationMeasure K ρ univ ≤ ρ univ := by
  rw [unitOccupationMeasure, Measure.map_apply (by fun_prop) MeasurableSet.univ, preimage_univ]
  exact unitOccupationProduct_mass_le K ρ

/-- Positive elapsed time puts the entire occupation measure in the open unit slab. -/
theorem unitOccupationMeasure_compl_slab (K : WholeKernel d) (ρ : Measure (PDE.Vec d)) :
    unitOccupationMeasure K ρ (Ioo (0 : ℝ) 1 ×ˢ univ)ᶜ = 0 := by
  rw [unitOccupationMeasure, Measure.map_apply (by fun_prop)
    ((measurableSet_Ioo.prod MeasurableSet.univ).compl)]
  have he : (fun q : (PDE.Vec d × ElapsedTime (ENNReal.ofReal (1 : ℝ))) × PDE.Vec d =>
      (q.1.2.1, q.2)) ⁻¹'
      (Ioo (0 : ℝ) 1 ×ˢ univ)ᶜ = ∅ := by
    ext q
    simp only [mem_preimage, mem_compl_iff, mem_prod, mem_Ioo, mem_univ, and_true,
      mem_empty_iff_false, iff_false, not_not]
    exact ⟨q.1.2.2.1, ((ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mp q.1.2.2.2)⟩
  rw [he, measure_empty]

/-- Projected occupation integration is the full iterated first-marginal characterization. -/
theorem integral_unitOccupationMeasure (K : WholeKernel d) (ρ : Measure (PDE.Vec d))
    [IsFiniteMeasure ρ] (φ : TimeVelocity d → ℝ) (hφ : Measurable φ)
    (hφb : ∃ M : ℝ, ∀ q, |φ q| ≤ M) :
    (∫ q, φ q ∂unitOccupationMeasure K ρ) =
      ∫ v, ∫ τ : ElapsedTime (ENNReal.ofReal (1 : ℝ)),
        ∫ w, φ (τ.1, w) ∂K.firstMarginal
          (wholeSpaceQuery 0 (0 + τ.1) (le_add_of_nonneg_right τ.2.1.le) v 0)
        ∂elapsedVolume (ENNReal.ofReal (1 : ℝ)) ∂ρ := by
  obtain ⟨M, hM⟩ := hφb
  let ψ : (PDE.Vec d × ElapsedTime (ENNReal.ofReal (1 : ℝ))) × PDE.Vec d → ℝ :=
    fun q => φ (q.1.2.1, q.2)
  have hψ : Measurable ψ := hφ.comp (by fun_prop)
  have hi : Integrable ψ ((ρ.prod (elapsedVolume (ENNReal.ofReal (1 : ℝ)))).compProd
      (unitOccupationKernel K)) :=
    (integrable_const M).mono' hψ.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => by simpa only [Real.norm_eq_abs] using hM _)
  rw [unitOccupationMeasure, integral_map (by fun_prop) hφ.aestronglyMeasurable]
  change (∫ q, ψ q ∂_) = _
  rw [Measure.integral_compProd hi]
  exact (integral_prod _ hi.integral_compProd).trans (by
    simp only [ProbabilityTheory.Kernel.prodMkLeft_apply, unitOccupationKernel,
      ProbabilityTheory.Kernel.comap_apply, ψ, zero_add])

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
