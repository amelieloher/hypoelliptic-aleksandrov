module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.FourierKernelsMarginal
public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierOccupation
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The projected finite-horizon interval occupation measure

This is the velocity marginal of the Section 2 product-kernel Green construction,
with initial state `(v,0)` and positive elapsed times strictly below `T`. Its
bounded-test integral retains the actual interval subtype of starting velocities.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Interval

open MeasureTheory Set SectionTwo
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open scoped ENNReal ProbabilityTheory

open HypoellipticAleksandrov.KineticAleksandrov.Decay

variable {a c : ℝ}
variable (σ T : ℝ) (hT : 0 < T)

include hT in
/-- Finite positive elapsed horizons carry finite Lebesgue measure. -/
theorem intervalElapsedVolume_finite : IsFiniteMeasure (elapsedVolume (ENNReal.ofReal T)) :=
  ⟨by rw [elapsedVolume_univ T hT]; exact ENNReal.ofReal_lt_top⟩

/-- Pull back the first marginal along the literal finite-horizon occupation queries. -/
def intervalOccupationKernel (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary) :
    ProbabilityTheory.Kernel ((PDE.oneDimensionalAxisBox a c) × ElapsedTime (ENNReal.ofReal T))
      (PDE.Vec 1) :=
  K.firstMarginal.comap (fun q => movingQuery σ (σ + q.2.1) (le_add_of_nonneg_right q.2.2.1.le)
    q.1.1 0
    (by simpa only [movingDomain_stationary] using q.1.2)) (by
    apply Measurable.subtype_mk
    change Measurable (fun q : (PDE.oneDimensionalAxisBox a c) × ElapsedTime (ENNReal.ofReal T) =>
      (σ, (σ + q.2.1, (q.1.1, 0))))
    fun_prop)

/-- The pulled-back velocity kernel is finite. -/
instance intervalOccupationKernel_finite (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c)
  stationary) :
    ProbabilityTheory.IsFiniteKernel (intervalOccupationKernel σ T K) := by
  unfold intervalOccupationKernel MovingFiberKernel.firstMarginal
  infer_instance

/-- The pulled-back kernel remains a subprobability kernel. -/
theorem intervalOccupationKernel_mass_le (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c)
  stationary)
    (q : (PDE.oneDimensionalAxisBox a c) × ElapsedTime (ENNReal.ofReal T)) :
    intervalOccupationKernel σ T K q univ ≤ 1 := by
  change K.firstMarginal (movingQuery σ (σ + q.2.1) (le_add_of_nonneg_right q.2.2.1.le) q.1.1 0
    (by simpa only [movingDomain_stationary] using q.1.2)) univ ≤ 1
  rw [K.firstMarginal_apply _ _ MeasurableSet.univ]
  simpa using K.mass_le_one (movingQuery σ (σ + q.2.1) (le_add_of_nonneg_right q.2.2.1.le) q.1.1 0
    (by simpa only [movingDomain_stationary] using q.1.2))

include hT in
/-- The product-kernel measure has mass at most the horizon times the initial mass. -/
theorem intervalOccupationProduct_mass_le (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c)
  stationary) (ρ : Measure (PDE.oneDimensionalAxisBox a c))
    [IsFiniteMeasure ρ] :
    ((ρ.prod (elapsedVolume (ENNReal.ofReal T))).compProd
      (intervalOccupationKernel σ T K)) univ ≤ ρ univ * ENNReal.ofReal T := by
  have := intervalElapsedVolume_finite T hT
  rw [Measure.compProd_apply MeasurableSet.univ]
  calc
    _ ≤ ∫⁻ q, (1 : ℝ≥0∞) ∂ρ.prod (elapsedVolume (ENNReal.ofReal T)) :=
      lintegral_mono fun q => by simpa using intervalOccupationKernel_mass_le σ T K q
    _ = ρ univ * ENNReal.ofReal T := by
      rw [lintegral_const, one_mul, ← univ_prod_univ, Measure.prod_prod]
      rw [elapsedVolume_univ T hT]

include hT in
/-- The unprojected product-kernel occupation measure is finite. -/
theorem intervalOccupationProduct_finite (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c)
  stationary) (ρ : Measure (PDE.oneDimensionalAxisBox a c))
    [IsFiniteMeasure ρ] :
    IsFiniteMeasure ((ρ.prod (elapsedVolume (ENNReal.ofReal T))).compProd
      (intervalOccupationKernel σ T K)) :=
  ⟨(intervalOccupationProduct_mass_le σ T hT K ρ).trans_lt (ENNReal.mul_lt_top (measure_lt_top ρ
    univ) ENNReal.ofReal_lt_top)⟩

/-- The finite-horizon occupation measure, with time and velocity in source order. -/
def intervalOccupationMeasure (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
  (ρ : Measure (PDE.oneDimensionalAxisBox a c)) :
    Measure (TimeVelocity 1) :=
  ((ρ.prod (elapsedVolume (ENNReal.ofReal T))).compProd (intervalOccupationKernel σ T K)).map
    (fun q => (q.1.2.1, q.2))

include hT in
/-- The projected occupation measure is finite for finite initial measures. -/
theorem intervalOccupationMeasure_finite (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c)
  stationary) (ρ : Measure (PDE.oneDimensionalAxisBox a c))
    [IsFiniteMeasure ρ] : IsFiniteMeasure (intervalOccupationMeasure σ T K ρ) := by
  have := intervalElapsedVolume_finite T hT
  unfold intervalOccupationMeasure
  infer_instance

include hT in
/-- Occupation mass is at most the initial mass. -/
theorem intervalOccupationMeasure_mass_le (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c)
  stationary) (ρ : Measure (PDE.oneDimensionalAxisBox a c))
    [IsFiniteMeasure ρ] : intervalOccupationMeasure σ T K ρ univ ≤ ρ univ * ENNReal.ofReal T := by
  rw [intervalOccupationMeasure, Measure.map_apply (by fun_prop) MeasurableSet.univ, preimage_univ]
  exact intervalOccupationProduct_mass_le σ T hT K ρ

include hT in
/-- Positive elapsed time puts the entire occupation measure in the open finite slab. -/
theorem intervalOccupationMeasure_compl_slab (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a
  c) stationary) (ρ : Measure (PDE.oneDimensionalAxisBox a c)) :
    intervalOccupationMeasure σ T K ρ (Ioo (0 : ℝ) T ×ˢ univ)ᶜ = 0 := by
  rw [intervalOccupationMeasure, Measure.map_apply (by fun_prop)
    ((measurableSet_Ioo.prod MeasurableSet.univ).compl)]
  have he : (fun q : ((PDE.oneDimensionalAxisBox a c) × ElapsedTime (ENNReal.ofReal T)) × PDE.Vec
    1 =>
      (q.1.2.1, q.2)) ⁻¹'
      (Ioo (0 : ℝ) T ×ˢ univ)ᶜ = ∅ := by
    ext q
    simp only [mem_preimage, mem_compl_iff, mem_prod, mem_Ioo, mem_univ, and_true,
      mem_empty_iff_false, iff_false, not_not]
    exact ⟨q.1.2.2.1, ((ENNReal.ofReal_lt_ofReal_iff hT).mp q.1.2.2.2)⟩
  rw [he, measure_empty]

include hT in
/-- Projected occupation integration is the full iterated first-marginal characterization. -/
theorem integral_intervalOccupationMeasure (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c)
  stationary) (ρ : Measure (PDE.oneDimensionalAxisBox a c))
    [IsFiniteMeasure ρ] (φ : TimeVelocity 1 → ℝ) (hφ : Measurable φ)
    (hφb : ∃ M : ℝ, ∀ q, |φ q| ≤ M) :
    (∫ q, φ q ∂intervalOccupationMeasure σ T K ρ) =
      ∫ v, ∫ τ : ElapsedTime (ENNReal.ofReal T),
        ∫ w, φ (τ.1, w) ∂K.firstMarginal
          (movingQuery σ (σ + τ.1) (le_add_of_nonneg_right τ.2.1.le) v.1 0
            (by simpa only [movingDomain_stationary] using v.2))
        ∂elapsedVolume (ENNReal.ofReal T) ∂ρ := by
  have := intervalElapsedVolume_finite T hT
  obtain ⟨M, hM⟩ := hφb
  let ψ : ((PDE.oneDimensionalAxisBox a c) × ElapsedTime (ENNReal.ofReal T)) × PDE.Vec 1 → ℝ :=
    fun q => φ (q.1.2.1, q.2)
  have hψ : Measurable ψ := hφ.comp (by fun_prop)
  have hi : Integrable ψ ((ρ.prod (elapsedVolume (ENNReal.ofReal T))).compProd
      (intervalOccupationKernel σ T K)) :=
    (integrable_const M).mono' hψ.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => by simpa only [Real.norm_eq_abs] using hM _)
  rw [intervalOccupationMeasure, integral_map (by fun_prop) hφ.aestronglyMeasurable]
  change (∫ q, ψ q ∂_) = _
  rw [Measure.integral_compProd hi]
  exact (integral_prod _ hi.integral_compProd).trans (by
    simp only [ProbabilityTheory.Kernel.prodMkLeft_apply, intervalOccupationKernel,
      ProbabilityTheory.Kernel.comap_apply, ψ])

/-- Set evaluation of the projected occupation measure is the iterated kernel action. -/
theorem intervalOccupationMeasure_apply
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (ρ : Measure (PDE.oneDimensionalAxisBox a c)) [IsFiniteMeasure ρ]
    (A : Set (TimeVelocity 1)) (hA : MeasurableSet A) :
    intervalOccupationMeasure σ T K ρ A =
      ∫⁻ v, ∫⁻ t : ElapsedTime (ENNReal.ofReal T),
        intervalOccupationKernel σ T K (v, t) {w | (t.1, w) ∈ A}
          ∂elapsedVolume (ENNReal.ofReal T) ∂ρ := by
  rw [intervalOccupationMeasure, Measure.map_apply (by fun_prop) hA,
    Measure.compProd_apply (hA.preimage (by fun_prop))]
  exact lintegral_prod _
    ((ProbabilityTheory.Kernel.measurable_kernel_prodMk_left
      (κ := intervalOccupationKernel σ T K) (hA.preimage (by fun_prop))).aemeasurable)

include hT in
/-- The occupation measure is concentrated in the open time-interval product. -/
theorem intervalOccupationMeasure_compl_region
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (ρ : Measure (PDE.oneDimensionalAxisBox a c)) [IsFiniteMeasure ρ] :
    intervalOccupationMeasure σ T K ρ
      (Ioo (0 : ℝ) T ×ˢ PDE.oneDimensionalAxisBox a c)ᶜ = 0 := by
  rw [intervalOccupationMeasure_apply σ T K ρ _ (measurableSet_Ioo.prod hJ).compl]
  apply lintegral_eq_zero_of_ae_eq_zero
  refine Filter.Eventually.of_forall fun v => ?_
  apply lintegral_eq_zero_of_ae_eq_zero
  refine Filter.Eventually.of_forall fun t => ?_
  have ht : t.1 < T := (ENNReal.ofReal_lt_ofReal_iff hT).mp t.2.2
  have he : {w : PDE.Vec 1 | (t.1, w) ∈
      (Ioo (0 : ℝ) T ×ˢ PDE.oneDimensionalAxisBox a c)ᶜ} =
        (PDE.oneDimensionalAxisBox a c)ᶜ := by
    ext w
    simp only [mem_ofPred_eq, mem_compl_iff, mem_prod, mem_Ioo,
      t.2.1, ht, true_and]
  dsimp only
  rw [he]
  let q : EvolutionQuery (PDE.oneDimensionalAxisBox a c) stationary := movingQuery σ (σ + t.1)
    (le_add_of_nonneg_right t.2.1.le) v.1 0
    (by simpa only [movingDomain_stationary] using v.2)
  change K.firstMarginal q _ = 0
  have hpre : MeasurableSet {p : EvolutionAmbientState 1 |
      p.1 ∈ (PDE.oneDimensionalAxisBox a c)ᶜ} := hJ.compl.preimage measurable_fst
  rw [K.firstMarginal_apply q _ hJ.compl, ← K.terminal_support q,
    Measure.restrict_apply hpre]
  have he' : {p : EvolutionAmbientState 1 | p.1 ∈
      (PDE.oneDimensionalAxisBox a c)ᶜ} ∩
      evolutionStateSet (PDE.oneDimensionalAxisBox a c) stationary q.1.2.1 = ∅ := by
    ext p
    simp only [mem_inter_iff, mem_ofPred_eq, mem_compl_iff, evolutionStateSet,
      movingDomain_stationary, mem_prod, mem_univ, and_true,
      not_and_self, mem_empty_iff_false]
  rw [he', measure_empty]

end HypoellipticAleksandrov.KineticAleksandrov.Interval
