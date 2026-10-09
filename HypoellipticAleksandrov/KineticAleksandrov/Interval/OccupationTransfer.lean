module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.OccupationDomination
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.OccupationDensity

/-! # Transfer of whole-space occupation density to the interval

Positive kernel domination is integrated over the actual interval initial measure
and elapsed Lebesgue measure. No occupation estimate is assumed for the interval.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay
open HypoellipticAleksandrov.KineticAleksandrov.Green

/-- Domination on an interior time slab transfers a whole-space occupation density. -/
theorem intervalOccupationMeasure_le_density {a c lam Lam : ℝ}
    (hac : a < c) (B : CoefficientField 1) (hB : IsSectionTwoCoefficient lam Lam B)
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (hp : HasParabolicMarginalBundle (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) K)
    (Kw : MovingFiberKernel (wholeSpace 1) (fun _ => (0 : PDE.Vec 1)))
    (hpw : HasParabolicMarginalBundle (wholeSpace 1) (fun _ => (0 : PDE.Vec 1))
      MeasurableSet.univ (zIndependentCoefficient B) Kw)
    (σ T : ℝ) (hT : 0 < T) (ρ : Measure (PDE.oneDimensionalAxisBox a c))
    [IsFiniteMeasure ρ] (g : TimeVelocity 1 → ℝ)
    (hg : SlabOccupationDensity Kw σ T (ρ.map Subtype.val) g)
    (hgi : Integrable g (volume.restrict (Ioo (0 : ℝ) T ×ˢ univ))) :
    intervalOccupationMeasure σ T K ρ ≤
      (volume.restrict (Ioo (0 : ℝ) T ×ˢ univ)).withDensity
        (fun p => ENNReal.ofReal (g p)) := by
  let R : Set (TimeVelocity 1) := Ioo 0 T ×ˢ univ
  have hR : MeasurableSet R := measurableSet_Ioo.prod MeasurableSet.univ
  have hs : (intervalOccupationMeasure σ T K ρ).restrict R =
      intervalOccupationMeasure σ T K ρ :=
    Measure.restrict_eq_self_of_ae_mem (by
      rw [ae_iff]; exact intervalOccupationMeasure_compl_slab σ T hT K ρ)
  have hsub : ∀ A : Set (TimeVelocity 1), MeasurableSet A → A ⊆ R →
      intervalOccupationMeasure σ T K ρ A ≤
        ∫⁻ p in A, ENNReal.ofReal (g p) := by
    intro A hA hAR
    have hm : Measurable (fun v : PDE.Vec 1 =>
        ∫⁻ t in Ioo 0 T, occupationKernel Kw σ t v {w | (t, w) ∈ A}) :=
      ((measurable_occupationKernel_section Kw σ hA).comp measurable_swap).lintegral_prod_right'
    rw [occupation_set_identity Kw σ T hT (ρ.map Subtype.val) g hg hgi hA hAR,
      lintegral_map hm measurable_subtype_coe]
    rw [intervalOccupationMeasure_apply σ T K ρ A hA]
    apply lintegral_mono
    intro v
    dsimp only
    rw [← lintegral_elapsed_finite T hT]
    apply lintegral_mono
    intro t
    have hst : σ < σ + t.1 := lt_add_of_pos_right _ t.2.1
    have hv : v.1 ∈ movingDomain (PDE.oneDimensionalAxisBox a c) stationary σ := by
      simpa only [movingDomain_stationary] using v.2
    have ht := interval_parabolic_le_whole hac hst B hB hJ K hp Kw hpw v.1 hv
    have he := interval_firstMarginal_eq_parabolic hJ K B hp σ (σ + t.1) hst.le v.1 0 hv
    change K.firstMarginal (movingQuery σ (σ + t.1) hst.le v.1 0 hv) _ ≤ _
    rw [he]
    dsimp only
    rw [occupationKernel_of_nonneg Kw σ t.1 t.2.1.le]
    exact Measure.le_iff'.1 ht _
  apply Measure.le_iff.2
  intro A hA
  rw [← hs, Measure.restrict_apply hA, withDensity_apply _ hA]
  calc
    _ ≤ ∫⁻ p in A ∩ R, ENNReal.ofReal (g p) :=
      hsub _ (hA.inter hR) inter_subset_right
    _ = _ := by rw [Measure.restrict_restrict hA]

end HypoellipticAleksandrov.KineticAleksandrov.Interval
