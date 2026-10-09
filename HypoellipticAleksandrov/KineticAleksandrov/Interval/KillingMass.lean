module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.KillingTests
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.SmoothTestOrder

/-! # From smooth endpoint tests to killed interval mass -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay

/-- Smooth compact tests bounded by one determine an upper bound for supported mass. -/
theorem mass_le_of_interval_smooth_tests {U : Set (PDE.Vec 1)} (hU : IsOpen U)
    (μ : Measure (PDE.Vec 1)) [IsFiniteMeasure μ] (hμ : μ.restrict U = μ)
    {C : ℝ} (hC : 0 ≤ C)
    (htest : ∀ φ : PDE.Vec 1 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ U → (∀ w, 0 ≤ φ w ∧ φ w ≤ 1) → ∫ w, φ w ∂μ ≤ C) :
    μ.real univ ≤ C := by
  have hbound : μ U ≤ ENNReal.ofReal C := by
    rw [hU.measure_eq_iSup_isCompact μ]
    refine iSup_le fun A => iSup_le fun hAU => iSup_le fun hA => ?_
    obtain ⟨φ, hφ, hφc, hφU, hφr, hφA⟩ := exists_smooth_cutoff hA hU hAU
    have hi := hφ.continuous.integrable_of_hasCompactSupport hφc (μ := μ)
    have hle : μ.real A ≤ ∫ w, φ w ∂μ := by
      rw [← integral_indicator_one hA.measurableSet]
      apply integral_mono ((integrable_const (1 : ℝ)).indicator hA.measurableSet) hi
      intro w
      by_cases hw : w ∈ A
      · simp only [indicator_of_mem hw, hφA w hw, le_refl]
      · simpa only [indicator_of_notMem hw] using (hφr w).1
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ A)]
    exact ENNReal.ofReal_le_ofReal (hle.trans (htest φ hφ hφc hφU hφr))
  have he : μ univ = μ U := by
    conv_lhs => rw [← hμ]
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
  rw [Measure.real, he]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq
    (ENNReal.toReal_ofReal hC)

/-- The endpoint test bound gives the total positive parabolic mass bound. -/
theorem interval_endpoint_mass_bound {a c lam Lam σ τ s e : ℝ}
    (hac : a < c) (hστ : σ < τ) (hlam : 0 < lam) (hs : s ^ 2 = 1)
    (B : CoefficientField 1) (hB : IsSectionTwoCoefficient lam Lam B)
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (hpar : HasParabolicMarginalBundle (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) K)
    (hdpos : ∀ w ∈ PDE.oneDimensionalAxisBox a c, 0 < s * (w 0 - e))
    (hdnonneg : ∀ w ∈ closure (PDE.oneDimensionalAxisBox a c), 0 ≤ s * (w 0 - e))
    (v : PDE.Vec 1) (hv : v ∈ movingDomain (PDE.oneDimensionalAxisBox a c) stationary σ) :
    (P K hJ (scalarQuery σ τ hστ.le v hv)).real univ ≤
      intervalHeat lam (τ - σ) (s * (v 0 - e)) := by
  have hvJ : v ∈ PDE.oneDimensionalAxisBox a c := by
    simpa only [movingDomain_stationary] using hv
  apply mass_le_of_interval_smooth_tests
    (isOpen_of_isAdmissibleEvolutionDomain (interval_admissible hac))
    (P K hJ (scalarQuery σ τ hστ.le v hv))
  · apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    exact P_compl_eq_zero_stationary K hJ _
  · exact intervalErf_nonneg (div_nonneg (hdpos v hvJ).le (by positivity))
  · intro φ hφs hφc hφJ hφ
    exact interval_endpoint_test_bound hac hστ hlam hs B hB hJ K hpar
      hdpos hdnonneg v hv φ hφs hφc hφJ hφ

end HypoellipticAleksandrov.KineticAleksandrov.Interval
