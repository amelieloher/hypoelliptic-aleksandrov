module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.DecayBlocks

/-! # Exponential loss of mass through the interval boundary -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay

/-- Zero-frequency total variation equals the positive scalar mass. -/
theorem interval_zero_tv_eq_mass {a c : ℝ}
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (B : CoefficientField 1)
    (hp : HasParabolicMarginalBundle (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) K)
    (σ τ : ℝ) (hστ : σ ≤ τ) (v : PDE.oneDimensionalAxisBox a c) :
    TV (intervalFourierKernel K σ τ hστ 0 v) =
      (P K hJ (scalarQuery σ τ hστ v.1
        (by simpa only [movingDomain_stationary] using v.2))).real univ := by
  let q : EvolutionQuery (PDE.oneDimensionalAxisBox a c) stationary := movingQuery σ τ hστ v.1 0
    (by simpa only [movingDomain_stationary] using v.2)
  have hm : K.firstMarginal q univ = K.master q univ := by
    rw [MovingFiberKernel.firstMarginal, ProbabilityTheory.Kernel.fst_apply,
      Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ]
  have : IsFiniteMeasure (K.firstMarginal q) :=
    ⟨by rw [hm]; exact (K.mass_le_one q).trans_lt ENNReal.one_lt_top⟩
  rw [intervalFourierKernel_zero]
  change (((K.firstMarginal q).withDensityᵥ (fun _ => (1 : ℂ))).variation univ).toReal = _
  rw [Measure.variation_withDensityᵥ (integrable_const (1 : ℂ))]
  simp only [enorm_one]
  change (((K.firstMarginal q).withDensity 1) univ).toReal = _
  rw [withDensity_one, hm]
  unfold Measure.real
  rw [interval_parabolic_mass_eq_master hJ K B hp σ τ hστ v.1 0]

/-- The scalar mass has the source killing decay with the exact squared-length rate. -/
theorem interval_mass_decay
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam m Lb length : ℝ) (hlam : 0 < lam) (hlength : 0 < length) :
    ∃ C k : ℝ, 0 < C ∧ 0 < k ∧
      ∀ (a c : ℝ) (_hac : a < c) (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1),
      SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b →
      ∀ (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
      (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
      (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary),
      RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
        (zIndependentCoefficient B) b S K →
      c - a = length → ∀ (σ τ : ℝ) (hστ : σ ≤ τ) (v : PDE.oneDimensionalAxisBox a c),
      (P K hJ (scalarQuery σ τ hστ v.1
        (by simpa only [movingDomain_stationary] using v.2))).real univ ≤
        C * Real.exp (-k * (τ - σ)) := by
  let q := intervalErf (1 / (4 * Real.sqrt lam))
  obtain ⟨hq, hq1⟩ := interval_killing_factor hlam
  have hT : 0 < length ^ 2 := sq_pos_of_pos hlength
  refine ⟨q⁻¹, -Real.log q / length ^ 2, inv_pos.mpr hq,
    div_pos (neg_pos.mpr (Real.log_neg hq hq1)) hT, ?_⟩
  intro a c hac B b hs hJ S K hr hlen σ τ hστ v
  obtain ⟨_hm, hp, hc⟩ := interval_evolution_clauses hH hLE hac B b hs hJ S K hr
  rw [← interval_zero_tv_eq_mass hJ K B hp σ τ hστ v]
  apply interval_exponential_of_blocks K hJ hr.2.2.2 hc hT hq hq1.le 0
  intro s w
  have h := interval_killing_block hH hLE hac B b hs hJ S K hr s 0 w
    (le_add_of_nonneg_right (sq_nonneg (c - a)))
  simpa only [hlen] using h

/-- Every Fourier mode inherits the scalar killing rate, including zero frequency. -/
theorem interval_fourier_killing_decay
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam m Lb length : ℝ) (hlam : 0 < lam) (hlength : 0 < length) :
    ∃ C k : ℝ, 0 < C ∧ 0 < k ∧
      ∀ (a c : ℝ) (_hac : a < c) (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1),
      SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b →
      ∀ (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
      (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
      (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary),
      RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
        (zIndependentCoefficient B) b S K →
      c - a = length → ∀ (σ τ : ℝ) (hστ : σ ≤ τ) (ξ : PDE.Vec 1)
      (v : PDE.oneDimensionalAxisBox a c),
      TV (intervalFourierKernel K σ τ hστ ξ v) ≤ C * Real.exp (-k * (τ - σ)) := by
  obtain ⟨C, k, hC, hk, hmass⟩ := interval_mass_decay hH hLE
    lam Lam m Lb length hlam hlength
  refine ⟨C, k, hC, hk, ?_⟩
  intro a c hac B b hs hJ S K hr hlen σ τ hστ ξ v
  have hp := (interval_evolution_clauses hH hLE hac B b hs hJ S K hr).2.1
  exact (interval_fourier_tv_le_mass hJ K B hp σ τ hστ v.1 0 ξ
    (by simpa only [movingDomain_stationary] using v.2) _
    (intervalFourierKernel_spec K σ τ hστ ξ v)).trans
    (hmass a c hac B b hs hJ S K hr hlen σ τ hστ v)

end HypoellipticAleksandrov.KineticAleksandrov.Interval
