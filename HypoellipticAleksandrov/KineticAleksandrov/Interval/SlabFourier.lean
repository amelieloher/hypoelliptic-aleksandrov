module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.SlabFourierAssembly
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.SlabFourierGreen

/-! # The interval slab Fourier theorem

Occupation, killing and frequency decay are discharged by their proved interval
lemmas. The only hypotheses are the explicit analytic inputs.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay
open HypoellipticAleksandrov.KineticAleksandrov.Green
open scoped ENNReal NNReal

/-- The scalar slab exponent is the literal exponent in case I. -/
theorem interval_slab_beta (γ : ℝ) : slabBeta 1 γ = 3 / (2 * γ) - 1 / 2 := by
  norm_num [slabBeta]

/-- Integrating frequencies gives the scalar slab height exponent. -/
theorem interval_slab_height_exponent (γ : ℝ) :
    slabBeta 1 γ - 3 * (1 : ℝ) / 2 = 3 / (2 * γ) - 2 := by
  rw [interval_slab_beta]
  ring

/-- Uniform interval slab Fourier densities, with both killing and frequency decay. -/
theorem interval_slab_fourier
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam m Lb length : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hm : 0 < m) (hmLb : m ≤ Lb) (hlength : 0 < length) :
    ∃ C : ℝ → ℝ≥0, ∃ k : ℝ, 0 < k ∧
    ∀ (a c : ℝ) (_hac : a < c) (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1),
    SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b →
    ∀ (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
      (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
      (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary),
    RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) b S K →
    c - a = length → ∀ (σ T : ℝ), 0 < T →
    ∀ (μ : Measure (EvolutionState (PDE.oneDimensionalAxisBox a c) stationary σ))
    [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier 1)), IsGreenMeasure K σ ⊤ μ Γ →
    ∃ g : SlabBase 1 → ℝ≥0∞, Measurable g ∧
      (slabMeasure 1 T Γ).fst = (slabBase 1 T).withDensity g ∧
      (∀ γ : ℝ, 1 ≤ γ → γ ≤ 2 → eLpNorm g (ENNReal.ofReal γ) (slabBase 1 T) ≤
        (C γ : ℝ≥0∞) * μ univ * ENNReal.ofReal (T ^ (3 / (2 * γ) - 1 / 2))) ∧
      ∃ f : PDE.Vec 1 → SlabBase 1 → ℂ, Measurable (Function.uncurry f) ∧
      (∀ ξ, Integrable (f ξ) (slabBase 1 T) ∧
        ∀ E : Set (SlabBase 1), MeasurableSet E → ∫ y in E, f ξ y ∂slabBase 1 T =
          ∫ p in {p : GreenCarrier 1 | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T},
            Complex.exp (-((PDE.vecDot ξ p.2.2 : ℝ) * Complex.I)) ∂Γ) ∧
      ∀ γ : ℝ, 1 ≤ γ → γ ≤ 2 →
        (∀ ξ, eLpNorm (f ξ) (ENNReal.ofReal γ) (slabBase 1 T) ≤
          (C γ : ℝ≥0∞) * μ univ * ENNReal.ofReal (T ^ (3 / (2 * γ) - 1 / 2) *
            Real.exp (-k * T * (1 + PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3))))) ∧
        ENNReal.ofReal ((2 * Real.pi)⁻¹) *
            ∫⁻ ξ, eLpNorm (f ξ) (ENNReal.ofReal γ) (slabBase 1 T) ≤
          (C γ : ℝ≥0∞) * μ univ *
            ENNReal.ofReal (T ^ (3 / (2 * γ) - 2) * Real.exp (-k * T)) := by
  obtain ⟨Co, hoc⟩ := intervalExtension_occupation hH hLE lam Lam hlam hlamLam
  obtain ⟨Cd, kd, hCd, hkd, hdec⟩ := intervalExtension_fourier_decay hH hLE
    lam Lam m Lb length hlam hlamLam hm hmLb hlength
  refine ⟨slabConstant' 1 Co Cd kd, kd / 2, div_pos hkd (by norm_num), ?_⟩
  intro a c hac B b hs hJ S K hr hlen σ T hT μ _ Γ hΓ
  let Kw := intervalExtension hJ K
  let μw := μ.map (intervalStateInclusion σ)
  have hc : IsTranslationCovariantEvolution (wholeSpace 1) (fun _ => (0 : PDE.Vec 1))
      MeasurableSet.univ Kw := intervalExtension_covariance hJ K
    (interval_evolution_clauses hH hLE hac B b hs hJ S K hr).2.2
  have hcomp : Kw.HasComposition MeasurableSet.univ :=
    intervalExtension_composition hJ K hr.2.2.2
  have hΓw := intervalExtension_isGreenMeasure hJ K σ μ Γ hΓ
  obtain ⟨g, hgm, hgE, hgb, f, hfm, hfE, hfb⟩ := killed_slab_fourier_of_bounds
    (by norm_num) Kw hc hcomp Co (hoc m Lb hm hmLb a c hac B b hs hJ S K hr)
    Cd kd hCd hkd (hdec a c hac B b hs hJ S K hr hlen) σ μw Γ hΓw hT
  have hM : μw univ = μ univ := by
    dsimp only [μw]
    rw [Measure.map_apply (measurable_intervalStateInclusion σ) MeasurableSet.univ,
      preimage_univ]
  refine ⟨g, hgm, hgE, ?_, f, hfm, hfE, ?_⟩
  · intro γ hγ1 hγ2
    have h := hgb γ hγ1 (by norm_num [slabGamma0]; exact hγ2)
    simpa only [hM, interval_slab_beta] using h
  · intro γ hγ1 hγ2
    obtain ⟨hf, hfreq⟩ := hfb γ hγ1 (by norm_num [slabGamma0]; exact hγ2)
    constructor
    · intro ξ
      have h := hf ξ
      rw [hM, interval_slab_beta] at h
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg hT.le _)]
      simpa only [neg_mul, mul_assoc] using h
    · rw [hM, Nat.cast_one, interval_slab_height_exponent] at hfreq
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg hT.le _)]
      simpa only [pow_one, neg_mul, mul_assoc] using hfreq

end HypoellipticAleksandrov.KineticAleksandrov.Interval
