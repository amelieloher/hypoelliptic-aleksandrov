module

public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierBound
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.SlabFourierDomination

/-! # Slab domination retaining the killing factor

The shared occupation and evolved-measure proof is applied to its constructed
half-time variation bound, retaining the additional exponential killing factor.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open MeasureTheory Set
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Green
open scoped ENNReal NNReal ProbabilityTheory
variable {d : ℕ} (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))

/-- Occupation domination bounds the Fourier density while retaining the half-time
killing and frequency factor. The half-time premise is discharged by the proved decay. -/
theorem killed_slab_fourier_density_bound (hd : 0 < d)
    (hcov : IsTranslationCovariantEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ K)
    (hcomp : K.HasComposition MeasurableSet.univ)
    (Cocc : ℝ → ℝ) (hocc : OccupationBoundedBy K Cocc)
    (Cdec cdec : ℝ) (hCdec : 0 < Cdec)  (σ₀ : ℝ)
    (μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀))
    [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier d)) (hΓ : IsGreenMeasure K σ₀ ⊤ μ Γ)
    {T : ℝ} (hT : 0 < T) (ξ : PDE.Vec d) (k : SlabBase d → ℂ) (hk : Integrable k (slabBase d T))
    (hkE : ∀ E : Set (SlabBase d), MeasurableSet E →
      ∫ y in E, k y ∂slabBase d T =
        ∫ p in {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T},
          Complex.exp (-((PDE.vecDot ξ p.2.2 : ℝ) * Complex.I)) ∂Γ)
    (hhalf : (halfMeasure K σ₀ T hT.le μ ξ).variation univ ≤
      μ univ * ENNReal.ofReal (Cdec * Real.exp
        (-(cdec * (T / 2) * (1 + PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3)))))) :
    ∀ γ : ℝ, 1 ≤ γ → γ ≤ slabGamma0 d →
      eLpNorm k (ENNReal.ofReal γ) (slabBase d T) ≤
        ENNReal.ofReal (Cocc γ * Cdec * (2 : ℝ) ^ slabBeta d γ) * μ univ *
          ENNReal.ofReal (T ^ slabBeta d γ) *
          ENNReal.ofReal (Real.exp
            (-((cdec / 2) * T * (1 + PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3))))) := by
  intro γ hγ1 hγ2
  have hρfin : IsFiniteMeasure (halfMeasure K σ₀ T hT.le μ ξ).variation :=
    interval_evolved_variation_finite μ _ _ _ (measurable_halfPhase ξ _) (norm_halfPhase ξ _)
  obtain ⟨gξ, hgξ, hnorm⟩ := hocc.2 (halfMeasure K σ₀ T hT.le μ ξ).variation (σ₀ + T / 2)
    (3 * T / 2) (by positivity)
  have hint : Integrable gξ
      (volume.restrict (Ioo (0 : ℝ) (3 * T / 2) ×ˢ (univ : Set (PDE.Vec d)))) := by
    have := (hnorm 1 le_rfl (one_le_slabGamma0 hd)).1
    rw [ENNReal.ofReal_one] at this
    exact memLp_one_iff_integrable.1 this
  have hkae := slab_fourier_ae_bound K hcov hcomp σ₀ μ Γ hΓ hT ξ gξ hgξ hint k hk hkE
  obtain ⟨hmem, hbd⟩ := hnorm γ hγ1 hγ2
  have hC0 : 0 ≤ Cocc γ := hocc.1 γ hγ1 hγ2
  have hβ := slabBeta_nonneg hd hγ1 hγ2
  -- step 1: domination
  have h1 : eLpNorm k (ENNReal.ofReal γ) (slabBase d T) ≤
      eLpNorm (fun y => ENNReal.ofReal (gξ (slabShift d (T / 2) y))) (ENNReal.ofReal γ)
        (slabBase d T) := by
    refine eLpNorm_mono_enorm_ae (f := k)
      (g := fun y => ENNReal.ofReal (gξ (slabShift d (T / 2) y))) hk.aestronglyMeasurable ?_
    filter_upwards [hkae] with y hy
    rwa [enorm_eq_self]
  -- step 2: the occupation bound
  set Cn : ℝ := Cocc γ * ((halfMeasure K σ₀ T hT.le μ ξ).variation univ).toReal *
    (3 * T / 2) ^ slabBeta d γ with hCn
  have hbd' : eLpNorm gξ (ENNReal.ofReal γ)
      (volume.restrict (Ioo (0 : ℝ) (3 * T / 2) ×ˢ (univ : Set (PDE.Vec d)))) ≤
        ENNReal.ofReal Cn := by
    rw [← ENNReal.ofReal_toReal hmem.eLpNorm_ne_top]
    exact ENNReal.ofReal_le_ofReal hbd
  have h2 := eLpNorm_slabShift_le gξ hgξ.1 hgξ.2.1 (T / 2) T (3 * T / 2) γ Cn hT.le
    (by linarith) (by linarith) hbd'
  -- step 3: arithmetic
  set E : ℝ := Real.exp (-((cdec / 2) * T * (1 + PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3)))) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hmass := hhalf
  have hrho : ((halfMeasure K σ₀ T hT.le μ ξ).variation univ).toReal ≤
      (μ univ).toReal * (Cdec * E) := by
    have hexp : Real.exp (-(cdec * (T / 2) * (1 + PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3)))) = E :=
      by
      rw [hE]; congr 1; ring
    rw [hexp] at hmass
    have hfin : μ univ * ENNReal.ofReal (Cdec * E) ≠ ⊤ :=
      ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
    have := ENNReal.toReal_mono hfin hmass
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  have hCnle : Cn ≤ (Cocc γ * Cdec * (2 : ℝ) ^ slabBeta d γ) * (μ univ).toReal *
      T ^ slabBeta d γ * E :=
    fourier_bound_arith _ _ _ _ _ _ _ hC0 hCdec.le ENNReal.toReal_nonneg hE0 hT hβ hrho
  have hfinal : ENNReal.ofReal Cn ≤
      ENNReal.ofReal (Cocc γ * Cdec * (2 : ℝ) ^ slabBeta d γ) * μ univ *
        ENNReal.ofReal (T ^ slabBeta d γ) * ENNReal.ofReal E := by
    refine (ENNReal.ofReal_le_ofReal hCnle).trans (le_of_eq ?_)
    have h2pos : 0 ≤ Cocc γ * Cdec * (2 : ℝ) ^ slabBeta d γ :=
      mul_nonneg (mul_nonneg hC0 hCdec.le) (Real.rpow_nonneg (by norm_num) _)
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul h2pos, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact h1.trans (h2.trans hfinal)


end HypoellipticAleksandrov.KineticAleksandrov.Interval
