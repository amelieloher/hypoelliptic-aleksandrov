module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationScalingCharacterization
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationScalingBundle

/-! # Scaling assembly from the unit-time duality conclusion -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic SectionTwo MeasureTheory Set
open scoped ENNReal
variable {d : ℕ}

/-- The unit-time duality conclusion supplies all slab densities by the source scaling. -/
theorem occupation_scaling_of_duality
    (lam Lam : ℝ)
    (hDuality :
    ∃ C : ℝ → ℝ,
      (∀ γ, 1 ≤ γ → γ ≤ ((d : ℝ) + 1) / d → 0 ≤ C γ) ∧
      ∀ (B : CoefficientField d) (_hB : IsSectionTwoCoefficient lam Lam B)
        (S : WholeFamily d) (K : WholeKernel d)
        (_hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          MeasurableSet.univ (zIndependentCoefficient B) (identityDrift d) S K)
        (_hP : HasParabolicMarginalBundle (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          MeasurableSet.univ (zIndependentCoefficient B) K)
        (ρ : Measure (PDE.Vec d)) [IsFiniteMeasure ρ],
        ∃ g : TimeVelocity d → ℝ, IsOccupationDensity K 0 1 ρ g ∧
          ∀ γ, 1 ≤ γ → γ ≤ ((d : ℝ) + 1) / d →
            MemLp g (ENNReal.ofReal γ)
              (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ univ)) ∧
            occupationLpNorm 1 γ g ≤ C γ * (ρ univ).toReal ) :
    ∃ C : ℝ → ℝ,
      (∀ γ, 1 ≤ γ → γ ≤ ((d : ℝ) + 1) / d → 0 ≤ C γ) ∧
      ∀ (B : CoefficientField d) (_hB : IsSectionTwoCoefficient lam Lam B)
        (S : WholeFamily d) (K : WholeKernel d)
        (_hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          MeasurableSet.univ (zIndependentCoefficient B) (identityDrift d) S K)
        (_hP : HasParabolicMarginalBundle (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          MeasurableSet.univ (zIndependentCoefficient B) K)
        (ρ : Measure (PDE.Vec d)) [IsFiniteMeasure ρ]
        (σ₀ T : ℝ) (hT : 0 < T),
        let r : {r : ℝ // 0 < r} := ⟨Real.sqrt T, Real.sqrt_pos.2 hT⟩
        let Φ := Scaling.KineticAffineScaling.ofRadius σ₀ 0 0 (identityDrift d) r
        let Ktilde := Scaling.KineticAffineScaling.pushKernel
          (Scaling.KineticAffineScaling.mapsDomain_wholeSpace Φ) K
        let ρtilde := ρ.map (fun v => (Real.sqrt T)⁻¹ • v)
        ∃ (g gtilde : TimeVelocity d → ℝ),
          IsOccupationDensity K σ₀ T ρ g ∧
          IsOccupationDensity Ktilde 0 1 ρtilde gtilde ∧
          (∀ q, g q = T ^ (-(d : ℝ) / 2) *
            gtilde (q.1 / T, (Real.sqrt T)⁻¹ • q.2)) ∧
          ∀ γ, 1 ≤ γ → γ ≤ ((d : ℝ) + 1) / d →
            MemLp g (ENNReal.ofReal γ)
              (volume.restrict (Ioo (0 : ℝ) T ×ˢ univ)) ∧
            MemLp gtilde (ENNReal.ofReal γ)
              (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ univ)) ∧
            occupationLpNorm T γ g =
              T ^ occupationBeta d γ * occupationLpNorm 1 γ gtilde ∧
            occupationLpNorm T γ g ≤
              C γ * (ρ univ).toReal * T ^ occupationBeta d γ := by
  obtain ⟨C, hC0, hunit⟩ := hDuality
  refine ⟨C, hC0, ?_⟩
  intro B hB S K hreal hP ρ _ σ₀ T hT
  dsimp only
  let r : {r : ℝ // 0 < r} := ⟨Real.sqrt T, Real.sqrt_pos.mpr hT⟩
  let Φ := Scaling.KineticAffineScaling.ofRadius σ₀ 0 0 (identityDrift d) r
  let Kt := Scaling.KineticAffineScaling.pushKernel
    (Scaling.KineticAffineScaling.mapsDomain_wholeSpace Φ) K
  let ρt := ρ.map (fun v => (Real.sqrt T)⁻¹ • v)
  have hBt := scaledCoefficient_sectionTwo lam Lam B hB σ₀ 0 r
  have hr := Scaling.realizes_ofRadius_wholeSpace σ₀ 0 0 r hreal
  have hPt := occupation_scaled_marginalBundle σ₀ r K hP
  obtain ⟨gt, hgt, hnorm⟩ := hunit (scaledCoefficient B σ₀ 0 r) hBt
    (Scaling.fiberOperator Kt MeasurableSet.univ) Kt hr hPt ρt
  let g := fun q => T ^ (-(d : ℝ) / 2) *
    gt (parabolicAffine 0 0 (Real.sqrt T)⁻¹ q)
  have hg := isOccupationDensity_scaled K σ₀ hT ρ gt hgt
  have hgeq : ∀ q, g q = T ^ (-(d : ℝ) / 2) *
      gt (q.1 / T, (Real.sqrt T)⁻¹ • q.2) := by
    intro q
    dsimp [g]
    congr 2
    apply Prod.ext
    · change 0 + (Real.sqrt T)⁻¹ ^ 2 * q.1 = q.1 / T
      rw [inv_pow, Real.sq_sqrt hT.le]
      simp only [zero_add, inv_mul_eq_div]
    · simp only [parabolicAffine, zero_add]
  refine ⟨g, gt, hg, hgt, hgeq, ?_⟩
  intro γ hγ0 hγ1
  obtain ⟨hmem, hbd⟩ := hnorm γ hγ0 hγ1
  have hmemg : MemLp g (ENNReal.ofReal γ)
      (volume.restrict (Ioo (0 : ℝ) T ×ˢ univ)) := by
    apply occupation_memLp_pullback 0 0 (inv_pos.mpr (Real.sqrt_pos.mpr hT))
    simpa only [occupation_inverseScaling_image_slab hT] using hmem
  have hnormeq : occupationLpNorm T γ g =
      T ^ occupationBeta d γ * occupationLpNorm 1 γ gt := by
    rw [show g = fun q => T ^ (-(d : ℝ) / 2) *
      gt (q.1 / T, (Real.sqrt T)⁻¹ • q.2) from funext hgeq]
    exact occupationLpNorm_scaledDensity hT (zero_le_one.trans hγ0) gt
  have hmass : (ρt univ).toReal = (ρ univ).toReal := by
    have hm : Measurable (fun v : PDE.Vec d => (Real.sqrt T)⁻¹ • v) :=
      (continuous_const_smul (Real.sqrt T)⁻¹).measurable
    change (ρ.map (fun v => (Real.sqrt T)⁻¹ • v) univ).toReal = _
    rw [Measure.map_apply hm MeasurableSet.univ, preimage_univ]
  refine ⟨hmemg, hmem, hnormeq, ?_⟩
  rw [hnormeq]
  rw [hmass] at hbd
  have hh := mul_le_mul_of_nonneg_left hbd
    (Real.rpow_nonneg hT.le (occupationBeta d γ))
  calc
    _ ≤ T ^ occupationBeta d γ * (C γ * (ρ univ).toReal) := hh
    _ = _ := by ring

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
