module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationScalingAssembly
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationDensityConsumer
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.Duality
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationDensityEvolution

/-! # Occupation assembly and the exact slab consumer -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic SectionTwo MeasureTheory Set
open scoped ENNReal
variable {d : ℕ}

/-- Forget the scaled representative after scaling the unit-time duality theorem. -/
theorem occupation_of_duality (lam Lam : ℝ) (hDuality :
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
            occupationLpNorm 1 γ g ≤ C γ * (ρ univ).toReal) :
    ∃ C : ℝ → ℝ,
      (∀ γ, 1 ≤ γ → γ ≤ ((d : ℝ) + 1) / d → 0 ≤ C γ) ∧
      ∀ (B : CoefficientField d) (_hB : IsSectionTwoCoefficient lam Lam B)
        (S : WholeFamily d) (K : WholeKernel d)
        (_hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          MeasurableSet.univ (zIndependentCoefficient B) (identityDrift d) S K)
        (_hP : HasParabolicMarginalBundle (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          MeasurableSet.univ (zIndependentCoefficient B) K)
        (ρ : Measure (PDE.Vec d)) [IsFiniteMeasure ρ]
        (σ₀ T : ℝ) (_hT : 0 < T),
        ∃ g : TimeVelocity d → ℝ, IsOccupationDensity K σ₀ T ρ g ∧
          ∀ γ, 1 ≤ γ → γ ≤ ((d : ℝ) + 1) / d →
            MemLp g (ENNReal.ofReal γ)
              (volume.restrict (Ioo (0 : ℝ) T ×ˢ univ)) ∧
            occupationLpNorm T γ g ≤
              C γ * (ρ univ).toReal * T ^ occupationBeta d γ := by
  obtain ⟨C, hC0, hscale⟩ := occupation_scaling_of_duality lam Lam hDuality
  refine ⟨C, hC0, ?_⟩
  intro B hB S K hreal hP ρ _ σ₀ T hT
  obtain ⟨g, gt, hg, -, -, hb⟩ := hscale B hB S K hreal hP ρ σ₀ T hT
  refine ⟨g, hg, ?_⟩
  intro γ hγ0 hγ1
  exact ⟨(hb γ hγ0 hγ1).1, (hb γ hγ0 hγ1).2.2.2⟩

/-- The whole-space occupation theorem with all its original premises. -/
theorem occupation
    (hH : HormanderHypoellipticityStatement)
    (hd : 0 < d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ → ℝ,
      (∀ γ, 1 ≤ γ → γ ≤ ((d : ℝ) + 1) / d → 0 ≤ C γ) ∧
      ∀ (B : CoefficientField d) (_hB : IsSectionTwoCoefficient lam Lam B)
        (S : WholeFamily d) (K : WholeKernel d)
        (_hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          MeasurableSet.univ (zIndependentCoefficient B) (identityDrift d) S K)
        (_hP : HasParabolicMarginalBundle (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          MeasurableSet.univ (zIndependentCoefficient B) K)
        (ρ : Measure (PDE.Vec d)) [IsFiniteMeasure ρ]
        (σ₀ T : ℝ) (_hT : 0 < T),
        ∃ g : TimeVelocity d → ℝ, IsOccupationDensity K σ₀ T ρ g ∧
          ∀ γ, 1 ≤ γ → γ ≤ ((d : ℝ) + 1) / d →
            MemLp g (ENNReal.ofReal γ)
              (volume.restrict (Ioo (0 : ℝ) T ×ˢ univ)) ∧
            occupationLpNorm T γ g ≤
              C γ * (ρ univ).toReal * T ^ occupationBeta d γ := by
  exact occupation_of_duality lam Lam (occupation_duality hH hd lam Lam hlam hLam)

/-- The occupation family, relative to the terminal evolution statement and Hörmander's theorem. -/
theorem parabolicOccupationFamily_holds (hEvol : TerminalEvolutionStatement)
    (hH : HormanderHypoellipticityStatement)
    (hd : 0 < d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    Green.ParabolicOccupationFamily d lam Lam := by
  obtain ⟨C, hC0, hocc⟩ := occupation hH hd lam Lam hlam hLam
  refine ⟨C, ?_⟩
  intro B hB S K hreal
  refine ⟨hC0, ?_⟩
  intro ρ _ σ₀ T hT
  have hP := wholeSpace_marginalBundle_of_evolution hEvol hd hB S K hreal
  obtain ⟨g, hg, hb⟩ := hocc B hB S K hreal hP ρ σ₀ T hT
  refine ⟨g, (isOccupationDensity_iff_slabOccupationDensity K σ₀ T ρ g).mp hg, ?_⟩
  intro γ hγ0 hγ1
  exact hb γ hγ0 hγ1

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
