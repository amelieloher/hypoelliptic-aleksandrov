module

public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.SmoothEstimate
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.SmoothEstimateSource
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.LocalisedSource
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.Borel

/-! # Localized time--velocity estimate from slab Fourier bounds

The explicit inputs are Hörmander, the case-W slab Fourier family bound, and the
whole-space supplied-evolution conclusion, retaining its shared witnesses and source clauses.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set MeasureTheory SectionTwo Green Parabolic TheoremA
open scoped ENNReal NNReal MatrixOrder

/-- The localized conclusion with the smooth slab and evolution inputs discharged downstream. -/
theorem kinetic_aleksandrov_timeVelocity_localised_of_slabFourierBounds
    (d : ℕ) (hd : 1 ≤ d) (lam Lam p : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (hp : 2 * (d : ℝ) + 1 < p)
    (hH : HormanderHypoellipticityStatement)
    (hbounds : ∃ (C : ℝ → ℝ≥0) (c : ℝ), ∀ (B : CoefficientField d),
      IsSectionTwoCoefficient lam Lam B →
      ∀ (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
        (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))),
      RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d)) MeasurableSet.univ
        (zIndependentCoefficient B) (identityDrift d) S K →
      ∀ (σ₀ : ℝ) (μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀))
        [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier d)), IsGreenMeasure K σ₀ ⊤ μ Γ →
      ∀ T : ℝ, 0 < T → SlabFourierBounds d C c (μ univ) T Γ)
    (hevolution : ∀ B : CoefficientField d, IsSectionTwoCoefficient lam Lam B →
      ∃ (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
        (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))),
        RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d)) MeasurableSet.univ
          (zIndependentCoefficient B) (identityDrift d) S K ∧
        (∀ (hBz : ∀ (σ : ℝ) (y z z' : PDE.Vec d),
          (zIndependentCoefficient B) σ y z = (zIndependentCoefficient B) σ y z'),
          let _ := hBz
          IsTranslationCovariantEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
            MeasurableSet.univ K) ∧
        IsDomainMonotoneEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          (zIndependentCoefficient B) (identityDrift d) K ∧
        HasParabolicMarginalBundle (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          MeasurableSet.univ (zIndependentCoefficient B) K) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
      ∀ (A : CoefficientField d),
        IsBorelCoefficient A → IsSymmetricCoefficient A →
        HasLowerEllipticityAE lam A → HasUpperEllipticityAE Lam A →
      ∀ (f u : KineticPoint d → ℝ),
        Measurable (fun P : backwardCylinder P₀ R => f P) →
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        Parabolic.IsKineticC112On u (backwardCylinder P₀ R) →
        (∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
          backwardOperatorOfTimeVelocityCoefficient A u P ≤ f P) →
        MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
          (volume.restrict (backwardCylinder P₀ R)) →
        ∀ P ∈ closure (backwardCylinder P₀ R),
          u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
            C * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
              (eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0))
                (ENNReal.ofReal p)
                (volume.restrict (backwardCylinder P₀ R))).toReal := by
  have he : ∀ B : CoefficientField d, IsSectionTwoCoefficient lam Lam B →
      ∃ (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
        (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))),
        RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d)) MeasurableSet.univ
          (zIndependentCoefficient B) (identityDrift d) S K := by
    intro B hB
    obtain ⟨S, K, hreal, hcov, hmono, hpar⟩ := hevolution B hB
    have _ := hcov
    have _ := hmono
    have _ := hpar
    exact ⟨S, K, hreal⟩
  obtain ⟨C, hC, hsmooth⟩ := smooth_estimate_of_slabFourierBounds hd lam Lam p
    hlam hLam hp hH hbounds he
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hp1 : 1 ≤ p := by linarith
  have hfull : ∀ A : CoefficientField d,
      IsSmoothCoefficient A → IsSymmetricCoefficient A →
      HasLowerEllipticity lam A → HasUpperEllipticity Lam A →
      ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
      ∀ u f : KineticPoint d → ℝ,
      ContinuousOn u (closure (backwardCylinder P₀ R)) →
      IsKineticC112On u (backwardCylinder P₀ R) → Measurable f →
      MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₀ R)) →
      (∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
        backwardOperatorOfTimeVelocityCoefficient A u P ≤ f P) →
      ∀ P ∈ closure (backwardCylinder P₀ R), u P ≤
        sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
          C * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
            (eLpNorm (borelSource true u f) (ENNReal.ofReal p)
              (volume.restrict (backwardCylinder P₀ R))).toReal := by
    intro A hAs hsym hlo hhi P₀ R hR u f hc hr hf hLp hsub P hP
    have hloAE : HasLowerEllipticityAE lam A :=
      Filter.Eventually.of_forall (fun z => hlo z.1 z.2)
    have hhiAE : HasUpperEllipticityAE Lam A :=
      Filter.Eventually.of_forall (fun z => hhi z.1 z.2)
    simpa only [borelSource, ite_true] using
      hsmooth A hAs hsym hloAE hhiAE P₀ R hR u f hc hr hf hLp hsub P hP
  refine ⟨C, hC, ?_⟩
  intro P₀ R hR A hBorel hsym hlo hhi f u hf hc hr hsub hLp P hP
  have hQ := (isOpen_backwardCylinder P₀ R hR).measurableSet
  let f₀ := (backwardCylinder P₀ R).indicator f
  have hf₀ : Measurable f₀ := measurable_source_indicator hQ f hf
  have hae := source_indicator_ae_eq hQ f
  have hmax : (fun P => max (f P) 0) =ᵐ[volume.restrict (backwardCylinder P₀ R)]
      (fun P => max (f₀ P) 0) := by
    filter_upwards [hae] with P hP
    change max (f P) 0 = max ((backwardCylinder P₀ R).indicator f P) 0
    rw [hP]
  have hLp₀ := hLp.ae_eq hmax
  have hsub₀ : ∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
      backwardOperatorOfTimeVelocityCoefficient A u P ≤ f₀ P := by
    filter_upwards [hsub, hae] with P hsub hEq
    change backwardOperatorOfTimeVelocityCoefficient A u P ≤
      (backwardCylinder P₀ R).indicator f P
    rw [hEq]
    exact hsub
  have hbound := kinetic_abp_smooth_to_borel lam Lam hlam hLam p hp1
    (2 - (4 * (d : ℝ) + 2) / p) C true hfull A hBorel hsym hlo hhi
    P₀ R hR u f₀ hc hr hf₀ hLp₀ hsub₀ P hP
  simpa only [f₀, borelSource, ite_true,
    eLpNorm_localized_source_indicator hQ f u] using hbound

end HypoellipticAleksandrov.KineticAleksandrov
