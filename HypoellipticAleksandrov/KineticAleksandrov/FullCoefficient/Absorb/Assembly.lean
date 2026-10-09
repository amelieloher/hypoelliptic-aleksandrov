module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Absorb.DensityGreen
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Realization
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Green
public import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem

/-!
# The Green density for full coefficients

The Green density estimate for a unit point mass.  The smoothed
slice densities of the flow family obey `∫∫ ρ_ε^q ≤ C₁ T^{1-2d(q-1)}` (`SmoothedLqBound`, the
output of the absorption estimate and of the passage to the limit), and the
duality argument (`greenDensity_of_smoothed_bound`) turns this into the Lebesgue
density with the constant `C = C₁^{1/q}`, independent of `Λ`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal

/-- The smoothing-time estimate of the absorption estimate after the limits `δ → 0`, `τ₁ ↓ 0`,
`τ₂ ↑ T`: for
every admissible coefficient and every `ε > 0`, `∫∫_{(0,T) × ℝ^{2d}} ρ_ε^q ≤ C₁ T^{1-2d(q-1)}`,
with `C₁` depending only on `d`, `λ`, `q`. -/
def SmoothedLqBound (d : ℕ) (lam q : ℝ) (hl : 0 < lam) : Prop :=
  ∃ C₁ : ℝ, 0 ≤ C₁ ∧
    ∀ (Lam : ℝ), lam ≤ Lam →
      q ≤ 1 + 3 * lam ^ 2 / (128 * (d : ℝ) ^ 2 * Lam ^ 2) →
    ∀ (B : FullKineticCoefficient d),
      IsSmoothFullKineticCoefficient B →
      IsSymmetricFullKineticCoefficient B →
      HasEverywhereLoewnerBounds lam Lam B →
    ∀ (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
      (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))),
      RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
        MeasurableSet.univ B (identityDrift d) S K →
    ∀ (σ₀ : ℝ) (p : EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀)
      (T : ℝ), 0 < T →
    ∀ ε : ℝ, 0 < ε →
      ∫⁻ x, ENNReal.ofReal
          (smoothDensity (flowKernelFamily (d := d) hl) ε (sliceMeasure K σ₀ p x.1) x.2 ^ q)
        ∂((elapsedVolume (ENNReal.ofReal T)).prod (volume : Measure (EvolutionAmbientState d))) ≤
        ENNReal.ofReal (C₁ * T ^ (1 - 2 * (d : ℝ) * (q - 1)))

/-- **The Green density bound for full coefficients, conditional on the smoothed bound.**
The conclusion is the Green density statement `exists_greenDensity_fullCoefficient`. -/
theorem exists_greenDensity_fullCoefficient_of_smoothedLqBound
    (d : ℕ) (hd : 1 ≤ d) (lam q : ℝ) (hlam : 0 < lam) (hq : 1 < q)
    (hbound : SmoothedLqBound d lam q hlam) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Lam : ℝ), lam ≤ Lam →
        q ≤ 1 + 3 * lam ^ 2 / (128 * (d : ℝ) ^ 2 * Lam ^ 2) →
      ∀ (B : FullKineticCoefficient d),
        IsSmoothFullKineticCoefficient B →
        IsSymmetricFullKineticCoefficient B →
        HasEverywhereLoewnerBounds lam Lam B →
      ∀ (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
        (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))),
        RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          MeasurableSet.univ B (identityDrift d) S K →
      ∀ (σ₀ : ℝ) (p : EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀)
        (T : ℝ), 0 < T →
      ∀ (Γ : Measure (ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d)),
        IsGreenMeasure K σ₀ (ENNReal.ofReal T) (Measure.dirac p) Γ →
        ∃ G : ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d → ℝ≥0∞,
          Measurable G ∧
          Γ = ((elapsedVolume (ENNReal.ofReal T)).prod
            (volume : Measure (EvolutionAmbientState d))).withDensity G ∧
          eLpNorm G (ENNReal.ofReal q) ((elapsedVolume (ENNReal.ofReal T)).prod
            (volume : Measure (EvolutionAmbientState d))) ≤
            ENNReal.ofReal (C * T ^ ((1 - 2 * (d : ℝ) * (q - 1)) / q)) := by
  obtain ⟨C₁, hC₁, hb⟩ := hbound
  refine ⟨C₁ ^ (1 / q), Real.rpow_nonneg hC₁ _, ?_⟩
  intro Lam hLam hqLam B hB1 hB2 hB3 S K hK σ₀ p T hT Γ hΓ
  exact greenDensity_of_smoothed_bound hlam K σ₀ p hT Γ hΓ hq hC₁
    (hb Lam hLam hqLam B hB1 hB2 hB3 S K hK σ₀ p T hT)

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
