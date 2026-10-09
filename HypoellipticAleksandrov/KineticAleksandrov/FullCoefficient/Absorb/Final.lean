module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Absorb.SmoothedLq

/-!
# The Green density for full coefficients

The proof of the Green density estimate for a unit point mass: the duality argument
(`exists_greenDensity_fullCoefficient_of_smoothedLqBound`) applied to the smoothed bound
(`smoothedLqBound_holds`).
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal

/-- **The Green density bound for full coefficients**: the proof of
`exists_greenDensity_fullCoefficient`. -/
theorem greenDensity_aux
    (d : ℕ) (hd : 1 ≤ d) (lam q : ℝ) (hlam : 0 < lam) (hq : 1 < q) :
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
            ENNReal.ofReal (C * T ^ ((1 - 2 * (d : ℝ) * (q - 1)) / q)) :=
  exists_greenDensity_fullCoefficient_of_smoothedLqBound d hd lam q hlam hq
    (smoothedLqBound_holds hd lam q hlam hq)

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
