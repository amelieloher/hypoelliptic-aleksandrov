module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Absorb.Final
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Realization
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Green
public import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Green density for coefficients depending on time, velocity and position

Proved by the adjoint-smoothing argument of https://weneedabp.github.io/, for a
unit point mass. In case (W) of the terminal solution operator (whole space, identity
drift), with a smooth symmetric
coefficient `B(σ,v,z)` obeying `λ I ≤ B ≤ Λ I` everywhere, the Green measure over a horizon
`T` from a unit point mass has a Lebesgue density on `(0,T) × ℝ^d × ℝ^d` whose `L^q` norm is
at most `C T^{(1-2d(q-1))/q}`, for every `1 < q ≤ q_* = 1 + 3λ²/(128 d² Λ²)`, with `C`
depending only on `d`, `λ`, `q`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

/-- The Green density bound for full coefficients. The constant depends only on `d`, `λ`, `q`: it
is fixed before the upper ellipticity bound `Λ` (which enters only through `q ≤ q_*`), the
coefficient, the realizing evolution, the start point and the horizon. -/
theorem exists_greenDensity_fullCoefficient
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
            ENNReal.ofReal (C * T ^ ((1 - 2 * (d : ℝ) * (q - 1)) / q)) := by
  exact HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.greenDensity_aux
    d hd lam q hlam hq

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
