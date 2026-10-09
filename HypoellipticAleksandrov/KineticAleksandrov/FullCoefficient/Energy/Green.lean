module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Energy.DatumMain
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothed.Green

/-!
# The energy inequality for the Green measure

The energy inequality, for the Green measure of a point mass and the flow
kernel `flowKernelFamily`; no premise of the smoothed equation remains.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory Set
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal

variable {d : ℕ} {lam Lam T : ℝ}

/-- **The energy inequality for the Green measure**, with `ρ = greenDensity`
and `β_h = greenBeta`, for `1 < q`, `h > 0` and `δ < τ₁ < τ₂ < T - δ`. -/
theorem energy_inequality_green (hd : 1 ≤ d) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : FullKineticCoefficient d) (hB : IsSmoothFullKineticCoefficient B)
    (hBs : IsSymmetricFullKineticCoefficient B) (hell : HasEverywhereLoewnerBounds lam Lam B)
    (S : TerminalOperatorFamily (wholeSpace d) (fun _ => 0))
    (K : MovingFiberKernel (wholeSpace d) (fun _ => 0))
    (hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ B
      (identityDrift d) S K)
    (σ₀ : ℝ) (hT : 0 < T) (p : EvolutionState (wholeSpace d) (fun _ => 0) σ₀)
    (Γ : Measure (ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d))
    (hΓ : IsGreenMeasure K σ₀ (ENNReal.ofReal T) (Measure.dirac p) Γ)
    {δ : ℝ} {η : ℝ → ℝ} (hη : IsMollifier δ η) {h q τ₁ τ₂ : ℝ} (hh : 0 < h) (hδ : 0 < δ)
    (hq : 1 < q) (hτ : τ₁ < τ₂) (hτ₁ : δ < τ₁) (hτ₂ : τ₂ + δ < T) :
    ENNReal.ofReal (q * (q - 1) / 4) *
        ∫⁻ τ in Set.Ioo τ₁ τ₂, ∫⁻ y, ENNReal.ofReal (greenDensity hlam η h Γ τ y ^ (q - 2) *
          flowGamma lam h (greenDensity hlam η h Γ τ) (greenDensity hlam η h Γ τ) y) ≤
      (∫⁻ y, ENNReal.ofReal (greenDensity hlam η h Γ τ₁ y ^ q)) +
        ENNReal.ofReal (4 * d * q * (q - 1) / lam ^ 2) *
          ∫⁻ τ in Set.Ioo τ₁ τ₂, ∫⁻ y, ENNReal.ofReal (greenDensity hlam η h Γ τ y ^ q *
            coefficientGammaSum lam h (greenBeta hlam η B σ₀ Lam h Γ τ) y) := by
  have : IsFiniteMeasure Γ := isFiniteMeasure_green K σ₀ hT p Γ hΓ
  exact energy_inequality_datum (flowKernelFamily hlam) hη
    (isSmoothingDatum_green hlam hLam B hB hBs hell σ₀ Γ
      (fun A hA => green_prod_fst_le K σ₀ (ENNReal.ofReal T) p Γ hΓ A hA)) hh hδ hq hτ hτ₁ hτ₂
    (isForwardMeasure_green hd hlam hLam B hB hBs hell S K hreal σ₀ hT p Γ hΓ)
    (fun w => transportDerivative_flowKernel hlam hh w)

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
