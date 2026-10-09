module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Integrands

/-!
# The smoothing estimates: integrability of the list, with uniform bounds

Assembles the pointwise bounds of `Targets` into integrability statements for the ten integrands
of `Integrands`, and then the uniformity in `m` (through its mass) and locally in `h`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {lam Lam : ℝ} {Φ : SmoothingKernelFamily d lam} {h : ℝ}
  {F : EvolutionAmbientState d → PDE.Mat d} {m : Measure (EvolutionAmbientState d)} {q : ℝ}

/-- `T` is integrable with integral at most `C`. -/
def IntegrableBy (T : EvolutionAmbientState d → ℝ) (C : ℝ) : Prop :=
  Integrable T ∧ ∫ y, T y ≤ C

/-- All ten integrands of the smoothing estimates are integrable, with integral at most `C`. -/
structure PackageIntegrable (Φ : SmoothingKernelFamily d lam) (h : ℝ)
    (F : EvolutionAmbientState d → PDE.Mat d) (m : Measure (EvolutionAmbientState d)) (q C : ℝ) :
    Prop where
  pow : IntegrableBy (integrandPow Φ h m q) C
  powBeta : IntegrableBy (integrandPowBeta Φ h F m q) C
  grad : IntegrableBy (integrandGrad Φ h m q) C
  hess : IntegrableBy (integrandHess Φ h m q) C
  fisher : IntegrableBy (integrandFisher Φ h m q) C
  betaGrad : IntegrableBy (integrandBetaGrad Φ h F m q) C
  fluxGrad : IntegrableBy (integrandFluxGrad Φ h F m q) C
  fluxHess : IntegrableBy (integrandFluxHess Φ h F m q) C
  fluxFisher : IntegrableBy (integrandFluxFisher Φ h F m q) C
  mixed : IntegrableBy (integrandMixed Φ h F m q) C

theorem PackageIntegrable.mono {C C' : ℝ} (hP : PackageIntegrable Φ h F m q C) (hC : C ≤ C') :
    PackageIntegrable Φ h F m q C' :=
  ⟨⟨hP.pow.1, hP.pow.2.trans hC⟩, ⟨hP.powBeta.1, hP.powBeta.2.trans hC⟩,
    ⟨hP.grad.1, hP.grad.2.trans hC⟩, ⟨hP.hess.1, hP.hess.2.trans hC⟩,
    ⟨hP.fisher.1, hP.fisher.2.trans hC⟩, ⟨hP.betaGrad.1, hP.betaGrad.2.trans hC⟩,
    ⟨hP.fluxGrad.1, hP.fluxGrad.2.trans hC⟩, ⟨hP.fluxHess.1, hP.fluxHess.2.trans hC⟩,
    ⟨hP.fluxFisher.1, hP.fluxFisher.2.trans hC⟩, ⟨hP.mixed.1, hP.mixed.2.trans hC⟩⟩

/-- The sum of the coefficients in the ten pointwise bounds of `Targets`. -/
def pkgCoefSum (d : ℕ) (Lam q C1 C2 Cfi R : ℝ) : ℝ :=
  R ^ (q - 1) * (1 + d * Lam ^ 2 + (2 * d + 1) * |C1| + ((2 * d) ^ 2 + 1) * |C2| + Cfi +
    (1 + 4 * d ^ 2 * Lam ^ 2 * Cfi) / 2 + (d ^ 2 * (2 * d) + 1) * Lam * |C1| +
    (d ^ 2 * (2 * d) ^ 2 + 1) * Lam * |C2| + d ^ 2 * Lam ^ 2 * Cfi + 2 * d * Lam * Cfi)

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
