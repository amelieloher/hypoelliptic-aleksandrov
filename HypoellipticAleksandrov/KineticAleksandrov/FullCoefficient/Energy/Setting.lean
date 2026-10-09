module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Energy.Time

/-!
# The abstract setting of the energy inequality

The energy inequality. The energy inequality only uses the following
properties of the smoothed densities `ρ(τ, y)`, coefficients `β(τ, y)` and fluxes `J(τ, y)`,
on the time interval `(τ₁, τ₂)` and at fixed smoothing `h`; they are established for the smoothing
datum and for the Green measure in `Energy.Datum` and `Energy.Green`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory Matrix
open scoped MatrixOrder

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

/-- A non-zero slice: positive smooth density, smooth coefficient with `λ ≤ β`, flux `J = ρ β`,
the smoothed equation (in its integrated form) and the integrability of the smoothing estimates. -/
structure NonzeroSlice (lam h q : ℝ) (ρ dρ : EvolutionAmbientState d → ℝ)
    (β J : EvolutionAmbientState d → PDE.Mat d) : Prop where
  smooth_rho : ContDiff ℝ (⊤ : ℕ∞) ρ
  pos : ∀ y, 0 < ρ y
  smooth_beta : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) fun y => β y i j
  flux_eq : ∀ i j y, J y i j = ρ y * β y i j
  loewner : ∀ y, lam • (1 : PDE.Mat d) ≤ β y
  equation : ∀ y, dρ y + transportDerivative ρ y =
    lam * h ^ 2 / 2 * positionLaplacian ρ y - lam * h * mixedDivergence ρ y +
      ∑ i, ∑ j, velocityPartial i (velocityPartial j (fun y => J y i j)) y
  integrable : SliceIntegrable q ρ β J

/-- The setting of the energy inequality on `(τ₁, τ₂)` at smoothing `h`. -/
structure EnergySetting (lam h q τ₁ τ₂ : ℝ) (ρ : ℝ → EvolutionAmbientState d → ℝ)
    (β J : ℝ → EvolutionAmbientState d → PDE.Mat d) : Prop where
  lam_pos : 0 < lam
  one_lt : 1 < q
  lt : τ₁ < τ₂
  smooth_rho : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × EvolutionAmbientState d => ρ p.1 p.2)
  smooth_flux : ∀ i j, ContDiff ℝ (⊤ : ℕ∞)
    (fun p : ℝ × EvolutionAmbientState d => J p.1 p.2 i j)
  nonneg : ∀ τ y, 0 ≤ ρ τ y
  bounded : ∃ R₀, ∀ τ y, ρ τ y ≤ R₀
  time_dom : ∃ D : EvolutionAmbientState d → ℝ, Integrable D ∧
    ∀ τ y, |deriv (fun τ' => ρ τ' y) τ| ≤ D y
  pow_integrable : ∀ τ ∈ Set.Icc τ₁ τ₂, Integrable fun y => ρ τ y ^ q
  beta_meas : ∀ i j c, Measurable fun p : ℝ × EvolutionAmbientState d =>
    coordPartial c (fun y => β p.1 y i j) p.2
  slices : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Set.Ioo τ₁ τ₂, (∀ y, ρ τ y = 0) ∨
    (NonzeroSlice lam h q (ρ τ) (fun y => deriv (fun τ' => ρ τ' y) τ) (β τ) (J τ) ∧
      (∫ y, ρ τ y ^ (q - 1) * gradNorm (ρ τ) y) ≤ C ∧
      (∫ y, ρ τ y ^ (q - 1) * coefficientGradNorm (J τ) y) ≤ C)

/-- The weighted energy term `A_ζ(τ) = ∫ ζ ρ^{q-2} |Dρ|²_{M^h}`. -/
def energyA (lam h q : ℝ) (ρ : ℝ → EvolutionAmbientState d → ℝ)
    (ζ : EvolutionAmbientState d → ℝ) (τ : ℝ) : ℝ :=
  ∫ y, ζ y * (ρ τ y ^ (q - 2) * flowGamma lam h (ρ τ) (ρ τ) y)

/-- The weighted coefficient term `B_ζ(τ) = ∫ ζ ρ^q |Dβ|²_{M^h}`. -/
def energyB (lam h q : ℝ) (ρ : ℝ → EvolutionAmbientState d → ℝ)
    (β : ℝ → EvolutionAmbientState d → PDE.Mat d) (ζ : EvolutionAmbientState d → ℝ)
    (τ : ℝ) : ℝ :=
  ∫ y, ζ y * (ρ τ y ^ q * coefficientGammaSum lam h (β τ) y)

/-- The cut-off error term. -/
def energyG (lam h q : ℝ) (ρ : ℝ → EvolutionAmbientState d → ℝ)
    (J : ℝ → EvolutionAmbientState d → PDE.Mat d) (τ : ℝ) : ℝ :=
  |lam * h / 2| * (∫ y, ρ τ y ^ (q - 1) * gradNorm (ρ τ) y) +
    d * ∫ y, ρ τ y ^ (q - 1) * coefficientGradNorm (J τ) y

/-- The hypotheses of the slice energy inequality hold for a non-zero slice and a cut-off. -/
theorem NonzeroSlice.toSliceHyp {lam h q Bv ε : ℝ} {ρ dρ ζ : EvolutionAmbientState d → ℝ}
    {β J : EvolutionAmbientState d → PDE.Mat d} (hS : NonzeroSlice lam h q ρ dρ β J)
    (hlam : 0 < lam) (hq : 1 < q) (hε : 0 ≤ ε) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζ0 : ∀ y, 0 ≤ ζ y) (hζ1 : ∀ y, ζ y ≤ 1)
    (hinr : ∀ i y, coordPartial (Sum.inr i) ζ y = 0) (hBv : ∀ i y, |y.1 i * ζ y| ≤ Bv)
    (hinl : ∀ i y, |coordPartial (Sum.inl i) ζ y| ≤ ε) :
    SliceHyp lam h q Bv ε ρ dρ ζ β J :=
  ⟨hlam, hq, hε, hS.smooth_rho, hS.pos, hS.smooth_beta, hS.flux_eq, hS.loewner, hS.equation,
    hS.integrable, hζ, hζ0, hζ1, hinr, hBv, hinl⟩

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
