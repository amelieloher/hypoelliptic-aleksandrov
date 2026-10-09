module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Assembly
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Setting
public import HypoellipticAleksandrov.Coefficients.Ellipticity
public import Mathlib.Analysis.Matrix.MeasurableSpace

/-!
# The Aleksandrov principle implies Hölder continuity

Companion paper, Theorem 9.1. This implication requires no further theorem as a premise.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open Set MeasureTheory Holder
open scoped ENNReal MatrixOrder

/-- Companion paper, Theorem 9.1, uniform over full coefficients and all solution/domain data. -/
theorem kinetic_holder_of_aleksandrov
    (d : ℕ) (hd : 1 ≤ d) (lam Lam p C_A : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (hp : 1 ≤ p) :
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧
      ∀ A : FullKineticCoefficient d,
        Measurable (fullKineticCoefficientAt A) →
        (∀ P : KineticPoint d, (fullKineticCoefficientAt A P).IsSymm) →
        (∀ᵐ P ∂(volume : Measure (KineticPoint d)),
          lam • (1 : PDE.Mat d) ≤ fullKineticCoefficientAt A P) →
        (∀ᵐ P ∂(volume : Measure (KineticPoint d)),
          fullKineticCoefficientAt A P ≤ Lam • (1 : PDE.Mat d)) →
      ∀ (Omega : Set (KineticPoint d)), IsOpen Omega →
      ∀ (u : KineticPoint d → ℝ),
        (∃ M : ℝ, ∀ P ∈ Omega, |u P| ≤ M) →
        IsAdmissibleSolution A Omega p C_A u →
      ∀ (K : Set (KineticPoint d)), K ⊆ Omega → IsCompact K →
      ∀ (R₀ : ℝ), 0 < R₀ →
        (∀ P ∈ K, closure (backwardCylinder P (2 * R₀)) ⊆ Omega) →
      ∀ P ∈ K, ∀ P' ∈ K,
        |u P - u P'| ≤ C * oscillationOn u (holderNeighbourhood R₀ K) *
          (quasiDistance P P' / R₀) ^ alpha := by
  exact HypoellipticAleksandrov.KineticAleksandrov.kinetic_holder_of_aleksandrov_aux
    d hd lam Lam p C_A hlam hLam hp

end HypoellipticAleksandrov.KineticAleksandrov
