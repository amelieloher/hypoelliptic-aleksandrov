module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Final
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Setting
public import HypoellipticAleksandrov.Coefficients.Ellipticity
public import Mathlib.Analysis.Matrix.MeasurableSpace

/-!
# Interior Hölder estimate for coefficients depending on time, position and velocity

Proved by the adjoint-smoothing argument of https://weneedabp.github.io/. For a
Borel symmetric coefficient `A(t,x,v)` with `λ I ≤ A ≤ Λ I` almost everywhere, a bounded
`C^{1,1,2}` solution of
`P_A u = 0` almost everywhere on an open set is Hölder continuous on every compact set whose
doubled backward cylinders stay in the open set, with exponent and constant depending only on
`d, λ, Λ`, in the kinetic quasi-distance and relative to the oscillation on the neighbourhood.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal MatrixOrder

namespace HypoellipticAleksandrov.KineticAleksandrov

open Holder

/-- The interior Hölder estimate for full coefficients. -/
theorem kinetic_holder_fullCoefficient
    (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
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
        Parabolic.IsKineticC112On u Omega →
        (∀ᵐ P ∂(volume.restrict Omega), backwardOperator A u P = 0) →
      ∀ (K : Set (KineticPoint d)), K ⊆ Omega → IsCompact K →
      ∀ (R₀ : ℝ), 0 < R₀ →
        (∀ P ∈ K, closure (backwardCylinder P (2 * R₀)) ⊆ Omega) →
      ∀ P ∈ K, ∀ P' ∈ K,
        |u P - u P'| ≤ C * oscillationOn u (holderNeighbourhood R₀ K) *
          (quasiDistance P P' / R₀) ^ alpha := by
  exact HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.holder_aux
    d hd lam Lam hlam hLam

end HypoellipticAleksandrov.KineticAleksandrov
