module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Final
public import HypoellipticAleksandrov.KineticAleksandrov.Geometry
public import HypoellipticAleksandrov.KineticAleksandrov.Operator
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import HypoellipticAleksandrov.Geometry.KineticPointMeasure
public import HypoellipticAleksandrov.Coefficients.Ellipticity
public import Mathlib.Analysis.Matrix.MeasurableSpace

/-!
# Kinetic Aleksandrov estimate for coefficients depending on time, position and velocity

Proved by the adjoint-smoothing argument of https://weneedabp.github.io/, in
localized form. For a Borel symmetric
coefficient `A(t,x,v)` with `λ I ≤ A ≤ Λ I` almost everywhere and every exponent
`p ≥ p_* = 1 + (128 d²/3)(Λ/λ)²`, a subsolution `P_A u ≤ f` on a backward kinetic cylinder
is bounded by its positive part on the kinetic boundary plus `C R^{2-(4d+2)/p}` times the
`L^p` norm of `f₊` on the positivity set of `u`, with `C` depending only on `d, λ, Λ, p`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal MatrixOrder

namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The kinetic Aleksandrov estimate for full coefficients, localized to the positivity set,
with the uniform constant quantified before the data. -/
theorem kinetic_aleksandrov_fullCoefficient
    (d : ℕ) (hd : 1 ≤ d) (lam Lam p : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hp : 1 + 128 * (d : ℝ) ^ 2 * (Lam / lam) ^ 2 / 3 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
      ∀ (A : FullKineticCoefficient d),
        Measurable (fullKineticCoefficientAt A) →
        (∀ P : KineticPoint d, (fullKineticCoefficientAt A P).IsSymm) →
        (∀ᵐ P ∂(volume : Measure (KineticPoint d)),
          lam • (1 : PDE.Mat d) ≤ fullKineticCoefficientAt A P) →
        (∀ᵐ P ∂(volume : Measure (KineticPoint d)),
          fullKineticCoefficientAt A P ≤ Lam • (1 : PDE.Mat d)) →
      ∀ (f u : KineticPoint d → ℝ),
        Measurable (fun P : backwardCylinder P₀ R => f P) →
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        Parabolic.IsKineticC112On u (backwardCylinder P₀ R) →
        (∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
          backwardOperator A u P ≤ f P) →
        MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
          (volume.restrict (backwardCylinder P₀ R)) →
        ∀ P ∈ closure (backwardCylinder P₀ R),
          u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
            C * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
              (eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0)) (ENNReal.ofReal p)
                (volume.restrict (backwardCylinder P₀ R))).toReal := by
  exact HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.aleksandrov_aux
    d hd lam Lam p hlam hLam hp

end HypoellipticAleksandrov.KineticAleksandrov
