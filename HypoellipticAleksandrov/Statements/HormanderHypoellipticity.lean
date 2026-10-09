module

public import HypoellipticAleksandrov.KineticAleksandrov.HormanderBridge
public import HypoellipticAleksandrov.KineticAleksandrov.Hormander

/-!
# Hörmander's hypoellipticity theorem

Let `L = Σ Xᵢ² + X₀ + c` be built from smooth vector fields whose Lie algebra spans at every
point of an open set, and let `u` be a locally integrable weak solution of `L u = g` with
smooth `c, g`. Then `u` agrees almost everywhere with a smooth function. The proof is by
the `hormander` package.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov
open scoped BigOperators

namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The locally integrable Hörmander regularity statement. -/
theorem exists_smooth_aeRepresentative_of_hormander
    {k N : ℕ} {Ω : Set (PDE.Vec N)}
    (hΩ : IsOpen Ω)
    (X : Fin (k + 1) → PDE.Vec N → PDE.Vec N)
    (c g u : PDE.Vec N → ℝ)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hspan : LieAlgebraSpansOn Ω X)
    (hc : ContDiffOn ℝ (⊤ : ℕ∞) c Ω)
    (hEq : HasWeakHormanderEquation Ω X c g u) :
    ∃ f : PDE.Vec N → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) f Ω ∧
        u =ᵐ[Measure.restrict volume Ω] f := by
  exact HypoellipticAleksandrov.KineticAleksandrov.exists_smooth_aeRepresentative_of_hormander_aux
    hΩ X c g u hX hspan hc hEq

end HypoellipticAleksandrov.KineticAleksandrov
