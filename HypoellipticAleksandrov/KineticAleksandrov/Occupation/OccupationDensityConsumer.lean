module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierPremises

/-!
# Exact identification with the slab consumer's occupation predicates

These are definitional identifications only. They supply no density existence,
no norm bound, and no marginal-bundle derivation.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set

/-- The density characterization is exactly the slab consumer's predicate. -/
theorem isOccupationDensity_iff_slabOccupationDensity {d : ℕ} (K : WholeKernel d)
    (σ₀ T : ℝ) (ρ : Measure (PDE.Vec d)) (g : ℝ × PDE.Vec d → ℝ) :
    IsOccupationDensity K σ₀ T ρ g ↔ Green.SlabOccupationDensity K σ₀ T ρ g := by
  rfl

/-- The source scaling exponent is exactly the exponent used by the consumer. -/
theorem occupationBeta_eq_slabBeta (d : ℕ) (γ : ℝ) :
    occupationBeta d γ = Green.slabBeta d γ := by
  rfl

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
