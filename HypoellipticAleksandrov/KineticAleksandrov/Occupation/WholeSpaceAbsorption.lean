module

public import Mathlib.Topology.Order.Real
public import Mathlib.Tactic.Linarith

/-!
# Supremum absorption in the whole-space occupation estimate

This elementary lemma is the final algebraic step after the localized comparison.
It does not assert that comparison for the occupation potential.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open Set

/-- A uniform half-supremum bound absorbs to twice the source bound. -/
theorem wholeSpace_absorb {α : Type*} {A : Set α} {W : α → ℝ} {M : ℝ}
    (hne : A.Nonempty)
    (hpoint : ∀ x ∈ A, W x ≤ M + sSup (W '' A) / 2) :
    sSup (W '' A) ≤ 2 * M := by
  have hsup : sSup (W '' A) ≤ M + sSup (W '' A) / 2 := by
    apply csSup_le (hne.image W)
    rintro _ ⟨x, hx, rfl⟩
    exact hpoint x hx
  linarith only [hsup]

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
