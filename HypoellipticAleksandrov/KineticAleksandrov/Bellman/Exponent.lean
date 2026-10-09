module

public import HypoellipticAleksandrov.Statements.BellmanExponentWellDefined

/-! # The homogeneous adjoint exponent

Definition of β_* (companion paper, Appendix B) as the unique real
least upper bound of the admissible normalized degrees, chosen from the
well-definedness theorem, together with its full characterization.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set

/-- The unique real supremum of the source's admissible normalized adjoint degrees. -/
def bellmanAdjointExponent (ratio : ℝ) (hRatio : 1 ≤ ratio) : ℝ :=
  (existsUnique_bellmanAdjointExponent ratio hRatio).choose

/-- Full characteristic property and uniqueness of the same chosen real exponent.
This does not assert that the supremal degree is attained by an admissible pair. -/
theorem bellmanAdjointExponent_characterization (ratio : ℝ) (hRatio : 1 ≤ ratio) :
    IsLUB (bellmanAdmissibleDegrees ratio) (bellmanAdjointExponent ratio hRatio) ∧
      ∀ β : ℝ, IsLUB (bellmanAdmissibleDegrees ratio) β →
        β = bellmanAdjointExponent ratio hRatio := by
  exact (existsUnique_bellmanAdjointExponent ratio hRatio).choose_spec

end HypoellipticAleksandrov.KineticAleksandrov
