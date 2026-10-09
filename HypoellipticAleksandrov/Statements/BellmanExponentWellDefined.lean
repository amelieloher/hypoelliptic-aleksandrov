module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.ExponentWellDefined
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.ExponentSetting

/-!
# Well-definedness of the homogeneous adjoint exponent

Companion paper, Appendix B: the supremum of the admissible degrees is a unique real least
upper bound.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

/-- Well-definedness: the supremum is a unique real least upper bound.
Nonemptiness and boundedness are proof steps, never additional hypotheses. -/
theorem existsUnique_bellmanAdjointExponent (ratio : ℝ) (hRatio : 1 ≤ ratio) :
    ∃! β : ℝ, IsLUB (bellmanAdmissibleDegrees ratio) β := by
  exact HypoellipticAleksandrov.KineticAleksandrov.existsUnique_bellmanAdjointExponent_aux
    ratio hRatio

end HypoellipticAleksandrov.KineticAleksandrov
