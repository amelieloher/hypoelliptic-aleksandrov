module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HighDegreeExclusion
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureStationary
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! # The unique real supremum of genuine Bellman adjoint degrees -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- Proof of the existence and uniqueness of the real least upper bound. -/
theorem existsUnique_bellmanAdjointExponent_aux (ratio : ℝ) (hRatio : 1 ≤ ratio) :
    ∃! β : ℝ, IsLUB (bellmanAdmissibleDegrees ratio) β := by
  have hn : (bellmanAdmissibleDegrees ratio).Nonempty :=
    ⟨2, two_mem_bellmanAdmissibleDegrees ratio hRatio⟩
  have hb : BddAbove (bellmanAdmissibleDegrees ratio) :=
    ⟨3, fun β hβ => (admissible_degree_lt_three ratio hRatio β hβ).le⟩
  have hsup := isLUB_csSup hn hb
  exact ⟨sSup (bellmanAdmissibleDegrees ratio), hsup, fun _ h => h.unique hsup⟩

end HypoellipticAleksandrov.KineticAleksandrov
