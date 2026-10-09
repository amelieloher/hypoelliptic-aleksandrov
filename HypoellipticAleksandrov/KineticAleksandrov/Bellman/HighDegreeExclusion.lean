module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularAnnihilationOffAxis
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AxisAnnihilation

/-! # Exclusion of every admissible density degree at least three -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- Every degree of a genuine normalized stationary homogeneous Radon pair is below three. -/
theorem admissible_degree_lt_three (R : ℝ) (hR : 1 ≤ R) (β : ℝ)
    (hβ : β ∈ bellmanAdmissibleDegrees R) : β < 3 := by
  by_contra hn
  have hge : 3 ≤ β := le_of_not_gt hn
  obtain ⟨μ, η, hp⟩ := (mem_bellmanAdmissibleDegrees_iff R β).mp hβ
  have haxis := adjoint_vanishes_off_position_axis R β hR hge μ η hp
  have hlo : μ ≤ η := by
    simpa only [ENNReal.ofReal_one, one_smul] using hp.2.2.2.1
  obtain ⟨hμ, _⟩ := stationary_axis_pair_eq_zero R hR μ η hp.1 hp.2.1 hlo
    hp.2.2.2.2.1 hp.2.2.2.2.2.1 haxis.1
  exact hp.left_ne_zero hμ

end HypoellipticAleksandrov.KineticAleksandrov
