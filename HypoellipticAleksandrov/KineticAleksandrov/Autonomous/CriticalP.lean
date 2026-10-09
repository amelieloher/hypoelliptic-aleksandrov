module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.DegreeGap
import Mathlib.Tactic.Linarith

/-! # The autonomous critical source exponent -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous

/-- The source threshold is one plus the characterized homogeneous adjoint exponent. -/
def criticalP (ratio : {r : ℝ // 1 ≤ r}) : ℝ :=
  1 + bellmanAdjointExponent ratio.1 ratio.2

/-- The source threshold lies in the half-open interval from three to four. -/
theorem criticalP_bounds (ratio : {r : ℝ // 1 ≤ r}) :
    3 ≤ criticalP ratio ∧ criticalP ratio < 4 := by
  obtain ⟨hl, hu⟩ := bellmanAdjointExponent_range ratio.1 ratio.2
  unfold criticalP
  constructor <;> linarith only [hl, hu]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
