module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.ExponentSetting

/-! # Unnormalized admissible stationary homogeneous Radon pairs -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set MeasureTheory

/-- Positive Radon measure on the actual punctured plane. -/
def IsBellmanRadon (μ : Measure BellmanPuncturedPlane) : Prop :=
  IsFiniteMeasureOnCompacts μ ∧ Measure.InnerRegular μ

/-- The source's unnormalized homogeneous adjoint pair, without a density assumption. -/
def IsBellmanAdjointPair (lam Lam β : ℝ) (μ η : Measure BellmanPuncturedPlane) : Prop :=
  IsBellmanRadon μ ∧ IsBellmanRadon η ∧ (μ ≠ 0 ∨ η ≠ 0) ∧
    ENNReal.ofReal lam • μ ≤ η ∧ η ≤ ENNReal.ofReal Lam • μ ∧
    IsBellmanStationaryAdjointPair μ η ∧
    HasBellmanDensityDegree β μ ∧ HasBellmanDensityDegree β η

/-- Admissible degrees for the source's unnormalized ellipticity interval. -/
def bellmanDegrees (lam Lam : ℝ) : Set ℝ :=
  {β | ∃ μ η : Measure BellmanPuncturedPlane, IsBellmanAdjointPair lam Lam β μ η}

/-- The normalized pair condition is exactly membership in the degree set. -/
theorem mem_bellmanAdmissibleDegrees_iff (ratio β : ℝ) :
    β ∈ bellmanAdmissibleDegrees ratio ↔
      ∃ μ η : Measure BellmanPuncturedPlane, IsBellmanAdjointPair 1 ratio β μ η := by
  simp only [bellmanAdmissibleDegrees, Set.mem_ofPred_eq, IsBellmanAdjointPair,
    IsBellmanRadon, ENNReal.ofReal_one, one_smul, and_assoc]

/-- Unnormalized degrees with lower bound one are the normalized degree set. -/
theorem bellmanDegrees_one (ratio : ℝ) :
    bellmanDegrees 1 ratio = bellmanAdmissibleDegrees ratio := by
  ext β
  exact (mem_bellmanAdmissibleDegrees_iff ratio β).symm

/-- Nontriviality of a compared pair forces its first measure to be nonzero. -/
theorem IsBellmanAdjointPair.left_ne_zero {lam Lam β : ℝ}
    {μ η : Measure BellmanPuncturedPlane} (h : IsBellmanAdjointPair lam Lam β μ η) :
    μ ≠ 0 := by
  intro hμ
  have hη : η = 0 := le_antisymm (by simpa only [hμ, smul_zero] using h.2.2.2.2.1)
    (bot_le : (⊥ : Measure BellmanPuncturedPlane) ≤ η)
  rcases h.2.2.1 with h | h
  · exact h hμ
  · exact h hη

end HypoellipticAleksandrov.KineticAleksandrov
