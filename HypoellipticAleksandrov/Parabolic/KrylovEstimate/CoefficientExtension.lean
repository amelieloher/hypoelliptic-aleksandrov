module

public import HypoellipticAleksandrov.Parabolic.KrylovCylinder
public import Mathlib.Topology.TietzeExtension

/-! # Continuous extension of the coefficient matrix from a closed set -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.KrylovEstimate

/-- Extend a continuous matrix field from a closed set, preserving its values there. -/
theorem exists_continuous_matrix_extension
    {N : ℕ} {K : Set (TimeVelocity N)} (hK : IsClosed K)
    (a : TimeVelocity N → PDE.Mat N) (ha : ContinuousOn a K) :
    ∃ ae : TimeVelocity N → PDE.Mat N,
      Continuous ae ∧ Set.EqOn ae a K := by
  have he (i j : Fin N) : ∃ g : C(TimeVelocity N, ℝ),
      ∀ z : K, g z = a z i j := by
    let f : C(K, ℝ) := ⟨fun z => a z i j,
      (continuous_apply j).comp ((continuous_apply i).comp ha.domRestrict)⟩
    obtain ⟨g, hg⟩ := f.exists_extension' hK.isClosedEmbedding_subtypeVal
    exact ⟨g, fun z => congrFun hg z⟩
  choose g hg using he
  refine ⟨fun z i j => g i j z, ?_, ?_⟩
  · exact continuous_pi fun i => continuous_pi fun j => (g i j).continuous
  · intro z hz
    funext i j
    exact hg i j ⟨z, hz⟩

end HypoellipticAleksandrov.Parabolic.KrylovEstimate
