module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftScaling

/-! # The homogeneous-test-lift node with its literal operator chain rule -/

@[expose] public section
noncomputable section
open Set
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The actual radial integral is C² homogeneous with the required operator scaling. -/
theorem bellman_test_lift (alpha : ℝ) (_ha : 0 < alpha) (_ha1 : alpha < 1)
    (zeta : (ℝ × ℝ) → ℝ) (hz : ContDiffOn ℝ 2 zeta bellmanPuncturedSet)
    (hc : HasCompactSupport zeta) (hs : tsupport zeta ⊆ bellmanPuncturedSet) :
    IsBellmanHomogeneous alpha (lift alpha zeta) ∧
      ∀ r : ℝ, 0 < r → ∀ q ∈ bellmanPuncturedSet, ∀ b : ℝ,
        bellmanOperator b (fun z => zeta (bellmanPlaneDilation r z)) q =
          r ^ 2 * bellmanOperator b zeta (bellmanPlaneDilation r q) := by
  refine ⟨⟨bellman_lift_contDiffOn alpha zeta hz hc hs, ?_⟩, ?_⟩
  · intro r hr q _
    exact bellman_lift_scaling alpha zeta r hr q
  · intro r hr q hq b
    exact bellmanOperator_comp_dilation r hr zeta hz q hq b

end HypoellipticAleksandrov.KineticAleksandrov
