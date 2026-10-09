module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionDomination
import Mathlib.Tactic

/-! # Actual waiting-domain occupation gives no mass to core velocities -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/-- Every actual waiting Green kernel gives zero occupation to the core. -/
theorem enlargedWaitingGreenKernel_core_zero
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ) (p : Point) :
    enlargedVisitGreenKernel hH hLE hlam hLam A (visitWaitingUnion c J) T p
      {q | q.velocity 0 ∈ c.core} = 0 := by
  classical
  change (if hp : p ∈ enlargedVisitPoleSet (visitWaitingUnion c J) T then
    finiteUnionGreen hH hLE hlam hLam A (visitWaitingUnion c J) T
      (enlargedVisitPole _ T ⟨p, hp⟩) else 0) {q | q.velocity 0 ∈ c.core} = 0
  split
  · rename_i hp
    have hae := visitUnionGreen_ae_velocity hH hLE hlam hLam A (visitWaitingUnion c J) T
      (enlargedVisitPole _ T ⟨p, hp⟩)
    have hz := ae_iff.mp hae
    apply le_antisymm _ zero_le
    apply (measure_mono (show {q : Point | q.velocity 0 ∈ c.core} ⊆
        {q | q.velocity 0 ∉ (visitWaitingUnion c J).carrier} from
      fun _ hc hv => Set.disjoint_left.mp (visitWaiting_disjoint_core c J) hv hc)).trans_eq hz
  · rfl

/-- Integrating any starting measure against the actual waiting kernel still avoids the core. -/
theorem enlargedWaitingGreenMixture_core_zero
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ) (mu : Measure Point) :
    (enlargedVisitGreenKernel hH hLE hlam hLam A (visitWaitingUnion c J) T ∘ₘ mu)
      {q | q.velocity 0 ∈ c.core} = 0 := by
  have hC : MeasurableSet {q : Point | q.velocity 0 ∈ c.core} :=
    isClosed_Icc.measurableSet.preimage ((continuous_apply 0).comp continuous_velocity).measurable
  rw [Measure.bind_apply hC (Kernel.aemeasurable _)]
  simp only [enlargedWaitingGreenKernel_core_zero, lintegral_zero]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
