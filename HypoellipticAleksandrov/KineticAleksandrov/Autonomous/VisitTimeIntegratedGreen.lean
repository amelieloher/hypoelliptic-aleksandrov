module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitTimeIntegrals
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassOutgoing
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripKernelIntegral

/-! # The actual short-time quadratic identity integrated over entrance measures -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/-- The localized quadratic is integrable against every actual entrance measure. -/
theorem visitTimeQuadratic_integrable_entrance
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T b : ℝ)
    (P : Point) (n : ℕ) :
    Integrable (fun p => visitTimeCutoff b c.r c.positive p.time *
      visitQuadratic c (p.velocity 0))
      (visitEntrancePiece hH hLE hlam hLam A c J s T P n) := by
  apply visitTimeQuadratic_integrable_of_active_support
  exact (visitGamma_ae_closedEntrance P c J s T _ _ n).mono
    (fun p hp => subset_closure (visitClosedEntrance_subset_active c hp))

/-- The localized quadratic also has exactly zero outgoing internal-face integral. -/
theorem visitTimeQuadratic_outgoing_integral_zero
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T b : ℝ)
    (P : Point) (n : ℕ) :
    (∫ p, visitTimeCutoff b c.r c.positive p.time * visitQuadratic c (p.velocity 0)
      ∂visitOutgoingPiece hH hLE hlam hLam A c J s T P n) = 0 := by
  have hz : (fun p => visitTimeCutoff b c.r c.positive p.time *
      visitQuadratic c (p.velocity 0)) =ᵐ[
        visitOutgoingPiece hH hLE hlam hLam A c J s T P n] 0 := by
    filter_upwards [visitQuadratic_ae_zero_outgoing hH hLE hlam hLam A c J s T P n] with p hp
    rw [hp, mul_zero]
    rfl
  rw [integral_congr_ae hz]
  exact integral_zero _ _

/-- Every actual entrance satisfies the genuine integrated short-time quadratic identity. -/
theorem visitTimeQuadratic_entrance_green_identity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T b : ℝ) (P : Point)
    (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (n : ℕ) :
    let mu := visitEntrancePiece hH hLE hlam hLam A c J s T P n
    let E := visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T
    let G := visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T
    let f := fun q : Point => visitTimeCutoff b c.r c.positive q.time *
      visitQuadratic c (q.velocity 0)
    (∫ p, f p ∂mu) = (∫ p, f p ∂E ∘ₘ mu) -
      ∫ p, forwardScalarOperator A.a f p ∂G ∘ₘ mu := by
  classical
  dsimp only
  let mu := visitEntrancePiece hH hLE hlam hLam A c J s T P n
  let E := visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T
  let G := visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T
  let f := fun q : Point => visitTimeCutoff b c.r c.positive q.time *
    visitQuadratic c (q.velocity 0)
  let g := fun p => forwardScalarOperator A.a f p
  have hE : Integrable f (E ∘ₘ mu) :=
    visitTimeQuadratic_integrable_activeExitMixture hH hLE hlam hLam A c J s T b mu
  have hG : Integrable g (G ∘ₘ mu) :=
    visitTimeQuadratic_operator_integrable_activeGreenMixture hH hLE hlam hLam A c J s T b mu
  have hiE : Integrable (fun p => ∫ q, f q ∂E p) mu := by
    rw [Measure.comp_eq_comp_const_apply] at hE
    simpa only [Kernel.const_apply] using hE.integral_comp
  have hiG : Integrable (fun p => ∫ q, g q ∂G p) mu := by
    rw [Measure.comp_eq_comp_const_apply] at hG
    simpa only [Kernel.const_apply] using hG.integral_comp
  have hp : f =ᵐ[mu] fun p => (∫ q, f q ∂E p) - ∫ q, g q ∂G p := by
    filter_upwards [visitEntrancePiece_ae_activePole hH hLE hlam hLam A c J s T P hP n]
      with p hp
    let ep := visitPoleInclusion (visitActiveUnion c J) s T ⟨p, hp⟩
    have he : E p = finiteUnionExit hH hLE hlam hLam A (visitActiveUnion c J) T ep := by
      change (if ht : p ∈ visitPoleSet (visitActiveUnion c J) s T then
        finiteUnionExit hH hLE hlam hLam A (visitActiveUnion c J) T
          (visitPoleInclusion _ s T ⟨p, ht⟩) else 0) = _
      rw [dite_eq_left hp]
    have hg : G p = finiteUnionGreen hH hLE hlam hLam A (visitActiveUnion c J) T ep := by
      change (if ht : p ∈ visitPoleSet (visitActiveUnion c J) s T then
        finiteUnionGreen hH hLE hlam hLam A (visitActiveUnion c J) T
          (visitPoleInclusion _ s T ⟨p, ht⟩) else 0) = _
      rw [dite_eq_left hp]
    have hh := visitTimeQuadratic_active_identity hH hLE hlam hLam A c J b T ep
    dsimp only at hh
    rw [← he, ← hg] at hh
    exact hh
  change (∫ p, f p ∂mu) = (∫ p, f p ∂E ∘ₘ mu) - ∫ p, g p ∂G ∘ₘ mu
  rw [integral_congr_ae hp, integral_sub hiE hiG]
  rw [nested_integral_bind mu E E.measurable f hE,
    nested_integral_bind mu G G.measurable g hG]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
