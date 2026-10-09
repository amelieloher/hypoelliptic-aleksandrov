module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassEntranceIntegrals
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitMeasureFuture

/-! # Closed velocity support and quadratic integrability for actual active exit mixtures -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/-- Actual union exits remain in the closure of the physical union velocity carrier. -/
theorem visitUnionExit_ae_velocity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (T : ℝ)
    (p : FiniteUnionPole H (T : WithTop ℝ)) :
    ∀ᵐ q ∂finiteUnionExit hH hLE hlam hLam A H T p,
      q.velocity 0 ∈ closure H.carrier := by
  let I := H.component (finiteUnionPoleIndex H T p)
  filter_upwards [stripExitOfRealization_ae_closed_future hH hlam hLam A I
    (stripEvolution hH hLE hlam hLam A I)
    (stripEvolution_spec hH hLE hlam hLam A I) T (finiteUnionComponentPole H T p)] with q hq
  apply closure_mono (H.component_subset (finiteUnionPoleIndex H T p))
  change q.velocity 0 ∈ closure I.carrier
  simpa only [Interval.carrier, closure_Ioo I.ordered.ne] using hq.2.2

/-- Every active exit kernel is concentrated on the closed active interval. -/
theorem visitActiveExitKernel_ae_velocity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (p : Point) :
    ∀ᵐ q ∂visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T p,
      q.velocity 0 ∈ closure c.active := by
  classical
  change ∀ᵐ q ∂(if hp : p ∈ visitPoleSet (visitActiveUnion c J) s T then
    finiteUnionExit hH hLE hlam hLam A (visitActiveUnion c J) T
      (visitPoleInclusion _ s T ⟨p, hp⟩) else 0), q.velocity 0 ∈ closure c.active
  split
  · rename_i hp
    apply (visitUnionExit_ae_velocity hH hLE hlam hLam A (visitActiveUnion c J) T
      (visitPoleInclusion _ s T ⟨p, hp⟩)).mono
    intro q hq
    apply closure_mono _ hq
    rw [visitActiveUnion_carrier]
    exact inter_subset_left
  · simp

/-- Integrating the active exit family preserves its closed physical velocity support. -/
theorem visitActiveExitMixture_ae_velocity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (mu : Measure Point) :
    ∀ᵐ q ∂(visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ mu),
      q.velocity 0 ∈ closure c.active := by
  apply Measure.ae_comp_of_ae_ae
    (isClosed_closure.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)
  exact Filter.Eventually.of_forall
    (visitActiveExitKernel_ae_velocity hH hLE hlam hLam A c J s T)

/-- The source quadratic is integrable against each finite actual active exit mixture. -/
theorem visitQuadratic_integrable_activeExitMixture
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (mu : Measure Point) [IsFiniteMeasure mu] :
    Integrable (fun q => visitQuadratic c (q.velocity 0))
      (visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ mu) := by
  apply Integrable.mono' (integrable_const (9 * c.r ^ 2 / 16))
    (((visitQuadratic_smooth c).continuous.comp
      ((continuous_apply 0).comp continuous_velocity)).measurable.aestronglyMeasurable)
  filter_upwards [visitActiveExitMixture_ae_velocity hH hLE hlam hLam A c J s T mu] with q hq
  change ‖visitQuadratic c (q.velocity 0)‖ ≤ 9 * c.r ^ 2 / 16
  rw [Real.norm_eq_abs, abs_of_nonneg (visitQuadratic_nonneg c hq)]
  exact visitQuadratic_le c _

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
