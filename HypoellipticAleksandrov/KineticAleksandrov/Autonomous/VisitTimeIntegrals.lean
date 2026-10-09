module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitTimeGreenTest
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassExitIntegrals
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassCoefficientIntegral
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationWaiting
import Mathlib.Tactic

/-! # Integrability of the genuine localized test and operator on actual visit measures -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/-- Closed active velocity support makes the actual localized quadratic integrable. -/
theorem visitTimeQuadratic_integrable_of_active_support (c : Clock) (b : ℝ)
    (mu : Measure Point) [IsFiniteMeasure mu]
    (hmu : ∀ᵐ p ∂mu, p.velocity 0 ∈ closure c.active) :
    Integrable (fun p => visitTimeCutoff b c.r c.positive p.time *
      visitQuadratic c (p.velocity 0)) mu := by
  have hc : Continuous (fun p : Point => visitTimeCutoff b c.r c.positive p.time *
      visitQuadratic c (p.velocity 0)) :=
    ((visitTimeCutoff_properties b c.r c.positive).1.continuous.comp
    continuous_time).mul ((visitQuadratic_smooth c).continuous.comp
      ((continuous_apply 0).comp continuous_velocity))
  apply Integrable.mono' (integrable_const (9 * c.r ^ 2 / 16))
    hc.measurable.aestronglyMeasurable
  filter_upwards [hmu] with p hp
  change ‖visitTimeCutoff b c.r c.positive p.time * visitQuadratic c (p.velocity 0)‖ ≤ _
  have he := (visitTimeCutoff_properties b c.r c.positive).2 p.time
  have hf := visitQuadratic_nonneg c hp
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg he.1, abs_of_nonneg hf]
  have hm := mul_le_mul_of_nonneg_right he.2 hf
  simp only [one_mul] at hm
  exact hm.trans (visitQuadratic_le c _)

/-- The exact localized operator is continuous without differentiating the coefficient. -/
theorem visitTimeQuadratic_operator_continuous {lam Lam : ℝ}
    (A : SmoothAutonomous lam Lam) (c : Clock) (b : ℝ) :
    Continuous (fun p : Point => forwardScalarOperator A.a
      (fun q => visitTimeCutoff b c.r c.positive q.time *
        visitQuadratic c (q.velocity 0)) p) := by
  let eta := visitTimeCutoff b c.r c.positive
  have he := (visitTimeCutoff_properties b c.r c.positive).1
  have hf : Continuous (fun p : Point => visitQuadratic c (p.velocity 0)) :=
    (visitQuadratic_smooth c).continuous.comp
    ((continuous_apply 0).comp continuous_velocity)
  have hh : (fun p : Point => forwardScalarOperator A.a
      (fun q => eta q.time * visitQuadratic c (q.velocity 0)) p) =
      fun p => deriv eta p.time * visitQuadratic c (p.velocity 0) -
        2 * A.a (p.position 0) (p.velocity 0) * eta p.time :=
    funext (visitTimeQuadratic_operator c eta he A.a)
  rw [hh]
  exact (((he.continuous_deriv (by norm_num)).comp continuous_time).mul hf).sub
    ((continuous_const.mul (visitCoefficient_continuous A)).mul
      (he.continuous.comp continuous_time))

/-- Closed active support makes the bounded localized operator integrable. -/
theorem visitTimeQuadratic_operator_integrable_of_active_support
    {lam Lam : ℝ} (hlam : 0 < lam) (A : SmoothAutonomous lam Lam)
    (c : Clock) (b : ℝ) (mu : Measure Point) [IsFiniteMeasure mu]
    (hmu : ∀ᵐ p ∂mu, p.velocity 0 ∈ closure c.active) :
    Integrable (fun p => forwardScalarOperator A.a
      (fun q => visitTimeCutoff b c.r c.positive q.time *
        visitQuadratic c (q.velocity 0)) p) mu := by
  obtain ⟨D, _hD, hd⟩ := visitTimeQuadratic_uniform_operator_bound
  apply Integrable.mono' (integrable_const (9 * D / 16 + 2 * Lam))
    (visitTimeQuadratic_operator_continuous A c b).measurable.aestronglyMeasurable
  filter_upwards [hmu] with p hp
  change ‖forwardScalarOperator A.a
    (fun q => visitTimeCutoff b c.r c.positive q.time * visitQuadratic c (q.velocity 0)) p‖ ≤ _
  rw [Real.norm_eq_abs]
  exact hd c b lam Lam hlam A p hp

/-- The actual active Green mixture has closed active velocity support. -/
theorem visitActiveGreenMixture_ae_closedActive
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (mu : Measure Point) :
    ∀ᵐ q ∂(visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ mu),
      q.velocity 0 ∈ closure c.active := by
  classical
  apply Measure.ae_comp_of_ae_ae
    (isClosed_closure.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)
  apply Filter.Eventually.of_forall
  intro p
  change ∀ᵐ q ∂(if hp : p ∈ visitPoleSet (visitActiveUnion c J) s T then
    finiteUnionGreen hH hLE hlam hLam A (visitActiveUnion c J) T
      (visitPoleInclusion _ s T ⟨p, hp⟩) else 0), q.velocity 0 ∈ closure c.active
  split
  · rename_i hp
    exact (visitUnionGreen_ae_velocity hH hLE hlam hLam A (visitActiveUnion c J) T
      (visitPoleInclusion _ s T ⟨p, hp⟩)).mono fun q hq =>
        subset_closure ((visitActiveUnion_carrier c J).le hq).1
  · simp

/-- The actual active exit mixture discharges the localized test's support condition. -/
theorem visitTimeQuadratic_integrable_activeExitMixture
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T b : ℝ)
    (mu : Measure Point) [IsFiniteMeasure mu] :
    Integrable (fun p => visitTimeCutoff b c.r c.positive p.time *
      visitQuadratic c (p.velocity 0))
      (visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ mu) :=
  visitTimeQuadratic_integrable_of_active_support c b _
    (visitActiveExitMixture_ae_velocity hH hLE hlam hLam A c J s T mu)

/-- The actual active Green mixture discharges the localized operator's support condition. -/
theorem visitTimeQuadratic_operator_integrable_activeGreenMixture
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T b : ℝ)
    (mu : Measure Point) [IsFiniteMeasure mu] :
    Integrable (fun p => forwardScalarOperator A.a
      (fun q => visitTimeCutoff b c.r c.positive q.time *
        visitQuadratic c (q.velocity 0)) p)
      (visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ mu) :=
  visitTimeQuadratic_operator_integrable_of_active_support hlam A c b _
    (visitActiveGreenMixture_ae_closedActive hH hLE hlam hLam A c J s T mu)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
