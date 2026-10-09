module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitTimeIntegratedGreen
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitTimeSupport
import Mathlib.Tactic

/-! # Entrance counting and operator integration in the actual short time window -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/-- The localized test counts every actual entrance in the closed interval of length r squared. -/
theorem visitTimeQuadratic_entrance_integral_lower
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T b : ℝ)
    (P : Point) (n : ℕ) :
    5 * c.r ^ 2 / 16 *
      (visitEntrancePiece hH hLE hlam hLam A c J s T P n
        {p | p.time ∈ Icc b (b + c.r ^ 2)}).toReal ≤
      ∫ p, visitTimeCutoff b c.r c.positive p.time * visitQuadratic c (p.velocity 0)
        ∂visitEntrancePiece hH hLE hlam hLam A c J s T P n := by
  let mu := visitEntrancePiece hH hLE hlam hLam A c J s T P n
  let W := {p : Point | p.time ∈ Icc b (b + c.r ^ 2)}
  have hW : MeasurableSet W := isClosed_Icc.measurableSet.preimage continuous_time.measurable
  have hi := integral_mono_ae ((integrable_const (5 * c.r ^ 2 / 16)).indicator hW)
    (visitTimeQuadratic_integrable_entrance hH hLE hlam hLam A c J s T b P n) (by
      filter_upwards [visitGamma_ae_closedEntrance P c J s T _ _ n] with p hp
      by_cases ht : p ∈ W
      · rw [indicator_of_mem ht, visitTimeCutoff_eq_one b c.r c.positive ht, one_mul]
        exact visitQuadratic_entrance_lower c hp
      · rw [indicator_of_notMem ht]
        exact mul_nonneg ((visitTimeCutoff_properties b c.r c.positive).2 p.time).1
          ((by positivity : 0 ≤ 5 * c.r ^ 2 / 16).trans
            (visitQuadratic_entrance_lower c hp)))
  rw [integral_indicator hW, integral_const] at hi
  simpa only [smul_eq_mul, Measure.real, Measure.restrict_apply_univ, mul_comm] using hi

/-- The actual localized Green operator is controlled by occupation only in its short window. -/
theorem visitTimeQuadratic_activeGreen_integral_bound : ∃ D : ℝ, 0 ≤ D ∧
    ∀ (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
      (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
      (c : Clock) (J : Interval) (s T b : ℝ) (mu : Measure Point)
      (_hmuFinite : IsFiniteMeasure mu),
      let G := visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ mu;
      -(∫ p, forwardScalarOperator A.a
        (fun q => visitTimeCutoff b c.r c.positive q.time *
          visitQuadratic c (q.velocity 0)) p ∂G) ≤
        (9 * D / 16 + 2 * Lam) *
          (G {p | p.time ∈ Icc (b - c.r ^ 2) (b + 2 * c.r ^ 2)}).toReal := by
  obtain ⟨D, hD, hd⟩ := visitTimeQuadratic_uniform_operator_bound
  refine ⟨D, hD, ?_⟩
  intro hH hLE lam Lam hlam hLam A c J s T b mu hmuFinite
  let := hmuFinite
  dsimp only
  let G := visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ mu
  let f := fun p : Point => forwardScalarOperator A.a
    (fun q => visitTimeCutoff b c.r c.positive q.time * visitQuadratic c (q.velocity 0)) p
  let W := {p : Point | p.time ∈ Icc (b - c.r ^ 2) (b + 2 * c.r ^ 2)}
  have hW : MeasurableSet W := isClosed_Icc.measurableSet.preimage continuous_time.measurable
  have hi := integral_mono_ae
    (visitTimeQuadratic_operator_integrable_activeGreenMixture
      hH hLE hlam hLam A c J s T b mu).neg
    ((integrable_const (9 * D / 16 + 2 * Lam)).indicator hW) (by
      filter_upwards [visitActiveGreenMixture_ae_closedActive hH hLE hlam hLam A c J s T mu]
        with p hp
      change -f p ≤ W.indicator (fun _ => 9 * D / 16 + 2 * Lam) p
      by_cases ht : p ∈ W
      · rw [indicator_of_mem ht]
        exact (neg_le_abs _).trans (hd c b lam Lam hlam A p hp)
      · have hz : f p = 0 := (visitTimeQuadratic_zero_off_window c b A.a p ht).2
        rw [indicator_of_notMem ht, hz]
        exact neg_zero.le)
  change (∫ p, -f p ∂G) ≤ ∫ p, W.indicator (fun _ => 9 * D / 16 + 2 * Lam) p ∂G at hi
  rw [integral_neg, integral_indicator hW, integral_const] at hi
  change -(∫ p, f p ∂G) ≤ (9 * D / 16 + 2 * Lam) * (G W).toReal
  simpa only [smul_eq_mul, Measure.real, Measure.restrict_apply_univ, mul_comm] using hi

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
