module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassIntegratedGreen
import Mathlib.Tactic

/-! # Finite quadratic Green integrals for enlarged-strip entrances -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/-- On poles after `s`, the enlarged Green kernel agrees with a finite clipped kernel. -/
theorem enlargedVisitGreen_comp_eq_clipped
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (s T : ℝ)
    (mu : Measure Point) (hs : ∀ᵐ p ∂mu, s ≤ p.time) :
    enlargedVisitGreenKernel hH hLE hlam hLam A H T ∘ₘ mu =
      visitUnionGreenKernel hH hLE hlam hLam A H (s - 1) T ∘ₘ mu := by
  classical
  apply Measure.comp_congr
  filter_upwards [hs] with p hp
  change (if h : p ∈ enlargedVisitPoleSet H T then
    finiteUnionGreen hH hLE hlam hLam A H T (enlargedVisitPole H T ⟨p, h⟩) else 0) =
      (if h : p ∈ visitPoleSet H (s - 1) T then
        finiteUnionGreen hH hLE hlam hLam A H T
          (visitPoleInclusion H (s - 1) T ⟨p, h⟩) else 0)
  have he : p ∈ enlargedVisitPoleSet H T ↔ p ∈ visitPoleSet H (s - 1) T := by
    change (p.time < T ∧ p.velocity 0 ∈ H.carrier) ↔
      (s - 1 < p.time ∧ p.time < T ∧ p.velocity 0 ∈ H.carrier)
    constructor
    · intro h
      exact ⟨by linarith, h⟩
    · exact fun h => h.2
  by_cases h : p ∈ enlargedVisitPoleSet H T
  · rw [dite_eq_left h, dite_eq_left (he.mp h)]
    rfl
  · rw [dite_eq_right h, dite_eq_right (fun hh => h (he.mpr hh))]

/-- Each actual active occupation is finite, although its unrestricted kernel is not uniform. -/
theorem enlargedActivePiece_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (hs : s ≤ P.time) (hT : P.time < T) (n : ℕ) :
    IsFiniteMeasure (enlargedActivePiece hH hLE hlam hLam A c J s T P n) := by
  unfold enlargedActivePiece
  rw [enlargedVisitGreen_comp_eq_clipped hH hLE hlam hLam A (visitActiveUnion c J) s T _
    ((enlargedVisitEntrance_ae_support hH hLE hlam hLam A c J s T P hs hT n).mono
      fun _ hp => hp.1)]
  infer_instance

/-- Actual enlarged exit mixtures remain in the closed active interval. -/
theorem enlargedActiveExitMixture_ae_velocity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ)
    (mu : Measure Point) :
    ∀ᵐ q ∂(enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T ∘ₘ mu),
      q.velocity 0 ∈ closure c.active := by
  classical
  apply Measure.ae_comp_of_ae_ae
    (isClosed_closure.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)
  apply Filter.Eventually.of_forall
  intro p
  change ∀ᵐ q ∂(if hp : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) T then
    finiteUnionExit hH hLE hlam hLam A (visitActiveUnion c J) T
      (enlargedVisitPole _ T ⟨p, hp⟩) else 0), q.velocity 0 ∈ closure c.active
  split
  · rename_i hp
    apply (visitUnionExit_ae_velocity hH hLE hlam hLam A (visitActiveUnion c J) T
      (enlargedVisitPole _ T ⟨p, hp⟩)).mono
    intro q hq
    apply closure_mono _ hq
    rw [visitActiveUnion_carrier]
    exact inter_subset_left
  · simp only [ae_zero, Filter.eventually_bot]

/-- The quadratic is integrable against each finite enlarged active exit mixture. -/
theorem enlargedQuadratic_integrable_exit
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ)
    (mu : Measure Point) [IsFiniteMeasure mu] :
    Integrable (fun q => visitQuadratic c (q.velocity 0))
      (enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T ∘ₘ mu) := by
  apply Integrable.mono' (integrable_const (9 * c.r ^ 2 / 16))
    (((visitQuadratic_smooth c).continuous.comp
      ((continuous_apply 0).comp continuous_velocity)).measurable.aestronglyMeasurable)
  filter_upwards [enlargedActiveExitMixture_ae_velocity hH hLE hlam hLam A c J T mu]
    with q hq
  change ‖visitQuadratic c (q.velocity 0)‖ ≤ 9 * c.r ^ 2 / 16
  rw [Real.norm_eq_abs, abs_of_nonneg (visitQuadratic_nonneg c hq)]
  exact visitQuadratic_le c _

/-- Every actual entrance satisfies the integrated quadratic identity on its active domain. -/
theorem enlargedQuadratic_entrance_green_identity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (P : Point)
    (hs : s ≤ P.time) (hT : P.time < T)
    (hJ : closure c.active ⊆ J.carrier) (n : ℕ) :
    (∫ p, visitQuadratic c (p.velocity 0)
      ∂enlargedVisitEntrance hH hLE hlam hLam A c J s T P n) =
      (∫ p, visitQuadratic c (p.velocity 0)
        ∂(enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T ∘ₘ
          enlargedVisitEntrance hH hLE hlam hLam A c J s T P n)) +
      ∫ p, 2 * A.a (p.position 0) (p.velocity 0)
        ∂(enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) T ∘ₘ
          enlargedVisitEntrance hH hLE hlam hLam A c J s T P n) := by
  classical
  let mu := enlargedVisitEntrance hH hLE hlam hLam A c J s T P n
  let E := enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T
  let G := enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) T
  let f := fun p : Point => visitQuadratic c (p.velocity 0)
  let g := fun p : Point => 2 * A.a (p.position 0) (p.velocity 0)
  have hE : Integrable f (E ∘ₘ mu) :=
    enlargedQuadratic_integrable_exit hH hLE hlam hLam A c J T mu
  have : IsFiniteMeasure (G ∘ₘ mu) :=
    enlargedActivePiece_isFiniteMeasure hH hLE hlam hLam A c J s T P hs hT n
  have hG : Integrable g (G ∘ₘ mu) := visitCoefficient_integrable hlam A _
  have hiE : Integrable (fun p => ∫ q, f q ∂E p) mu := by
    rw [Measure.comp_eq_comp_const_apply] at hE
    simpa only [Kernel.const_apply] using hE.integral_comp
  have hiG : Integrable (fun p => ∫ q, g q ∂G p) mu := by
    rw [Measure.comp_eq_comp_const_apply] at hG
    simpa only [Kernel.const_apply] using hG.integral_comp
  have hp : f =ᵐ[mu] fun p => (∫ q, f q ∂E p) + ∫ q, g q ∂G p := by
    filter_upwards [enlargedVisitEntrance_ae_activePole hH hLE hlam hLam A c J s T P hs hT hJ n]
      with p hp
    let ep := enlargedVisitPole (visitActiveUnion c J) T ⟨p, hp⟩
    have he : E p = finiteUnionExit hH hLE hlam hLam A (visitActiveUnion c J) T ep := by
      change (if ht : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) T then
        finiteUnionExit hH hLE hlam hLam A (visitActiveUnion c J) T
          (enlargedVisitPole _ T ⟨p, ht⟩) else 0) = _
      rw [dite_eq_left hp]
    have hg : G p = finiteUnionGreen hH hLE hlam hLam A (visitActiveUnion c J) T ep := by
      change (if ht : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) T then
        finiteUnionGreen hH hLE hlam hLam A (visitActiveUnion c J) T
          (enlargedVisitPole _ T ⟨p, ht⟩) else 0) = _
      rw [dite_eq_left hp]
    have hh := visitQuadratic_active_identity hH hLE hlam hLam A c J T ep
    have hn : (fun q : Point => -2 * A.a (q.position 0) (q.velocity 0)) = -g := by
      funext q
      dsimp [g]
      ring
    rw [← he, ← hg, hn] at hh
    change f p = (∫ q, f q ∂E p) - ∫ q, -g q ∂G p at hh
    rw [integral_neg, sub_neg_eq_add] at hh
    exact hh
  change (∫ p, f p ∂mu) = (∫ p, f p ∂E ∘ₘ mu) + ∫ p, g p ∂G ∘ₘ mu
  rw [integral_congr_ae hp, integral_add hiE hiG]
  rw [nested_integral_bind mu E E.measurable f hE,
    nested_integral_bind mu G G.measurable g hG]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
