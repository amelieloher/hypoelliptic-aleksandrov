module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassGreen
import Mathlib.Tactic

/-! # The quadratic exit term retains only the actual terminal slice -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory HypoellipticAleksandrov

/-- An outer interval containing the closed active interval does not clip its component. -/
theorem enlarged_activeUnion_eq (c : Clock) (J : Interval)
    (hJ : closure c.active ⊆ J.carrier) :
    visitActiveUnion c J = c.activeInterval.toFiniteUnion := by
  have ho : c.vbar - 3 * c.r / 4 < c.vbar + 3 * c.r / 4 := by
    linarith [c.positive]
  have hl : J.lo < c.vbar - 3 * c.r / 4 := by
    apply (hJ ?_).1
    rw [Clock.active, closure_Ioo ho.ne]
    exact ⟨le_rfl, ho.le⟩
  have hu : c.vbar + 3 * c.r / 4 < J.hi := by
    apply (hJ ?_).2
    rw [Clock.active, closure_Ioo ho.ne]
    exact ⟨ho.le, le_rfl⟩
  unfold visitActiveUnion
  rw [max_eq_left hl.le, min_eq_left hu.le]
  unfold visitIntervalUnion
  rw [dite_eq_left ho]
  rfl

/-- Away from terminal time, actual active exits carry zero quadratic value. -/
theorem enlargedActiveExit_ae_quadratic_zero_or_terminal
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ)
    (hJ : closure c.active ⊆ J.carrier) (mu : Measure Point) :
    ∀ᵐ q ∂(enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T ∘ₘ mu),
      q.time = T ∨ visitQuadratic c (q.velocity 0) = 0 := by
  classical
  have hm : MeasurableSet {q : Point | q.time = T ∨
      visitQuadratic c (q.velocity 0) = 0} :=
    (isClosed_eq continuous_time continuous_const).measurableSet.union
      (isClosed_eq ((visitQuadratic_smooth c).continuous.comp
        ((continuous_apply 0).comp continuous_velocity)) continuous_const).measurableSet
  apply Measure.ae_comp_of_ae_ae hm
  apply Filter.Eventually.of_forall
  intro p
  rw [enlarged_activeUnion_eq c J hJ]
  change ∀ᵐ q ∂(if hp : p ∈ enlargedVisitPoleSet c.activeInterval.toFiniteUnion T then
    finiteUnionExit hH hLE hlam hLam A c.activeInterval.toFiniteUnion T
      (enlargedVisitPole _ T ⟨p, hp⟩) else 0), _
  split
  · rename_i hp
    have hb : ∀ᵐ q ∂finiteUnionExit hH hLE hlam hLam A c.activeInterval.toFiniteUnion T
        (enlargedVisitPole _ T ⟨p, hp⟩), q ∈ stripClosedExit c.activeInterval T := by
      rw [ae_iff]
      exact stripExitOfRealization_compl_closedExit hH hlam hLam A c.activeInterval
        (stripEvolution hH hLE hlam hLam A c.activeInterval)
        (stripEvolution_spec hH hLE hlam hLam A c.activeInterval) T
        (finiteUnionComponentPole _ T (enlargedVisitPole _ T ⟨p, hp⟩))
    apply hb.mono
    intro q hq
    rcases hq with hq | hq
    · exact Or.inl hq.1
    · right
      rcases hq.2 with hv | hv
      · exact hv ▸ (visitQuadratic_endpoints c).1
      · exact hv ▸ (visitQuadratic_endpoints c).2
  · simp only [ae_zero, Filter.eventually_bot]

/-- At the horizon, the actual terminal mixture is precisely the restricted exit mixture. -/
theorem enlargedActiveTerminal_bind_eq_restrict
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ)
    (mu : Measure Point) (ht : ∀ᵐ p ∂mu, p.time < T) :
    mu.bind (enlargedActiveTerminalFamily hH hLE hlam hLam A c J T) =
      (enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T ∘ₘ mu).restrict
        {q | q.time = T} := by
  classical
  let E := enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T
  let S : Set Point := {q | q.time = T}
  have hS : MeasurableSet S := (isClosed_eq continuous_time continuous_const).measurableSet
  have he : enlargedActiveTerminalFamily hH hLE hlam hLam A c J T =ᵐ[mu]
      fun p => (E p).restrict S := by
    filter_upwards [ht] with p hp
    unfold enlargedActiveTerminalFamily
    rw [ite_eq_right (fun h => (ne_of_lt hp) h.1)]
  rw [Measure.bind_congr_right he]
  have hm : Measurable (fun p => (E p).restrict S) :=
    Measure.measurable_of_measurable_coe _ fun B hB => by
      simp_rw [Measure.restrict_apply hB]
      exact E.measurable_coe (hB.inter hS)
  ext B hB
  rw [Measure.bind_apply hB hm.aemeasurable, Measure.restrict_apply hB,
    Measure.bind_apply (hB.inter hS) E.aemeasurable]
  apply lintegral_congr
  intro p
  exact Measure.restrict_apply hB

/-- The integrated quadratic exit value is exactly its terminal-slice value. -/
theorem enlargedQuadratic_exit_integral_eq_terminal
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ)
    (hJ : closure c.active ⊆ J.carrier) (mu : Measure Point) [IsFiniteMeasure mu]
    (ht : ∀ᵐ p ∂mu, p.time < T) :
    (∫ q, visitQuadratic c (q.velocity 0)
      ∂(enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T ∘ₘ mu)) =
    ∫ q, visitQuadratic c (q.velocity 0)
      ∂mu.bind (enlargedActiveTerminalFamily hH hLE hlam hLam A c J T) := by
  rw [enlargedActiveTerminal_bind_eq_restrict hH hLE hlam hLam A c J T mu ht]
  symm
  rw [← integral_indicator (isClosed_eq continuous_time continuous_const).measurableSet]
  apply integral_congr_ae
  filter_upwards [enlargedActiveExit_ae_quadratic_zero_or_terminal
    hH hLE hlam hLam A c J T hJ mu] with q hq
  rcases hq with hq | hq
  · simp only [Set.indicator, mem_ofPred_eq, hq, ite_true]
  · by_cases htq : q.time = T
    · simp only [Set.indicator, mem_ofPred_eq, htq, ite_true]
    · simp only [Set.indicator, mem_ofPred_eq, htq, ite_false, hq]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
