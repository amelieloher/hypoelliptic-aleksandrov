module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionStartIntegrals
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonGreenSupport
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalInitial

/-! # The actual localized terminal action of an active piece -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory
open scoped Classical

/-- The concrete terminal family, including its zero-duration atom, is measurable. -/
theorem positionStartTerminalFamily_measurable
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) :
    Measurable (enlargedActiveTerminalFamily hH hLE hlam hLam A c J b) := by
  let E := enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) b
  have hS : MeasurableSet {q : Point | q.time = b} :=
    (isClosed_eq continuous_time continuous_const).measurableSet
  have hm : Measurable (fun p => (E p).restrict {q | q.time = b}) :=
    Measure.measurable_of_measurable_coe _ fun B hB => by
      simp_rw [Measure.restrict_apply hB]
      exact E.measurable_coe (hB.inter hS)
  exact Measure.measurable_dirac.ite
    (hS.inter ((visitActiveUnion c J).isOpen_carrier.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)) hm

/-- The position cutoff preserves the exact zero internal-exit contribution. -/
theorem positionStartQuadratic_exit_integral_eq_terminal
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (Y T : ℝ)
    (hJ : closure c.active ⊆ J.carrier) (mu : Measure Point)
    (ht : ∀ᵐ p ∂mu, p.time < T) :
    (∫ q, positionStartCutoff Y c.r c.positive (q.position 0) *
      visitQuadratic c (q.velocity 0)
      ∂(enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T ∘ₘ mu)) =
    ∫ q, positionStartCutoff Y c.r c.positive (q.position 0) *
      visitQuadratic c (q.velocity 0)
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
    · simp only [Set.indicator, mem_ofPred_eq, htq, ite_false, hq, mul_zero]

/-- Before a finite observation time, the concrete terminal family obeys the Green identity. -/
theorem positionStartQuadratic_terminal_identity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (Y b : ℝ)
    (hc : |c.vbar| = 2 * c.r) (hJ : closure c.active ⊆ J.carrier)
    (p : Point) (hv : p.velocity 0 ∈ c.active) (ht : p.time < b) :
    let f := fun q : Point => positionStartCutoff Y c.r c.positive (q.position 0) *
      visitQuadratic c (q.velocity 0)
    f p = (∫ q, f q ∂enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p) -
      ∫ q, forwardScalarOperator A.a f q
        ∂enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b p := by
  dsimp only
  have hp : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) b := by
    refine ⟨ht, ?_⟩
    rw [visitActiveUnion_carrier]
    exact ⟨hv, hJ (subset_closure hv)⟩
  let e := enlargedVisitPole (visitActiveUnion c J) b ⟨p, hp⟩
  have hi := positionStartQuadratic_active_identity hH hLE hlam hLam A c J Y b hc e
  have hE : enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) b p =
      finiteUnionExit hH hLE hlam hLam A (visitActiveUnion c J) b e := by
    change (if h : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) b then _ else 0) = _
    rw [dite_eq_left hp]
  have hG : enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b p =
      finiteUnionGreen hH hLE hlam hLam A (visitActiveUnion c J) b e := by
    change (if h : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) b then _ else 0) = _
    rw [dite_eq_left hp]
  have he := positionStartQuadratic_exit_integral_eq_terminal
    hH hLE hlam hLam A c J Y b hJ (Measure.dirac p)
      ((ae_dirac_iff (isOpen_lt continuous_time continuous_const).measurableSet).mpr ht)
  rw [visitKernel_comp_dirac,
    Measure.dirac_bind (positionStartTerminalFamily_measurable
      hH hLE hlam hLam A c J b)] at he
  rw [hE] at he
  dsimp only at hi
  rw [← hG, he] at hi
  exact hi

/-- Clipping the genuine all-time active occupation at `b` gives its finite Green kernel. -/
theorem positionStartGreen_eq_restrict
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ)
    (hJ : closure c.active ⊆ J.carrier) (p : Point)
    (hv : p.velocity 0 ∈ c.active) (ht : p.time < b) :
    enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b p =
      (stripGreen hH hLE hlam hLam A c.activeInterval ⊤
        (densityClockPole c p hv)).restrict {q | q.time < b} := by
  rw [enlarged_activeUnion_eq c J hJ]
  have hp : p ∈ enlargedVisitPoleSet c.activeInterval.toFiniteUnion b := by
    refine ⟨ht, ?_⟩
    rw [Interval.toFiniteUnion_carrier]
    exact (densityClockPole c p hv).2.2
  change (if h : p ∈ enlargedVisitPoleSet c.activeInterval.toFiniteUnion b then _
    else 0) = _
  rw [dite_eq_left hp]
  exact stripGreen_finite_restrict_infinite hH hLE hlam hLam A c.activeInterval
    (densityClockPole c p hv) b ht

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
