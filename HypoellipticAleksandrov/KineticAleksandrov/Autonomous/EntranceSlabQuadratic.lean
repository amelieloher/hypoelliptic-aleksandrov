module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassQuadratic

/-! # Quadratic identities for visits restricted to a time slab

The terminal family retains starts at its observation time. This endpoint is
needed for the right-closed time bins in the source entrance-slab estimate.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- Entrance-supported finite measures have an integrable source quadratic. -/
theorem entranceSlabQuadratic_integrable (c : Clock) (mu : Measure Point)
    [IsFiniteMeasure mu] (hmu : ∀ᵐ p ∂mu, p.velocity 0 ∈ closure c.entrance) :
    Integrable (fun p => visitQuadratic c (p.velocity 0)) mu := by
  apply Integrable.mono' (integrable_const (9 * c.r ^ 2 / 16))
    (((visitQuadratic_smooth c).continuous.comp
      ((continuous_apply 0).comp continuous_velocity)).measurable.aestronglyMeasurable)
  filter_upwards [hmu] with p hp
  change ‖visitQuadratic c (p.velocity 0)‖ ≤ 9 * c.r ^ 2 / 16
  rw [Real.norm_eq_abs, abs_of_nonneg
    ((by positivity : 0 ≤ 5 * c.r ^ 2 / 16).trans
      (visitQuadratic_entrance_lower c hp))]
  exact visitQuadratic_le c _

/-- The lower quadratic bound survives restriction to any measurable time slab. -/
theorem entranceSlabQuadratic_mass_lower (c : Clock) (mu : Measure Point)
    [IsFiniteMeasure mu] (hmu : ∀ᵐ p ∂mu, p.velocity 0 ∈ closure c.entrance) :
    5 * c.r ^ 2 / 16 * (mu univ).toReal ≤
      ∫ p, visitQuadratic c (p.velocity 0) ∂mu := by
  have h := integral_mono_ae (integrable_const (5 * c.r ^ 2 / 16))
    (entranceSlabQuadratic_integrable c mu hmu)
    (hmu.mono fun _ hp => visitQuadratic_entrance_lower c hp)
  simpa only [integral_const, smul_eq_mul, Measure.real, mul_comm] using h

/-- A visit starting at the right endpoint contributes its actual initial quadratic value. -/
theorem entranceSlabQuadratic_terminal_at_start
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) (p : Point)
    (ht : p.time = b) (hv : p.velocity 0 ∈ (visitActiveUnion c J).carrier) :
    (∫ q, visitQuadratic c (q.velocity 0)
      ∂enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p) =
        visitQuadratic c (p.velocity 0) := by
  unfold enlargedActiveTerminalFamily
  rw [ite_eq_left ⟨ht, hv⟩, integral_dirac]

/-- Before its right endpoint the slab identity is the actual active Green identity. -/
theorem entranceSlabQuadratic_point_identity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ)
    (hJ : closure c.active ⊆ J.carrier) (p : Point)
    (ht : p.time < b) (hv : p.velocity 0 ∈ (visitActiveUnion c J).carrier) :
    visitQuadratic c (p.velocity 0) =
      (∫ q, visitQuadratic c (q.velocity 0)
        ∂enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p) +
      ∫ q, 2 * A.a (q.position 0) (q.velocity 0)
        ∂enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b p := by
  classical
  have hp : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) b := ⟨ht, hv⟩
  let ep := enlargedVisitPole (visitActiveUnion c J) b ⟨p, hp⟩
  have hi := visitQuadratic_active_identity hH hLE hlam hLam A c J b ep
  have he : enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) b p =
      finiteUnionExit hH hLE hlam hLam A (visitActiveUnion c J) b ep := by
    change (if h : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) b then
      finiteUnionExit hH hLE hlam hLam A (visitActiveUnion c J) b
        (enlargedVisitPole _ b ⟨p, h⟩) else 0) = _
    rw [dite_eq_left hp]
  have hg : enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b p =
      finiteUnionGreen hH hLE hlam hLam A (visitActiveUnion c J) b ep := by
    change (if h : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) b then
      finiteUnionGreen hH hLE hlam hLam A (visitActiveUnion c J) b
        (enlargedVisitPole _ b ⟨p, h⟩) else 0) = _
    rw [dite_eq_left hp]
  let E := enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) b
  have hz := enlargedActiveExit_ae_quadratic_zero_or_terminal
    hH hLE hlam hLam A c J b hJ (Measure.dirac p)
  rw [Measure.dirac_bind E.measurable p] at hz
  have heq : (∫ q, visitQuadratic c (q.velocity 0) ∂E p) =
      ∫ q, visitQuadratic c (q.velocity 0)
        ∂enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p := by
    unfold enlargedActiveTerminalFamily
    rw [ite_eq_right (fun h => (ne_of_lt ht) h.1)]
    rw [← integral_indicator
      (isClosed_eq continuous_time continuous_const).measurableSet]
    apply integral_congr_ae
    filter_upwards [hz] with q hq
    rcases hq with hq | hq
    · simp only [Set.indicator, mem_ofPred_eq, hq, ite_true]
    · by_cases hqb : q.time = b
      · simp only [Set.indicator, mem_ofPred_eq, hqb, ite_true]
      · simp only [Set.indicator, mem_ofPred_eq, hqb, ite_false, hq]
  rw [← he, ← hg] at hi
  rw [heq] at hi
  have hn : (fun q : Point => -2 * A.a (q.position 0) (q.velocity 0)) =
      -(fun q => 2 * A.a (q.position 0) (q.velocity 0)) := by
    funext q
    simp only [Pi.neg_apply, neg_mul]
  rw [hn, integral_neg', sub_neg_eq_add] at hi
  exact hi

/-- The point identity includes visits starting exactly at the slab's right endpoint. -/
theorem entranceSlabQuadratic_closed_point_identity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ)
    (hJ : closure c.active ⊆ J.carrier) (p : Point)
    (ht : p.time ≤ b) (hv : p.velocity 0 ∈ (visitActiveUnion c J).carrier) :
    visitQuadratic c (p.velocity 0) =
      (∫ q, visitQuadratic c (q.velocity 0)
        ∂enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p) +
      ∫ q, 2 * A.a (q.position 0) (q.velocity 0)
        ∂enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b p := by
  classical
  rcases lt_or_eq_of_le ht with hlt | heq
  · exact entranceSlabQuadratic_point_identity hH hLE hlam hLam A c J b hJ p hlt hv
  · have hg : enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b p =
        0 := by
      change (if h : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) b then
        finiteUnionGreen hH hLE hlam hLam A (visitActiveUnion c J) b
          (enlargedVisitPole _ b ⟨p, h⟩) else 0) = 0
      exact dite_eq_right (fun h => (ne_of_lt h.1) heq)
    rw [hg, integral_zero_measure, add_zero,
      entranceSlabQuadratic_terminal_at_start hH hLE hlam hLam A c J b p heq hv]

/-- Restricting an actual entrance to new starts preserves the exact quadratic lower bound. -/
theorem entranceSlabQuadratic_restrict_mass_lower
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (hs : s ≤ P.time) (hT : P.time < T) (n : ℕ) (a b : ℝ) :
    let mu := (enlargedVisitEntrance hH hLE hlam hLam A c J s T P n).restrict
      {p | p.time ∈ Ioc a b}
    5 * c.r ^ 2 / 16 * (mu univ).toReal ≤
      ∫ p, visitQuadratic c (p.velocity 0) ∂mu := by
  apply entranceSlabQuadratic_mass_lower
  exact ((enlargedVisitEntrance_ae_support hH hLE hlam hLam A c J s T P hs hT n).mono
    fun _ hp => hp.2.2).filter_mono (ae_mono Measure.restrict_le_self)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
