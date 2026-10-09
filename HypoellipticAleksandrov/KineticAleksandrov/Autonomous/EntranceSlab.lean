module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EntranceSlabTerminal
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EntranceSlabArithmetic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassSummation
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionVisitsStatement

/-! # The entrance slab estimate for the actual enlarged visit count -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory HypoellipticAleksandrov

/-- The source slab estimate charges actual terminal and occupation mass, with no additive term. -/
theorem entranceSlab_mass_le
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T a b : ℝ)
    (hT : 0 < T) (ha : 0 ≤ a) (hab : a ≤ b) (hbT : b ≤ T)
    (hJ : closure c.active ⊆ J.carrier) (P : Point) (hv : P.velocity 0 ∈ J.carrier) :
    visitsFromZero hH hLE hlam hLam A c J T P
      {p | p.time ∈ Ioc (P.time + a) (P.time + b)} ≤
      ENNReal.ofReal (entranceSlabConstant Lam *
        (S hH hLE hlam hLam A b (activeVelocityDatum c) (P.position 0, P.velocity 0) +
          c.r ^ (-2 : ℤ) * ∫ t in Ioc a b,
            S hH hLE hlam hLam A t (activeVelocityDatum c) (P.position 0, P.velocity 0))) := by
  let gamma := enlargedVisitEntrance hH hLE hlam hLam A c J P.time (P.time + T) P
  let D : Set Point := {p | p.time ∈ Ioc (P.time + a) (P.time + b)}
  let mu := fun n => (gamma n).restrict D
  let f := fun t => S hH hLE hlam hLam A t (activeVelocityDatum c)
    (P.position 0, P.velocity 0)
  have hp : 0 ≤ f b := by
    dsimp only [f]
    rw [activeVelocityDatum_action_eq hH hLE hlam hLam A c b (ha.trans hab)]
    exact ENNReal.toReal_nonneg
  have hg : 0 ≤ ∫ t in Ioc a b, f t := by
    rw [← entranceSlab_fullSpaceOccupation_active_real hH hLE hlam hLam A c P T a b ha hbT]
    exact ENNReal.toReal_nonneg
  have hbound (N : ℕ) : (∑ n ∈ Finset.range N, mu n) univ ≤
      ENNReal.ofReal (entranceSlabConstant Lam *
        (f b + c.r ^ (-2 : ℤ) * ∫ t in Ioc a b, f t)) := by
    have hq := entranceSlabQuadratic_partial_mass_bound hH hLE hlam hLam A c J
      P.time (P.time + T) P le_rfl (by linarith) hJ (P.time + a) (P.time + b) N
    have ht := entranceSlab_partial_terminal_mass_le hH hLE hlam hLam A c J T a b
      hT (ha.trans hab) hbT hJ P N
    have ho := entranceSlab_partial_occupation_mass_le hH hLE hlam hLam A c J T a b
      hT ha hbT hJ P hv N
    have hL : 0 ≤ Lam := (hlam.trans_le hLam).le
    have hq' : 5 * c.r ^ 2 / 16 * (∑ n ∈ Finset.range N, (mu n univ).toReal) ≤
        9 * c.r ^ 2 / 16 * f b + 2 * Lam * ∫ t in Ioc a b, f t :=
      hq.trans (add_le_add (mul_le_mul_of_nonneg_left ht (by positivity))
        (mul_le_mul_of_nonneg_left ho (by positivity)))
    have hr := entranceSlab_mass_arithmetic c.positive hL hp hg hq'
    rw [← visit_partial_real_mass mu N univ MeasurableSet.univ] at hr
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ univ) (by
      exact mul_nonneg (entranceSlabConstant_pos hlam hLam).le
        (add_nonneg hp (mul_nonneg (by positivity) hg)))).mpr hr
  have hm := visit_sum_mass_le_of_partial_mass_le mu _ hbound
  have hD : MeasurableSet D := measurableSet_Ioc.preimage continuous_time.measurable
  have he : Measure.sum mu = (Measure.sum gamma).restrict D :=
    (Measure.restrict_sum gamma hD).symm
  rw [he, Measure.restrict_apply MeasurableSet.univ, univ_inter] at hm
  exact hm

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
