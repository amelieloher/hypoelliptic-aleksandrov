module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceWeakAssembly

/-! # Bounded Borel source integrals at finite and infinite terminal horizons -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov SectionTwo
open scoped ENNReal

/-- Quadratic mass makes the unique Green measure finite at every horizon. -/
instance stripGreen_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (T : WithTop ℝ) (e : StripPole H T) :
    IsFiniteMeasure (stripGreen hH hLE hlam hLam A H T e) :=
  ⟨lt_of_le_of_lt (stripGreen_quadratic_mass hH hLE hlam hLam A H T e)
    ENNReal.ofReal_lt_top⟩

/-- Every bounded Borel source is integrable against the same finite or infinite Green measure. -/
theorem stripGreen_integrable
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (T : WithTop ℝ) (e : StripPole H T)
    (g : BoundedBorel Point) : Integrable g (stripGreen hH hLE hlam hLam A H T e) := by
  obtain ⟨C, -, hg⟩ := g.exists_bound
  exact integrable_bounded_real _ g g.measurable C hg

/-- The source potential uses the actual unique Green measure at its admitted horizon. -/
def stripPotential
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (T : WithTop ℝ)
    (g : BoundedBorel Point) (e : StripPole H T) : ℝ :=
  ∫ p, g p ∂stripGreen hH hLE hlam hLam A H T e

/-- The quadratic bounded-source estimate is uniform over finite and infinite horizons. -/
theorem stripPotential_abs_le_quadratic
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (T : WithTop ℝ)
    (g : BoundedBorel Point) (e : StripPole H T)
    (C : ℝ) (hC : 0 ≤ C) (hg : ∀ p, |g p| ≤ C) :
    |stripPotential hH hLE hlam hLam A H T g e| ≤
      C * ((e.1.velocity 0 - H.lo) * (H.hi - e.1.velocity 0) / (2 * lam)) := by
  let q := (e.1.velocity 0 - H.lo) * (H.hi - e.1.velocity 0) / (2 * lam)
  have hq : 0 ≤ q :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr e.2.2.1.le) (sub_nonneg.mpr e.2.2.2.le))
      (by positivity)
  have hmass := stripGreen_quadratic_mass hH hLE hlam hLam A H T e
  change stripGreen hH hLE hlam hLam A H T e univ ≤ ENNReal.ofReal q at hmass
  have hm : (stripGreen hH hLE hlam hLam A H T e).real univ ≤ q :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass).trans_eq (ENNReal.toReal_ofReal hq)
  have hb : |stripPotential hH hLE hlam hLam A H T g e| ≤
      C * (stripGreen hH hLE hlam hLam A H T e).real univ := by
    simpa only [stripPotential, Real.norm_eq_abs] using
      norm_integral_le_of_norm_le_const (f := (g : Point → ℝ)) (C := C)
        (μ := stripGreen hH hLE hlam hLam A H T e)
        (Filter.Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hg p)
  exact hb.trans (mul_le_mul_of_nonneg_left hm hC)

/-- Both source estimates hold with the exact minimum on a finite horizon. -/
theorem stripPotential_abs_le_min
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (T : ℝ)
    (g : BoundedBorel Point) (e : StripPole H (T : WithTop ℝ))
    (C : ℝ) (hC : 0 ≤ C) (hg : ∀ p, |g p| ≤ C) :
    |stripPotential hH hLE hlam hLam A H T g e| ≤
      C * min (T - e.1.time)
        ((e.1.velocity 0 - H.lo) * (H.hi - e.1.velocity 0) / (2 * lam)) := by
  rw [mul_min_of_nonneg _ _ hC]
  exact le_min
    (stripPotentialOfKernel_abs_le H _ T g e C hC hg)
    (stripPotential_abs_le_quadratic hH hLE hlam hLam A H T g e C hC hg)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
