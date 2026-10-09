module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomainsMixtures
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceLimitsInfinite

/-! # Uniform finite mass of actual Green mixtures on finite interval unions -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open scoped ENNReal

/-- A finite union's mass constant depends only on its interval lengths and ellipticity. -/
def finiteUnionGreenMassBound (lam : ℝ) (H : FiniteIntervalUnion) : ℝ≥0∞ :=
  ∑ i : Fin H.count, ENNReal.ofReal (((H.component i).hi - (H.component i).lo) ^ 2 /
    (2 * lam))

/-- The geometric finite-union mass constant is finite. -/
theorem finiteUnionGreenMassBound_ne_top (lam : ℝ) (H : FiniteIntervalUnion) :
    finiteUnionGreenMassBound lam H ≠ ⊤ := by
  unfold finiteUnionGreenMassBound
  exact ENNReal.sum_ne_top.mpr (fun _ _ => ENNReal.ofReal_ne_top)

/-- Every actual union Green pole has the same uniform finite mass bound. -/
theorem finiteUnionGreen_mass_le
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (T : WithTop ℝ)
    (e : FiniteUnionPole H T) :
    finiteUnionGreen hH hLE hlam hLam A H T e univ ≤ finiteUnionGreenMassBound lam H := by
  let i := finiteUnionPoleIndex H T e
  let I := H.component i
  let ep := finiteUnionComponentPole H T e
  have hv := ep.2.2
  change I.lo < e.1.velocity 0 ∧ e.1.velocity 0 < I.hi at hv
  have hprod : (e.1.velocity 0 - I.lo) * (I.hi - e.1.velocity 0) ≤
      (I.hi - I.lo) ^ 2 := by
    have h1 : 0 ≤ e.1.velocity 0 - I.lo := by linarith
    have h2 : 0 ≤ I.hi - e.1.velocity 0 := by linarith
    nlinarith [sq_nonneg (e.1.velocity 0 - I.lo),
      sq_nonneg (I.hi - e.1.velocity 0), mul_nonneg h1 h2]
  have hb := stripGreen_quadratic_mass hH hLE hlam hLam A I T ep
  apply hb.trans
  apply (show ENNReal.ofReal ((e.1.velocity 0 - I.lo) * (I.hi - e.1.velocity 0) /
    (2 * lam)) ≤ ENNReal.ofReal ((I.hi - I.lo) ^ 2 / (2 * lam)) from
    ENNReal.ofReal_le_ofReal
      ((div_le_div_iff_of_pos_right (by positivity : 0 < 2 * lam)).mpr hprod)).trans
  unfold finiteUnionGreenMassBound
  exact Finset.single_le_sum
    (f := fun j : Fin H.count => ENNReal.ofReal
      (((H.component j).hi - (H.component j).lo) ^ 2 / (2 * lam)))
    (fun _ _ => zero_le) (Finset.mem_univ i)

/-- The actual Green mixture has mass bounded linearly by source mass. -/
theorem finiteUnionGreenMixture_mass_le
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (T : WithTop ℝ)
    (nu : Measure (FiniteUnionPole H T)) :
    finiteUnionGreenMixture hH hLE hlam hLam A H T nu univ ≤
      finiteUnionGreenMassBound lam H * nu univ := by
  unfold finiteUnionGreenMixture
  rw [Measure.bind_apply MeasurableSet.univ
    (finiteUnionGreen_measurable hH hLE hlam hLam A H T).aemeasurable]
  calc
    _ ≤ ∫⁻ _x, finiteUnionGreenMassBound lam H ∂nu :=
      lintegral_mono (fun e => finiteUnionGreen_mass_le hH hLE hlam hLam A H T e)
    _ = _ := lintegral_const _

/-- A finite source has a finite actual Green mixture, including at infinite horizon. -/
instance finiteUnionGreenMixture_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (T : WithTop ℝ)
    (nu : Measure (FiniteUnionPole H T)) [IsFiniteMeasure nu] :
    IsFiniteMeasure (finiteUnionGreenMixture hH hLE hlam hLam A H T nu) := by
  constructor
  exact (finiteUnionGreenMixture_mass_le hH hLE hlam hLam A H T nu).trans_lt
    (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr (finiteUnionGreenMassBound_ne_top lam H))
      (measure_lt_top nu univ))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
