module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonTail

/-! # No escape of exit mass to infinite physical time -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter
open scoped Topology ENNReal

/-- The unique infinite-horizon exit measure retains exactly unit mass. -/
theorem stripInfiniteExit_mass_one
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤) :
    stripInfiniteExit hH hLE hlam hLam A H e univ = 1 := by
  let μ := stripInfiniteExit hH hLE hlam hLam A H e
  let q := (e.1.velocity 0 - H.lo) * (H.hi - e.1.velocity 0) / (2 * lam)
  have hineq (n : ℕ) : (1 : ℝ) ≤ μ.real univ + q / ((n : ℝ) + 1) := by
    let R := e.1.time + (n : ℝ) + 1
    let T := R + 1
    have ht : e.1.time < T := by
      dsimp only [T, R]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hr : e.1.time < R := by
      dsimp only [R]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    let ep := stripPoleFinite H e T ht
    let ν := stripExit hH hLE hlam hLam A H T ep
    let S : Set Point := {p | p.time < R}
    have hS : MeasurableSet S := measurableSet_lt continuous_time.measurable measurable_const
    have heq := congrArg (fun ρ : Measure Point => ρ univ)
      (stripInfiniteExit_restrict_finite hH hLE hlam hLam A H e T ht R (by
        dsimp only [T]; linarith))
    have hms : μ S = ν S := by
      simpa only [Measure.restrict_apply MeasurableSet.univ, univ_inter] using heq
    have hsmall : ν.real S ≤ μ.real univ := by
      rw [Measure.real, ← hms]
      exact ENNReal.toReal_mono (measure_ne_top μ univ) (measure_mono (subset_univ _))
    have hsum := measureReal_add_measureReal_compl (μ := ν) hS
    have hone : ν.real univ = 1 := by
      rw [Measure.real, stripExit_mass_one, ENNReal.toReal_one]
    rw [hone] at hsum
    have htail := infinite_finite_exit_tail_le hH hLE hlam hLam A H T ep R hr
    have hcomp : Sᶜ = {p | R ≤ p.time} := by
      ext p
      exact (not_lt : ¬ p.time < R ↔ R ≤ p.time)
    change ν.real {p | R ≤ p.time} ≤ q / (R - e.1.time) at htail
    have hden : R - e.1.time = (n : ℝ) + 1 := by dsimp only [R]; ring
    rw [hden, ← hcomp] at htail
    linarith
  have hlim : Tendsto (fun n : ℕ => μ.real univ + q / ((n : ℝ) + 1)) atTop
      (𝓝 (μ.real univ)) := by
    have h := (tendsto_const_nhds (x := μ.real univ)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul q)
    simpa only [div_eq_mul_inv, one_mul, mul_zero, add_zero] using h
  have hr : (1 : ℝ) ≤ μ.real univ := ge_of_tendsto hlim (Eventually.of_forall hineq)
  apply le_antisymm (stripInfiniteExit_mass_le_one hH hLE hlam hLam A H e)
  exact (ENNReal.toReal_le_toReal (by simp) (measure_ne_top μ univ)).mp (by
    simpa only [ENNReal.toReal_one, Measure.real] using hr)

/-- Infinite exits form probability measures; the claim follows from the proved tail estimate. -/
instance stripInfiniteExit_isProbabilityMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤) :
    IsProbabilityMeasure (stripInfiniteExit hH hLE hlam hLam A H e) :=
  ⟨stripInfiniteExit_mass_one hH hLE hlam hLam A H e⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
