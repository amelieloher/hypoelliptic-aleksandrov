module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripMassInfinite

/-! # Quadratic bounds and velocity-face limits for bounded Borel source potentials -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter
open scoped Topology ENNReal

/-- The actual finite-horizon source potential obeys the exact quadratic interval estimate. -/
theorem stripPotentialOfRealization_abs_le_quadratic
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ))
    (g : BoundedBorel Point) (C : ℝ) (hC : 0 ≤ C) (hg : ∀ p, |g p| ≤ C) :
    |stripPotentialOfKernel H E.2 T g e| ≤
      C * ((e.1.velocity 0 - H.lo) * (H.hi - e.1.velocity 0) / (2 * lam)) := by
  let q := (e.1.velocity 0 - H.lo) * (H.hi - e.1.velocity 0) / (2 * lam)
  have hq : 0 ≤ q :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr e.2.2.1.le) (sub_nonneg.mpr e.2.2.2.le))
      (by positivity)
  have hm : (stripGreenOfKernel H E.2 T e).real univ ≤ q := by
    have hmass := stripGreenOfRealization_quadratic_mass hH hlam hLam A H E hE T e
    change stripGreenOfKernel H E.2 T e univ ≤ ENNReal.ofReal q at hmass
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass).trans_eq
      (ENNReal.toReal_ofReal hq)
  have hb : |stripPotentialOfKernel H E.2 T g e| ≤
      C * (stripGreenOfKernel H E.2 T e).real univ := by
    simpa only [stripPotentialOfKernel, Real.norm_eq_abs] using
      norm_integral_le_of_norm_le_const (f := (g : Point → ℝ)) (C := C)
        (μ := stripGreenOfKernel H E.2 T e)
        (Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hg p)
  exact hb.trans (mul_le_mul_of_nonneg_left hm hC)

/-- Approaching either velocity face sends a bounded-source potential to zero uniformly
in the remaining pole coordinates. -/
theorem stripPotentialOfRealization_velocityFace_tendsto
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (g : BoundedBorel Point)
    (e : ℕ → StripPole H (T : WithTop ℝ)) (v : ℝ) (hv : v = H.lo ∨ v = H.hi)
    (he : Tendsto (fun n => (e n).1.velocity 0) atTop (𝓝 v)) :
    Tendsto (fun n => stripPotentialOfKernel H E.2 T g (e n)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hg⟩ := g.exists_bound
  have ht : Tendsto (fun n => C * (((e n).1.velocity 0 - H.lo) *
      (H.hi - (e n).1.velocity 0) / (2 * lam))) atTop
      (𝓝 (C * ((v - H.lo) * (H.hi - v) / (2 * lam)))) := tendsto_const_nhds.mul
    (((he.sub_const H.lo).mul (tendsto_const_nhds.sub he)).div_const (2 * lam))
  have ht' : Tendsto (fun n => C * (((e n).1.velocity 0 - H.lo) *
      (H.hi - (e n).1.velocity 0) / (2 * lam))) atTop (𝓝 0) := by
    rcases hv with rfl | rfl <;> simpa using ht
  exact squeeze_zero_norm
    (fun n => by simpa only [Real.norm_eq_abs] using
      stripPotentialOfRealization_abs_le_quadratic hH hlam hLam A H E hE T (e n) g C hC hg)
    ht'

/-- The finite-time mass estimate also gives the zero terminal-time limit. -/
theorem stripPotentialOfKernel_terminal_tendsto (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (T : ℝ)
    (g : BoundedBorel Point) (e : ℕ → StripPole H (T : WithTop ℝ))
    (he : Tendsto (fun n => (e n).1.time) atTop (𝓝 T)) :
    Tendsto (fun n => stripPotentialOfKernel H K T g (e n)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hg⟩ := g.exists_bound
  apply squeeze_zero_norm
    (fun n => by simpa only [Real.norm_eq_abs] using
      stripPotentialOfKernel_abs_le H K T g (e n) C hC hg)
  have ht : Tendsto (fun n => C * (T - (e n).1.time)) atTop (𝓝 (C * (T - T))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub he)
  simpa only [sub_self, mul_zero] using ht

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
