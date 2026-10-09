module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassQuadratic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassCapacity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassGreenCapacity
import Mathlib.Tactic

/-! # Outer-independent bounds for canonical enlarged visit counts

Only the exact finite-piece occupation and terminal domination conclusions
are hypotheses here, as they belong to the enlarged recursion.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory HypoellipticAleksandrov

/-- Actual active pieces have the physical active-velocity support. -/
theorem enlargedActivePiece_ae_active
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (hs : s ≤ P.time) (hT : P.time < T) (n : ℕ) :
    ∀ᵐ q ∂enlargedActivePiece hH hLE hlam hLam A c J s T P n,
      q.velocity 0 ∈ c.active := by
  unfold enlargedActivePiece
  rw [enlargedVisitGreen_comp_eq_clipped hH hLE hlam hLam A (visitActiveUnion c J) s T _
    ((enlargedVisitEntrance_ae_support hH hLE hlam hLam A c J s T P hs hT n).mono
      fun _ hp => hp.1)]
  exact visitActiveGreenMixture_ae_active hH hLE hlam hLam A c J (s - 1) T _

/-- Finite active occupation sums inherit the full-space velocity-band capacity. -/
theorem enlargedActivePiece_partial_capacity_of_domination
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ)
    (P : Point) (hT : 0 < T) (hbar : |c.vbar| = 2 * c.r) (N : ℕ)
    (hOccupation : (∑ n ∈ Finset.range N,
      enlargedActivePiece hH hLE hlam hLam A c J P.time (P.time + T) P n) ≤
        enlargedFullSpaceOccupation hH hLE hlam hLam A P T) :
    (∑ n ∈ Finset.range N,
      (enlargedActivePiece hH hLE hlam hLam A c J P.time (P.time + T) P n univ).toReal) ≤
        (64 * c.r / lam) * Real.sqrt (2 * Lam * T) := by
  let gm := enlargedActivePiece hH hLE hlam hLam A c J P.time (P.time + T) P
  have hPT : P.time < P.time + T := by linarith
  have : ∀ n, IsFiniteMeasure (gm n) := fun n =>
    enlargedActivePiece_isFiniteMeasure hH hLE hlam hLam A c J P.time (P.time + T)
      P le_rfl hPT n
  let B : Set Point := {q | |q.velocity 0| ≤ 3 * c.r}
  have hB : MeasurableSet B := measurableSet_le
    (continuous_abs.measurable.comp ((continuous_apply 0).comp continuous_velocity).measurable)
    measurable_const
  have hs : ∀ᵐ q ∂(∑ n ∈ Finset.range N, gm n), q ∈ B := by
    apply ae_finsetSum_measure_iff.mpr
    intro n _
    apply (enlargedActivePiece_ae_active hH hLE hlam hLam A c J P.time (P.time + T)
      P le_rfl hPT n).mono
    intro q hq
    have hv := (c.active_abs_bounds hq).2
    rw [hbar] at hv
    change |q.velocity 0| ≤ 3 * c.r
    linarith
  have he := congrArg (fun m : Measure Point => m univ)
    (Measure.restrict_eq_self_of_ae_mem hs)
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter] at he
  have hb := (hOccupation B).trans
    (enlargedFullSpaceOccupation_band_le hH hLE hlam hLam A P T c.r hT c.positive)
  rw [he] at hb
  have hradius := c.positive
  have hnon : 0 ≤ (64 * c.r / lam) * Real.sqrt (2 * Lam * T) := by positivity
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_ofReal hnon, visit_partial_real_mass gm N univ MeasurableSet.univ] at hr
  exact hr

/-- Terminal domination bounds the total retained terminal mass by one. -/
theorem enlarged_terminal_partial_mass_le_one_of_domination
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ)
    (P : Point) (hT : 0 < T) (N : ℕ)
    (hTerminal : enlargedActiveTerminal hH hLE hlam hLam A c J P.time
      (P.time + T) P N (P.time + T) ≤
        enlargedFullSpaceTerminal hH hLE hlam hLam A P (P.time + T)) :
    (∑ n ∈ Finset.range N,
      (((enlargedVisitEntrance hH hLE hlam hLam A c J P.time (P.time + T) P n).bind
        (enlargedActiveTerminalFamily hH hLE hlam hLam A c J (P.time + T))) univ).toReal) ≤
          1 := by
  let mu := fun n =>
    (enlargedVisitEntrance hH hLE hlam hLam A c J P.time (P.time + T) P n).bind
      (enlargedActiveTerminalFamily hH hLE hlam hLam A c J (P.time + T))
  have : ∀ n, IsFiniteMeasure (mu n) := fun n =>
    enlarged_terminalPiece_isFiniteMeasure hH hLE hlam hLam A c J P.time (P.time + T)
      P le_rfl (by linarith) n
  have hm := (hTerminal univ).trans
    (enlargedFullSpaceTerminal_mass_le_one hH hLE hlam hLam A P (P.time + T))
  have hr := ENNReal.toReal_mono ENNReal.one_ne_top hm
  change ((∑ n ∈ Finset.range N, mu n) univ).toReal ≤ (1 : ENNReal).toReal at hr
  rw [visit_partial_real_mass mu N univ MeasurableSet.univ, ENNReal.toReal_one] at hr
  exact hr

/-- Source horizon conversion for the quadratic count inequality. -/
theorem enlarged_mass_arithmetic {r R M D : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hD : 0 ≤ D) (hM : 5 * r ^ 2 / 16 * M ≤ 9 * r ^ 2 / 16 + D * R * r) :
    M ≤ (9 / 5 + 16 / 5 * D) * (1 + R / r) := by
  have hraw : M ≤ 9 / 5 + 16 / 5 * D * (R / r) := by
    have hd : M ≤ (9 * r ^ 2 / 16 + D * R * r) / (5 * r ^ 2 / 16) :=
      (le_div_iff₀ (by positivity : 0 < 5 * r ^ 2 / 16)).mpr
        (by simpa only [mul_comm] using hM)
    convert hd using 1
    field_simp
  have hx : 0 ≤ R / r := div_nonneg hR hr.le
  nlinarith

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
