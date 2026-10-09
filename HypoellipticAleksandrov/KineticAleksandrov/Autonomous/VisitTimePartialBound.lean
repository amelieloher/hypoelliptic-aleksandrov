module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassOuterBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitTimeCountSteps
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripTimeMarginal
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-! # A uniform short-time bound for actual finite entrance sums -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/-- Active occupation in the cutoff window has total partial mass at most its time length. -/
theorem visitActiveGreen_partial_time_mass_le
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T b : ℝ) (hT : s < T)
    (P : Point) (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (N : ℕ) :
    ∑ n ∈ Finset.range N,
      ((visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ
        visitEntrancePiece hH hLE hlam hLam A c J s T P n)
          {p | p.time ∈ Icc (b - c.r ^ 2) (b + 2 * c.r ^ 2)}).toReal ≤ 3 * c.r ^ 2 := by
  let W : Set Point := {p | p.time ∈ Icc (b - c.r ^ 2) (b + 2 * c.r ^ 2)}
  have hW : MeasurableSet W := isClosed_Icc.measurableSet.preimage continuous_time.measurable
  have hm := visitActiveGreen_partial_le hH hLE hlam hLam A c J s T hT P hP N W
  rw [visitOuterGreen_eq_strip hH hLE hlam hLam A J s T P hP] at hm
  have ht := stripGreen_timeMarginal hH hLE hlam hLam A J T
    ⟨P, WithTop.coe_lt_coe.mpr hP.2.1, hP.2.2⟩
    (Icc (b - c.r ^ 2) (b + 2 * c.r ^ 2)) isClosed_Icc.measurableSet
  rw [Real.volume_Icc] at ht
  have hw : b + 2 * c.r ^ 2 - (b - c.r ^ 2) = 3 * c.r ^ 2 := by ring
  rw [hw] at ht
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hm.trans ht)
  rw [ENNReal.toReal_ofReal (by positivity), visit_partial_real_mass _ N W hW] at hh
  exact hh

/-- The short-time counting constant is uniform in the coefficient, clock, and outer strip. -/
theorem exists_visitTime_partial_constant {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
        (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T b : ℝ) (_hT : s < T)
        (P : Point) (_hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (N : ℕ),
        (∑ n ∈ Finset.range N,
          (visitEntrancePiece hH hLE hlam hLam A c J s T P n
            {p | p.time ∈ Icc b (b + c.r ^ 2)}).toReal) ≤ C := by
  obtain ⟨D, hD, hd⟩ := visitTimeQuadratic_partial_mass_bound
  let M := 9 * D / 16 + 2 * Lam
  have hM : 0 ≤ M := by dsimp only [M]; linarith
  refine ⟨9 / 5 + 48 * M / 5, by positivity, ?_⟩
  intro hH hLE A c J s T b hT P hP N
  have h := hd hH hLE lam Lam hlam hLam A c J s T b P hP N
  have he := visitRetainedExit_partial_real_mass_le_one hH hLE hlam hLam A c J s T hT P hP N
  have hg := visitActiveGreen_partial_time_mass_le hH hLE hlam hLam A c J s T b hT P hP N
  dsimp only at h he hg
  have hh := h.trans (add_le_add
    (mul_le_mul_of_nonneg_left he (by positivity)) (mul_le_mul_of_nonneg_left hg hM))
  have hr : 0 < c.r ^ 2 := pow_pos c.positive _
  change 5 * c.r ^ 2 / 16 * _ ≤ 9 * c.r ^ 2 / 16 * 1 + M * (3 * c.r ^ 2) at hh
  nlinarith only [hh, hr]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
