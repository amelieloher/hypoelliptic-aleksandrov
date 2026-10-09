module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionStartLower

/-! # Localized terminal bounds on the literal source box -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/-- The localized test is nonnegative and bounded by its quadratic maximum on the source box. -/
theorem positionStartQuadratic_box_bound (c : Clock) (Y : ℝ) (p : Point)
    (hc : |c.vbar| = 2 * c.r) (hv : p.velocity 0 ∈ closure c.active) :
    0 ≤ positionStartCutoff Y c.r c.positive (p.position 0) *
      visitQuadratic c (p.velocity 0) ∧
    positionStartCutoff Y c.r c.positive (p.position 0) *
      visitQuadratic c (p.velocity 0) ≤
      9 * c.r ^ 2 / 16 * (box 4 c.r Y).indicator (fun _ => (1 : ℝ))
        (p.position 0, p.velocity 0) := by
  have hchi := (positionStartCutoff_properties Y c.r c.positive).2 (p.position 0)
  have hq := visitQuadratic_nonneg c hv
  refine ⟨mul_nonneg hchi.1 hq, ?_⟩
  by_cases hb : (p.position 0, p.velocity 0) ∈ box 4 c.r Y
  · rw [indicator_of_mem hb, mul_one]
    exact (mul_le_mul_of_nonneg_right hchi.2 hq).trans (by
      simpa only [one_mul] using visitQuadratic_le c (p.velocity 0))
  · rw [indicator_of_notMem hb, mul_zero]
    have ho : c.vbar - 3 * c.r / 4 < c.vbar + 3 * c.r / 4 := by
      linarith [c.positive]
    have hvel := hv
    rw [Clock.active, closure_Ioo ho.ne] at hvel
    have hupper := le_abs_self c.vbar
    have hlower := neg_abs_le c.vbar
    rw [hc] at hupper hlower
    have hva : |p.velocity 0| ≤ 4 * c.r := by
      rw [abs_le]
      constructor <;> linarith [hvel.1, hvel.2, c.positive]
    have hnot : p.position 0 ∉ tsupport (positionStartCutoff Y c.r c.positive) := by
      intro hp
      have hs := positionStartCutoff_tsupport Y c.r c.positive hp
      apply hb
      change |p.position 0 - Y| ≤ 4 * c.r ^ 3 ∧ |p.velocity 0| ≤ 4 * c.r
      refine ⟨?_, hva⟩
      rw [abs_le]
      constructor <;> linarith [hs.1, hs.2, pow_pos c.positive 3]
    rw [image_eq_zero_of_notMem_tsupport hnot, zero_mul]

/-- A finite terminal mixture has a nonnegative localized value. -/
theorem positionStartQuadratic_terminal_integral_nonneg
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (Y b : ℝ)
    (mu : Measure Point) :
    0 ≤ ∫ q, positionStartCutoff Y c.r c.positive (q.position 0) *
      visitQuadratic c (q.velocity 0)
      ∂(positionStartTerminalKernel hH hLE hlam hLam A c J b ∘ₘ mu) := by
  apply integral_nonneg_of_ae
  exact (positionStartTerminalMixture_ae_closedActive hH hLE hlam hLam A c J b mu).mono
    fun q hq => mul_nonneg ((positionStartCutoff_properties Y c.r c.positive).2 _).1
      (visitQuadratic_nonneg c hq)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
