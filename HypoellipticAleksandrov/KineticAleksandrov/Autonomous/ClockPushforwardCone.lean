module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockGreenTestPullback
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizon

/-! # The physical cone forces the position clock to advance -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution

/-- The physical active interval on the existing interval carrier. -/
def Clock.activeInterval (c : Clock) : Interval :=
  ⟨c.vbar - 3 * c.r / 4, c.vbar + 3 * c.r / 4, by linarith [c.positive]⟩

/-- Every active velocity advances the normalized position clock at a rate at least one half. -/
theorem Clock.active_ratio_lower (c : Clock) {v : ℝ} (hv : v ∈ c.active) :
    (1 : ℝ) / 2 ≤ v / c.vbar := by
  rcases lt_or_gt_of_ne c.nonzero with hneg | hpos
  · apply (le_div_iff_of_neg hneg).mpr
    have hr := c.radius
    rw [abs_of_neg hneg] at hr
    have hv' : v < c.vbar + 3 * c.r / 4 := hv.2
    nlinarith
  · apply (le_div_iff₀ hpos).mpr
    have hr := c.radius
    rw [abs_of_pos hpos] at hr
    have hv' : c.vbar - 3 * c.r / 4 < v := hv.1
    nlinarith

/-- The source's physical forward cone implies a lower bound on elapsed position-clock time. -/
theorem clock_forward_cone_finite
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (T : ℝ)
    (e : StripPole c.activeInterval (T : WithTop ℝ)) :
    (∀ᵐ p ∂stripExit hH hLE hlam hLam A c.activeInterval T e,
      p.time - e.1.time ≤ 2 * c.r ^ 2 * (c.map e.1 p).time) ∧
    ∀ᵐ p ∂stripGreen hH hLE hlam hLam A c.activeInterval T e,
      p.time - e.1.time ≤ 2 * c.r ^ 2 * (c.map e.1 p).time := by
  have hh := reconstruction_transport_cone_ae hH hlam hLam A c.activeInterval
    (stripEvolution hH hLE hlam hLam A c.activeInterval)
    (stripEvolution_spec hH hLE hlam hLam A c.activeInterval) T e
    1 (-2 / c.vbar) (2 * e.1.position 0 / c.vbar - e.1.time)
    (by dsimp only [reconstructionConeCoordinate]; ring) (fun v hv => by
      have hr := c.active_ratio_lower hv
      have he : v * (-2 / c.vbar) = -2 * (v / c.vbar) := by ring
      rw [he]
      linarith)
  have hb (p : Point)
      (hp : reconstructionConeCoordinate 1 (-2 / c.vbar)
        (2 * e.1.position 0 / c.vbar - e.1.time) p ≤ 0) :
      p.time - e.1.time ≤ 2 * c.r ^ 2 * (c.map e.1 p).time := by
    have he : 2 * c.r ^ 2 * (c.map e.1 p).time =
        2 * (p.position 0 - e.1.position 0) / c.vbar := by
      dsimp [Clock.map]
      field_simp [c.nonzero, ne_of_gt c.positive]
    rw [he]
    have hp' : p.time - e.1.time -
        2 * (p.position 0 - e.1.position 0) / c.vbar ≤ 0 := by
      convert hp using 1
      · dsimp only [reconstructionConeCoordinate]
        ring
    linarith
  exact ⟨hh.1.mono hb, hh.2.mono hb⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
