module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapNorm
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FarVelocityDensityDomination
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitCone
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.Tactic

/-! # Canonical active Green kernels and their actual jointly measurable densities -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Classical

/-- The literal coordinate product makes physical spacetime second countable. -/
instance positionPoint_secondCountableTopology : SecondCountableTopology Point :=
  (HypoellipticAleksandrov.KineticPoint.homeomorphProd 1).secondCountableTopology

/-- The active Green kernel agrees with the canonical Green at every valid starting velocity. -/
theorem enlargedActiveGreenKernel_apply
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) :
    enlargedActiveGreenKernel hH hLE hlam hLam A c e =
      stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e he) := by
  change (if hp : e.velocity 0 ∈ c.active then
    stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e hp) else 0) = _
  rw [dite_eq_left he]

/-- Uniform quadratic mass makes the all-time physical active family a finite kernel. -/
instance enlargedActiveGreenKernel_isFiniteKernel
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) :
    IsFiniteKernel (enlargedActiveGreenKernel hH hLE hlam hLam A c) := by
  refine ⟨ENNReal.ofReal ((3 * c.r / 2) ^ 2 / (2 * lam)), ENNReal.ofReal_lt_top, ?_⟩
  intro e
  by_cases he : e.velocity 0 ∈ c.active
  · rw [enlargedActiveGreenKernel_apply hH hLE hlam hLam A c e he]
    apply (stripGreen_quadratic_mass hH hLE hlam hLam A c.activeInterval ⊤ _).trans
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_div_iff_of_pos_right (by linarith : 0 < 2 * lam)).2
    change (e.velocity 0 - (c.vbar - 3 * c.r / 4)) *
      (c.vbar + 3 * c.r / 4 - e.velocity 0) ≤ (3 * c.r / 2) ^ 2
    nlinarith only [sq_nonneg (e.velocity 0 - c.vbar), sq_nonneg c.r]
  · change (if hp : e.velocity 0 ∈ c.active then
      stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e hp)
      else 0) univ ≤ _
    rw [dite_eq_right he]
    exact zero_le

/-- The pushforward predecessor supplies absolute continuity of every actual active pole. -/
theorem enlargedActiveGreenKernel_absolutelyContinuous (hpush : PushforwardStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) :
    enlargedActiveGreenKernel hH hLE hlam hLam A c e ≪ (volume : Measure Point) := by
  by_cases he : e.velocity 0 ∈ c.active
  · obtain ⟨C, _, hd⟩ := (hpush hH hLE lam Lam hlam hLam).2 (5 / 4) (by norm_num)
    obtain ⟨G, _, _, hG, _, _⟩ := hd A c e he
    rw [enlargedActiveGreenKernel_apply hH hLE hlam hLam A c e he, hG]
    exact (withDensity_absolutelyContinuous _ _).trans
      Measure.restrict_le_self.absolutelyContinuous
  · change (if hp : e.velocity 0 ∈ c.active then
      stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e hp)
      else 0) ≪ volume
    rw [dite_eq_right he]
    intro B _
    rfl

/-- The actual joint extended density of the all-time active Green kernel. -/
def positionActiveDensity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) : Point → Point → ℝ≥0∞ := by
  letI := density_volume_sigmaFinite
  exact positionKernelDensity (enlargedActiveGreenKernel hH hLE hlam hLam A c) volume

/-- The active density is jointly measurable in the physical starting and observed points. -/
theorem measurable_positionActiveDensity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) :
    Measurable (fun p : Point × Point =>
      positionActiveDensity hH hLE hlam hLam A c p.1 p.2) := by
  have : SigmaFinite (volume : Measure Point) := density_volume_sigmaFinite
  exact measurable_positionKernelDensity
    (enlargedActiveGreenKernel hH hLE hlam hLam A c) (volume : Measure Point)

/-- The jointly measurable density represents the same canonical active kernel. -/
theorem withDensity_positionActiveDensity (hpush : PushforwardStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) :
    volume.withDensity (positionActiveDensity hH hLE hlam hLam A c e) =
      enlargedActiveGreenKernel hH hLE hlam hLam A c e := by
  have : SigmaFinite (volume : Measure Point) := density_volume_sigmaFinite
  exact withDensity_positionKernelDensity
    (enlargedActiveGreenKernel hH hLE hlam hLam A c) (volume : Measure Point) e
    (enlargedActiveGreenKernel_absolutelyContinuous hpush hH hLE hlam hLam A c e)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
