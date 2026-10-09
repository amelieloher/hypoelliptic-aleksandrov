module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalSetting
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassQuadratic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripMassInfinite
import Mathlib.Tactic

/-! # The actual physical all-time active-strip Green kernel for core domination -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/-- Physical points in the active velocity interval are valid all-time strip poles. -/
def coreAllTimePole (c : Clock) (p : {p : Point | p.velocity 0 ∈ c.active}) :
    StripPole (visitActiveInterval c) ⊤ := ⟨p.1, WithTop.coe_lt_top _, p.2⟩

/-- The all-time pole inclusion keeps Borel physical coordinates. -/
theorem measurable_coreAllTimePole (c : Clock) : Measurable (coreAllTimePole c) :=
  measurable_subtype_coe.subtype_mk

/-- The physical active velocity carrier is measurable. -/
theorem measurableSet_coreAllTimePole (c : Clock) :
    MeasurableSet {p : Point | p.velocity 0 ∈ c.active} :=
  isOpen_Ioo.measurableSet.preimage ((continuous_apply 0).comp continuous_velocity).measurable

/-- The actual all-time strip Green kernel, extended by zero off valid active velocities. -/
def coreAllTimeGreenKernel
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) : Kernel Point Point :=
  visitExtendKernel {p : Point | p.velocity 0 ∈ c.active} (measurableSet_coreAllTimePole c)
    (fun p => stripGreen hH hLE hlam hLam A (visitActiveInterval c) ⊤ (coreAllTimePole c p))
    ((Measure.measurable_measure.mpr
      (stripGreen_measurable_apply hH hLE hlam hLam A (visitActiveInterval c) ⊤)).comp
        (measurable_coreAllTimePole c))

/-- Its physical occupation mass has the exact quadratic upper bound independent of pole time. -/
theorem coreAllTimeGreenKernel_mass_le
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (p : Point) :
    coreAllTimeGreenKernel hH hLE hlam hLam A c p univ ≤
      ENNReal.ofReal (9 * c.r ^ 2 / (32 * lam)) := by
  classical
  change (if hp : p.velocity 0 ∈ c.active then
    stripGreen hH hLE hlam hLam A (visitActiveInterval c) ⊤ (coreAllTimePole c ⟨p, hp⟩)
      else 0) univ ≤ _
  split
  · rename_i hp
    apply (stripGreen_quadratic_mass hH hLE hlam hLam A (visitActiveInterval c) ⊤
      (coreAllTimePole c ⟨p, hp⟩)).trans
    apply ENNReal.ofReal_le_ofReal
    change visitQuadratic c (p.velocity 0) / (2 * lam) ≤ 9 * c.r ^ 2 / (32 * lam)
    calc
      _ ≤ (9 * c.r ^ 2 / 16) / (2 * lam) :=
        div_le_div_of_nonneg_right (visitQuadratic_le c _) (by positivity)
      _ = _ := by field_simp; ring
  · exact zero_le

/-- The actual all-time active-strip kernel is uniformly finite. -/
instance coreAllTimeGreenKernel_isFiniteKernel
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) :
    IsFiniteKernel (coreAllTimeGreenKernel hH hLE hlam hLam A c) :=
  ⟨ENNReal.ofReal (9 * c.r ^ 2 / (32 * lam)), ENNReal.ofReal_lt_top,
    coreAllTimeGreenKernel_mass_le hH hLE hlam hLam A c⟩

/-- The actual physical all-time Green measure started from a physical counting measure. -/
def coreAllTimeGreenMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (nu : Measure Point) : Measure Point :=
  coreAllTimeGreenKernel hH hLE hlam hLam A c ∘ₘ nu

/-- Finite starting mass gives a finite actual all-time active Green mixture. -/
instance coreAllTimeGreenMeasure_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (nu : Measure Point) [IsFiniteMeasure nu] :
    IsFiniteMeasure (coreAllTimeGreenMeasure hH hLE hlam hLam A c nu) := by
  unfold coreAllTimeGreenMeasure
  infer_instance

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
