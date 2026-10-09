module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionTerminalFamily

/-! # The measurable kernel of the canonical enlarged terminal family -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory
open scoped Classical

/-- The actual terminal family is measurable even on its zero-duration face. -/
theorem enlarged_terminal_family_measurable
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) :
    Measurable (enlargedActiveTerminalFamily hH hLE hlam hLam A c J b) := by
  let E := enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) b
  have hS : MeasurableSet {q : Point | q.time = b} :=
    (isClosed_eq continuous_time continuous_const).measurableSet
  have hm : Measurable (fun p => (E p).restrict {q | q.time = b}) :=
    Measure.measurable_of_measurable_coe _ fun B hB => by
      simp_rw [Measure.restrict_apply hB]
      exact E.measurable_coe (hB.inter hS)
  exact Measure.measurable_dirac.ite
    (hS.inter ((visitActiveUnion c J).isOpen_carrier.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)) hm

/-- Kernel packaging of the already defined actual terminal family. -/
def enlargedTerminalFamilyKernel
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) : Kernel Point Point :=
  ⟨enlargedActiveTerminalFamily hH hLE hlam hLam A c J b,
    enlarged_terminal_family_measurable hH hLE hlam hLam A c J b⟩

/-- The actual terminal kernel is uniformly finite with bound one. -/
instance enlargedTerminalFamilyKernel_isFiniteKernel
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) :
    IsFiniteKernel (enlargedTerminalFamilyKernel hH hLE hlam hLam A c J b) :=
  ⟨1, ENNReal.one_lt_top,
    enlarged_terminal_family_mass_le_one hH hLE hlam hLam A c J b⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
