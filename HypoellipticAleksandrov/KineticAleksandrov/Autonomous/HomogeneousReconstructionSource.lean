module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ScalarAdapters

/-! # The actual bounded Borel source of a regular strip test

The negative kinetic operator is extended by zero outside the open strip. Its
boundedness and measurability follow from the source test hypotheses, not a new premise.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open Parabolic

/-- The reconstruction regularity domain is open. -/
theorem isOpen_reconstructionStrip (H : Interval) (sMinus T : ℝ) :
    IsOpen (reconstructionStrip H sMinus T) :=
  (isOpen_Ioi.preimage continuous_time).inter (isOpen_stripPast H T)

/-- A C112 test has a continuous scalar kinetic operator on its regularity set. -/
theorem continuousOn_forwardScalarOperator {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    {D : Set Point} {phi : Point → ℝ} (hphi : IsKineticC112On phi D) :
    ContinuousOn (forwardScalarOperator A.a phi) D := by
  have hx : Continuous (fun p : Point => p.position 0) :=
    (continuous_apply 0).comp continuous_position
  have hv : Continuous (fun p : Point => p.velocity 0) :=
    (continuous_apply 0).comp continuous_velocity
  have ha : Continuous (fun p : Point => A.a (p.position 0) (p.velocity 0)) :=
    A.smooth.continuous.comp (hx.prodMk hv)
  have hg := (continuous_apply 0).comp_continuousOn
    hphi.continuousOn_kineticPositionGradient
  have hh := (continuous_apply 0).comp_continuousOn
    ((continuous_apply 0).comp_continuousOn hphi.continuousOn_kineticVelocityHessian)
  exact (hphi.continuousOn_kineticTimeDerivative.add (hv.continuousOn.mul hg)).add
    (ha.continuousOn.mul hh)

/-- The source assumptions supply an actual zero-extended bounded Borel negative operator. -/
theorem exists_bounded_reconstruction_source {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (H : Interval) (sMinus T : ℝ) (phi : Point → ℝ)
    (hphi : IsKineticC112On phi (reconstructionStrip H sMinus T))
    (hb : ∃ M : ℝ, ∀ p ∈ reconstructionStrip H sMinus T,
      |phi p| ≤ M ∧ |forwardScalarOperator A.a phi p| ≤ M) :
    ∃ g : BoundedBorel Point,
      (∀ p ∈ reconstructionStrip H sMinus T, g p = -forwardScalarOperator A.a phi p) ∧
      (∀ p ∉ reconstructionStrip H sMinus T, g p = 0) := by
  classical
  obtain ⟨M, hM⟩ := hb
  let D := reconstructionStrip H sMinus T
  let f : Point → ℝ := D.piecewise (fun p => -forwardScalarOperator A.a phi p) (fun _ => 0)
  have hm : Measurable f :=
    (continuousOn_forwardScalarOperator A hphi).neg.measurable_piecewise
      continuous_const.continuousOn (isOpen_reconstructionStrip H sMinus T).measurableSet
  have hb' : ∀ p, |f p| ≤ max M 0 := by
    intro p
    by_cases hp : p ∈ D
    · dsimp only [f]
      rw [piecewise_eq_of_mem D _ _ hp, abs_neg]
      exact (hM p hp).2.trans (le_max_left _ _)
    · dsimp only [f]
      rw [piecewise_eq_of_notMem D _ _ hp, abs_zero]
      exact le_max_right _ _
  let g : BoundedBorel Point := ⟨f, hm, ⟨max M 0, le_max_right _ _, hb'⟩⟩
  refine ⟨g, ?_, ?_⟩
  · intro p hp
    change f p = _
    dsimp only [f]
    exact piecewise_eq_of_mem D _ _ hp
  · intro p hp
    change f p = _
    dsimp only [f]
    exact piecewise_eq_of_notMem D _ _ hp

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
