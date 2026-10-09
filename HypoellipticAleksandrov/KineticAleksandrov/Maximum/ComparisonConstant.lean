module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonLinear
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! # Constant shifts in the classical kinetic comparison argument -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov.Parabolic Set

/-- All classical kinetic derivatives of a constant vanish. -/
theorem comparison_const_formulas {d : ℕ} (c : ℝ) (P : KineticPoint d) :
    kineticTimeDerivative (fun _ : KineticPoint d => c) P = 0 ∧
    kineticPositionGradient (fun _ : KineticPoint d => c) P = 0 ∧
    kineticVelocityGradient (fun _ : KineticPoint d => c) P = 0 ∧
    kineticVelocityHessian (fun _ : KineticPoint d => c) P = 0 := by
  refine ⟨deriv_const _ _,?_,?_,?_⟩
  · ext i
    simp [kineticPositionGradient, PDE.classicalGradient]
  · ext i
    simp [kineticVelocityGradient, PDE.classicalGradient]
  · have hg : (fun v : PDE.Vec d => PDE.classicalGradient (fun _ : PDE.Vec d => c) v) =
        fun _ => 0 := by
      funext v
      ext i
      simp [PDE.classicalGradient]
    unfold kineticVelocityHessian
    rw [hg]
    ext i j
    simp

/-- Constants belong to the exact anisotropic kinetic classical class on every set. -/
theorem comparison_regular_const {d : ℕ} (c : ℝ) (D : Set (KineticPoint d)) :
    IsKineticC112On (fun _ : KineticPoint d => c) D := by
  refine ⟨continuousOn_const,fun _ _ => differentiableAt_const c,
    fun _ _ => contDiffAt_const,fun _ _ => contDiffAt_const,?_,?_,?_,?_⟩
  · have h : kineticTimeDerivative (fun _ : KineticPoint d => c) = fun _ => 0 :=
      funext fun P => (comparison_const_formulas c P).1
    rw [h]
    exact continuousOn_const
  · have h : kineticPositionGradient (fun _ : KineticPoint d => c) = fun _ => 0 :=
      funext fun P => (comparison_const_formulas c P).2.1
    rw [h]
    exact continuousOn_const
  · have h : kineticVelocityGradient (fun _ : KineticPoint d => c) = fun _ => 0 :=
      funext fun P => (comparison_const_formulas c P).2.2.1
    rw [h]
    exact continuousOn_const
  · have h : kineticVelocityHessian (fun _ : KineticPoint d => c) = fun _ => 0 :=
      funext fun P => (comparison_const_formulas c P).2.2.2
    rw [h]
    exact continuousOn_const

/-- The general forward kinetic operator annihilates constants. -/
theorem comparison_forwardOperator_const {d : ℕ}
    (A : FullKineticCoefficient d) (c : ℝ) (P : KineticPoint d) :
    forwardKineticOperator A (fun _ : KineticPoint d => c) P = 0 := by
  obtain ⟨ht,hx,_,hv⟩ := comparison_const_formulas c P
  rw [forwardKineticOperator_apply,ht,hx,hv]
  simp [PDE.vecDot, HypoellipticAleksandrov.matrixContraction]

/-- Restriction to a smaller set preserves the exact anisotropic classical class. -/
theorem comparison_regular_mono {d : ℕ} {u : KineticPoint d → ℝ}
    {D S : Set (KineticPoint d)} (hu : IsKineticC112On u D) (hSD : S ⊆ D) :
    IsKineticC112On u S :=
  ⟨hu.continuousOn.mono hSD,
    fun _ hp => hu.timeSlice_differentiableAt (hSD hp),
    fun _ hp => hu.positionSlice_contDiffAt (hSD hp),
    fun _ hp => hu.velocitySlice_contDiffAt (hSD hp),
    hu.continuousOn_kineticTimeDerivative.mono hSD,
    hu.continuousOn_kineticPositionGradient.mono hSD,
    hu.continuousOn_kineticVelocityGradient.mono hSD,
    hu.continuousOn_kineticVelocityHessian.mono hSD⟩

end HypoellipticAleksandrov.KineticAleksandrov
