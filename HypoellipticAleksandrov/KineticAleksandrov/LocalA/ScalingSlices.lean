module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.Geometry
public import HypoellipticAleksandrov.KineticAleksandrov.Operator
public import HypoellipticAleksandrov.Parabolic.ScalarClassical

/-! # Fixed-position parabolic slices of the normalized kinetic equation -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set Parabolic

/-- The fixed-position embedding is continuous in the literal physical coordinates. -/
theorem continuous_fixedPosition {d : ℕ} (x : PDE.Vec d) :
    Continuous (fun z : TimeVelocity d => (⟨z.1, x, z.2⟩ : KineticPoint d)) :=
  KineticPoint.continuous_mk continuous_fst continuous_const continuous_snd

/-- Restriction to a fixed position preserves the anisotropic scalar regularity. -/
theorem kineticC112_fixedPosition {d : ℕ} {u : KineticPoint d → ℝ}
    {D : Set (KineticPoint d)} {E : Set (TimeVelocity d)}
    (hu : IsKineticC112On u D) (x : PDE.Vec d)
    (hE : ∀ z ∈ E, (⟨z.1, x, z.2⟩ : KineticPoint d) ∈ D) :
    IsScalarC12On (fun z => u ⟨z.1, x, z.2⟩) E := by
  have hc : ContinuousOn
      (fun z : TimeVelocity d => (⟨z.1, x, z.2⟩ : KineticPoint d)) E :=
    (continuous_fixedPosition x).continuousOn
  refine ⟨hu.continuousOn.comp hc hE, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact hu.timeSlice_differentiableAt (hE z hz)
  · intro z hz
    exact hu.velocitySlice_contDiffAt (hE z hz)
  · exact hu.continuousOn_kineticTimeDerivative.comp hc hE
  · exact hu.continuousOn_kineticVelocityGradient.comp hc hE
  · exact hu.continuousOn_kineticVelocityHessian.comp hc hE

/-- The source's fixed-position parabolic cylinder lies inside the unit kinetic cylinder. -/
theorem normalized_slice_mem {d : ℕ} (x : PDE.Vec d)
    (hx : x ∈ PDE.euclideanBall 0 (1 / 8 : ℝ))
    (z : TimeVelocity d)
    (hz : z ∈ scalarParabolicOpenCylinder (-9 / 16) 0
      (PDE.euclideanBall 0 (3 / 4 : ℝ))) :
    (⟨z.1, x, z.2⟩ : KineticPoint d) ∈
      backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 := by
  rcases hz with ⟨⟨htlo, hthi⟩, hv⟩
  change (0 : ℝ) - 1 ^ 2 < z.1 ∧ z.1 < 0 ∧
    z.2 ∈ PDE.euclideanBall 0 1 ∧
    relativePosition (⟨0, 0, 0⟩ : KineticPoint d) ⟨z.1, x, z.2⟩ ∈
      PDE.euclideanBall 0 (1 ^ 3)
  refine ⟨by linarith only [htlo], hthi, ?_, ?_⟩
  · exact PDE.euclideanBall_mono (by norm_num) (by norm_num) hv
  · simpa only [relativePosition, sub_zero, smul_zero, one_pow] using
      PDE.euclideanBall_mono (by norm_num) (by norm_num : (1 / 8 : ℝ) ≤ 1) hx

/-- The normalized homogeneous kinetic equation is the forced scalar slice equation. -/
theorem normalized_slice_equation {d : ℕ}
    (A : CoefficientField d) (u : KineticPoint d → ℝ)
    (hu : IsKineticC112On u (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1))
    (he : ∀ P ∈ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1,
      backwardOperatorOfTimeVelocityCoefficient A u P = 0)
    (x : PDE.Vec d) (hx : x ∈ PDE.euclideanBall 0 (1 / 8 : ℝ)) :
    let w : TimeVelocity d → ℝ := fun z => u ⟨z.1, x, z.2⟩
    IsScalarC12On w (scalarParabolicOpenCylinder (-9 / 16) 0
      (PDE.euclideanBall 0 (3 / 4 : ℝ))) ∧
    ∀ z ∈ scalarParabolicOpenCylinder (-9 / 16) 0
        (PDE.euclideanBall 0 (3 / 4 : ℝ)),
      scalarTimeDerivative w z - matrixContraction (coefficientAt A z)
        (scalarSpatialHessian w z) =
      -PDE.vecDot z.2 (kineticPositionGradient u ⟨z.1, x, z.2⟩) := by
  dsimp only
  refine ⟨kineticC112_fixedPosition hu x (normalized_slice_mem x hx), ?_⟩
  intro z hz
  have h := he ⟨z.1, x, z.2⟩ (normalized_slice_mem x hx z hz)
  rw [backwardOperatorOfTimeVelocityCoefficient_apply] at h
  change kineticTimeDerivative u ⟨z.1, x, z.2⟩ -
    matrixContraction (A z.1 z.2) (kineticVelocityHessian u ⟨z.1, x, z.2⟩) = _
  linarith only [h]

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
