module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementEnergyBoundary
public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementSmoothResidual
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonCalculus
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparison
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.LocalizedKrylovRegularity

/-! # Homogeneous replacement for smooth ambient boundary extensions

Subtracting the internally proved signed correction leaves the homogeneous equation
and preserves the actual terminal and lateral boundary data.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Set KineticAleksandrov
open scoped MatrixOrder Matrix.Norms.Elementwise

/-- Smooth ambient boundary data have a homogeneous classical backward replacement. -/
theorem exists_smooth_backward_homogeneous_replacement {d : ℕ} (hd : 0 < d)
    (v₀ : PDE.Vec d) (r : ℝ) (hr : 0 < r) (a T : ℝ) (haT : a < T)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : CoefficientField d) (hA : IsSmoothCoefficient A)
    (hlo : HasLowerEllipticity lam A) (hhi : HasUpperEllipticity Lam A)
    (w : TimeVelocity d → ℝ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) :
    ∃ v : TimeVelocity d → ℝ,
      IsClassicalBackwardDirichletSolution a T (PDE.euclideanBall v₀ r) A
        (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
        (fun y => w (T, y)) w v := by
  let F : TimeVelocity d → ℝ := fun z => scalarTimeDerivative w z +
    matrixContraction (coefficientAt A z) (scalarSpatialHessian w z)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := contDiff_smooth_backward_residual A hA w hw
  obtain ⟨u, hu⟩ := exists_signed_source_ball_correction hd v₀ r hr a T haT
    lam Lam hlam hLam A hA hlo hhi F hF
  have hwr := isScalarC12On_of_contDiff_two (hw.of_le (by simp))
    (scalarParabolicOpenCylinder a T (PDE.euclideanBall v₀ r))
  refine ⟨fun z => w z - u z,
    hw.continuous.continuousOn.sub hu.1, isScalarC12On_sub hwr hu.2.1, ?_, ?_, ?_⟩
  · intro z hz
    rw [scalarParabolicZeroOrderOperator_sub A (fun _ _ => 0) (fun _ _ => 0)
      hwr hu.2.1 hz, hu.2.2.1 z hz]
    have hwF : scalarParabolicZeroOrderOperator A (fun _ _ => 0) (fun _ _ => 0) w z = F z := by
      simp only [scalarParabolicZeroOrderOperator_apply, Pi.zero_apply, PDE.vecDot,
        zero_mul, Finset.sum_const_zero, add_zero]
      rfl
    rw [hwF, sub_self]
  · intro y hy
    change w (T, y) - u (T, y) = w (T, y)
    rw [hu.2.2.2.1 y hy, sub_zero]
  · intro z hz
    change w z - u z = w z
    rw [hu.2.2.2.2 z hz, sub_zero]

/-- The smooth replacement obeys the exact pointwise source-amplitude error bound. -/
theorem exists_smooth_backward_homogeneous_replacement_with_bound {d : ℕ} (hd : 0 < d)
    (v₀ : PDE.Vec d) (r : ℝ) (hr : 0 < r) (a T : ℝ) (haT : a < T)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : CoefficientField d) (hA : IsSmoothCoefficient A)
    (hlo : HasLowerEllipticity lam A) (hhi : HasUpperEllipticity Lam A)
    (w : TimeVelocity d → ℝ) (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (M : ℝ) (hM : 0 ≤ M)
    (hMbound : ∀ z ∈ scalarParabolicOpenCylinder a T (PDE.euclideanBall v₀ r),
      |scalarTimeDerivative w z +
        matrixContraction (coefficientAt A z) (scalarSpatialHessian w z)| ≤ M) :
    ∃ v : TimeVelocity d → ℝ,
      IsClassicalBackwardDirichletSolution a T (PDE.euclideanBall v₀ r) A
        (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
        (fun y => w (T, y)) w v ∧
      ∀ z ∈ scalarParabolicClosedCylinder a T (PDE.euclideanBall v₀ r),
        |w z - v z| ≤ M * (T - z.1) := by
  obtain ⟨v, hv⟩ := exists_smooth_backward_homogeneous_replacement hd v₀ r hr a T haT
    lam Lam hlam hLam A hA hlo hhi w hw
  let F : ℝ → PDE.Vec d → ℝ := fun t y => scalarTimeDerivative w (t, y) +
    matrixContraction (coefficientAt A (t, y)) (scalarSpatialHessian w (t, y))
  have hwr := isScalarC12On_of_contDiff_two (hw.of_le (by simp))
    (scalarParabolicOpenCylinder a T (PDE.euclideanBall v₀ r))
  have hu : IsClassicalBackwardDirichletSolution a T (PDE.euclideanBall v₀ r) A
      (fun _ _ => 0) (fun _ _ => 0) F (fun _ => 0) (fun _ => 0)
      (fun z => w z - v z) := by
    refine ⟨hw.continuous.continuousOn.sub hv.1, isScalarC12On_sub hwr hv.2.1, ?_, ?_, ?_⟩
    · intro z hz
      rw [scalarParabolicZeroOrderOperator_sub A (fun _ _ => 0) (fun _ _ => 0)
        hwr hv.2.1 hz, hv.2.2.1 z hz, sub_zero]
      simp only [scalarParabolicZeroOrderOperator_apply, Pi.zero_apply, PDE.vecDot,
        zero_mul, Finset.sum_const_zero, add_zero]
      rfl
    · intro y hy
      change w (T, y) - v (T, y) = 0
      rw [hv.2.2.2.1 y hy, sub_self]
    · intro z hz
      change w z - v z = 0
      rw [hv.2.2.2.2 z hz, sub_self]
  refine ⟨v, hv, ?_⟩
  exact abs_zeroBoundary_solution_le_time (PDE.isOpen_euclideanBall v₀ r)
    (Occupation.isBounded_euclideanBall v₀ hr) haT A hA.continuous
    (Occupation.posSemidef_of_lower_loewner hlam hlo) F M hM hMbound _ hu

end HypoellipticAleksandrov.Parabolic.LocalHolder
