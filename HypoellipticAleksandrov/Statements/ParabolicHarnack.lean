module

public import HypoellipticAleksandrov.Parabolic.ScalarClassical
public import HypoellipticAleksandrov.Parabolic.LocalClassical
public import PDEFoundation.Geometry.EuclideanBall.Basic
import HypoellipticAleksandrov.Parabolic.HarnackUnitCylinder.Assembly

/-!
# Parabolic Harnack inequality (Krylov–Safonov)

Companion paper, Theorem 3.5.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open scoped MatrixOrder

/-- The parabolic Harnack inequality, expressed as a comparison of every pair
of points in the lower and upper cylinders, with a uniform positive constant. -/
theorem parabolic_harnack_unit_cylinder
    (N : ℕ) (hN : 1 ≤ N) (lam : ℝ) (hlam : 0 < lam)
    (Lam : ℝ) (hlamLam : lam ≤ Lam) :
    ∃ h : ℝ, 0 < h ∧
      ∀ (B : CoefficientField N) (u : TimeVelocity N → ℝ),
        IsContinuousCoefficientOn B
          (Set.Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec N) 1) →
        (∀ z ∈ Set.Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec N) 1,
          (coefficientAt B z).IsSymm) →
        HasLowerEllipticityOn lam B
          (Set.Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec N) 1) →
        HasUpperEllipticityOn Lam B
          (Set.Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec N) 1) →
        IsScalarC12On u
          (Set.Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec N) 1) →
        IsNonnegativeOn u
          (Set.Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec N) 1) →
        (∀ z ∈ Set.Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec N) 1,
          scalarTimeDerivative u z =
            matrixContraction (coefficientAt B z) (scalarSpatialHessian u z)) →
        ∀ P ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2 : ℝ) ×ˢ
            PDE.euclideanBall (0 : PDE.Vec N) (1 / 2 : ℝ),
          ∀ P' ∈ Set.Ioo (3 / 4 : ℝ) 1 ×ˢ
              PDE.euclideanBall (0 : PDE.Vec N) (1 / 2 : ℝ),
            h * u P ≤ u P' := by
  exact HypoellipticAleksandrov.Parabolic.parabolic_harnack_unit_cylinder_aux
    N hN lam hlam Lam hlamLam

end HypoellipticAleksandrov.Parabolic
