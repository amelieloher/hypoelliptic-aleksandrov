module

public import HypoellipticAleksandrov.KineticAleksandrov.Lieberman.Assembly
public import HypoellipticAleksandrov.KineticAleksandrov.EllipsoidDirichlet
public import HypoellipticAleksandrov.Parabolic.ScalarDirichletData

/-!
# Classical Dirichlet solvability (Lieberman)

Existence and uniqueness for the terminal Cauchy–Dirichlet problem with smooth data on a
smooth ellipsoidal cylinder (Lieberman, Theorem 5.14).
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open Set
open HypoellipticAleksandrov
open HypoellipticAleksandrov.Parabolic
open scoped MatrixOrder

namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The smooth ellipsoidal Dirichlet statement, with
uniqueness on the closed cylinder. -/
theorem exists_isClassicalBackwardDirichletSolution_openEllipsoid_uniqueOn_of_lieberman
    {N : ℕ} {r₀ r₁ : ℝ} {Q : PDE.Mat N}
    (hQ : Q.PosDef)
    (hr : r₀ < r₁)
    (lam Lam : ℝ)
    (hlam : 0 < lam)
    (hlamLam : lam ≤ Lam)
    (a : CoefficientField N)
    (b : ℝ → PDE.Vec N → PDE.Vec N)
    (haSymm : ∀ t v, (a t v).IsSymm)
    (haSmooth : IsSmoothCoefficient a)
    (haLower : ∀ t v, lam • (1 : PDE.Mat N) ≤ a t v)
    (haUpper : ∀ t v, a t v ≤ Lam • (1 : PDE.Mat N))
    (hbSmooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : TimeVelocity N => b z.1 z.2))
    (φ : PDE.Vec N → ℝ)
    (hφSmooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφCompact : HasCompactSupport φ)
    (hφSupport : tsupport φ ⊆ openEllipsoid Q) :
    ∃ u : TimeVelocity N → ℝ,
      IsClassicalBackwardDirichletSolution
        r₀ r₁ (openEllipsoid Q) a b
        (fun _ _ => 0) (fun _ _ => 0) φ (fun _ => 0) u ∧
      ∀ v : TimeVelocity N → ℝ,
        IsClassicalBackwardDirichletSolution
          r₀ r₁ (openEllipsoid Q) a b
          (fun _ _ => 0) (fun _ _ => 0) φ (fun _ => 0) v →
          Set.EqOn v u
            (scalarParabolicClosedCylinder r₀ r₁ (openEllipsoid Q)) := by
  exact HypoellipticAleksandrov.KineticAleksandrov.ellipsoidDirichlet_aux
    hQ hr lam Lam hlam hlamLam a b haSymm haSmooth haLower haUpper
    hbSmooth φ hφSmooth hφCompact hφSupport

end HypoellipticAleksandrov.KineticAleksandrov
