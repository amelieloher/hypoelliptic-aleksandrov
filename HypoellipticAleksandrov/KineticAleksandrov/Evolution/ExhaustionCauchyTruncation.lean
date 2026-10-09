module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCauchyBound
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCauchyGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonEvolution

/-!
# Uniform bounds on the actual truncation solutions

The scalar maximum principle is applied directly to the centered ellipsoid and its
supplied classical Dirichlet solution. No full-domain solution is used.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set
open scoped MatrixOrder Matrix.Norms.Elementwise

/-- Every actual straightened finite Dirichlet solution has the original datum bound,
independent of the curve, both ellipsoid radii, and positive viscosity. -/
theorem abs_le_straightened_dirichlet {n : ℕ} {lam Lam : ℝ}
    {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (hlam : 0 < lam) (hB : HasEverywhereLoewnerBounds lam Lam B)
    (hBs : IsSmoothFullKineticCoefficient B) (hbs : IsSmoothDrift b)
    {a τ r R : ℝ} (haτ : a < τ) (hr : 0 < r) (hR : 0 < R)
    {g : ℝ → PDE.Vec n} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {ε : ℝ} (hε : 0 ≤ ε) (F : BoundedBorel (EvolutionAmbientState n))
    (u : TimeVelocity (n + n) → ℝ)
    (hu : IsClassicalBackwardDirichletSolution a τ
      (openEllipsoid (straightenedEllipsoidMatrix n r R))
      (straightenedCoefficient B g ε) (straightenedDrift b g)
      (fun _ _ => 0) (fun _ _ => 0)
      (fun x => F (g τ + spatialY x, spatialZ x)) (fun _ => 0) u)
    {C : ℝ} (hC : 0 ≤ C) (hFC : ∀ q, |F q| ≤ C) :
    ∀ q ∈ scalarParabolicClosedCylinder a τ
      (openEllipsoid (straightenedEllipsoidMatrix n r R)), |u q| ≤ C := by
  apply abs_le_of_classicalBackwardDirichlet_zero
    (isOpen_straightenedEllipsoid n hr hR) (isBounded_straightenedEllipsoid n hr hR)
    haτ (straightenedCoefficient B g ε) (straightenedDrift b g)
    (isSmoothCoefficient_straightenedCoefficient hBs hg ε).continuous
    (contDiff_straightenedDrift hbs hg).continuous
    (fun s x => ?_) _ u hu hC (fun x _ => hFC _)
  rw [straightenedCoefficient_apply]
  exact viscousBlockMatrix_posSemidef
    (posSemidef_of_hasEverywhereLoewnerBounds hlam.le hB _ _ _) hε

end HypoellipticAleksandrov.KineticAleksandrov
