module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import HypoellipticAleksandrov.Coefficients.Ellipticity
public import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.SpatialBlock
public import HypoellipticAleksandrov.KineticAleksandrov.Operator

/-!
# Straightened viscous coefficients for the truncation problem

For a smooth curve `g = γ_k` and a viscosity `ε`, the change of variable `Y = y - g(σ)` turns
the viscous transported operator `∂σ + B : D_y² + b(y) · ∇_z + ε Δ_z` into the scalar backward
operator on `(σ, (Y, z))` with block diffusion `diag(B(σ, g + Y, z), ε I)` and drift
`(-g'(σ), b(g(σ) + Y))`.  This module defines that coefficient and drift and proves the
premises of the classical smooth-data Dirichlet solvability theorem (Lieberman, Theorem 5.14)
`exists_isClassicalBackwardDirichletSolution_openEllipsoid_uniqueOn_of_lieberman` for them:
smoothness, pointwise symmetry, the Loewner bounds `min(lam, ε) ≤ · ≤ max(Lam, ε)`, and
smoothness of the (possibly unbounded) drift.  That theorem is not used in this file.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open scoped MatrixOrder ContDiff

namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The straightened block coefficient `diag(B(σ, g(σ) + Y, z), ε I)` on `(Y, z)`. -/
noncomputable def straightenedCoefficient {n : ℕ} (B : FullKineticCoefficient n)
    (g : ℝ → PDE.Vec n) (ε : ℝ) : CoefficientField (n + n) :=
  fun s x => viscousBlockMatrix (B s (g s + spatialY x) (spatialZ x)) ε

/-- The straightened drift `(-g'(σ), b(g(σ) + Y))` on `(Y, z)`. -/
noncomputable def straightenedDrift {n : ℕ} (b : PDE.Vec n → PDE.Vec n)
    (g : ℝ → PDE.Vec n) : ℝ → PDE.Vec (n + n) → PDE.Vec (n + n) :=
  fun s x => spatialPack (-deriv g s) (b (g s + spatialY x))

section Evaluation

variable {n : ℕ}

theorem straightenedCoefficient_apply (B : FullKineticCoefficient n) (g : ℝ → PDE.Vec n)
    (ε : ℝ) (s : ℝ) (x : PDE.Vec (n + n)) :
    straightenedCoefficient B g ε s x =
      viscousBlockMatrix (B s (g s + spatialY x) (spatialZ x)) ε :=
  rfl

theorem straightenedDrift_apply (b : PDE.Vec n → PDE.Vec n) (g : ℝ → PDE.Vec n) (s : ℝ)
    (x : PDE.Vec (n + n)) :
    straightenedDrift b g s x = spatialPack (-deriv g s) (b (g s + spatialY x)) :=
  rfl

end Evaluation

section Premises

variable {n : ℕ} {lam Lam : ℝ} {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}

/-- The derivative of a smooth curve is smooth. -/
theorem contDiff_deriv_of_smooth {g : ℝ → PDE.Vec n} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (deriv g) :=
  (contDiff_infty_iff_deriv.mp hg).2

/-- The straightened coefficient is a smooth coefficient field. -/
theorem isSmoothCoefficient_straightenedCoefficient
    (hB_smooth : IsSmoothFullKineticCoefficient B)
    {g : ℝ → PDE.Vec n} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (ε : ℝ) :
    IsSmoothCoefficient (straightenedCoefficient B g ε) := by
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun z i j => coefficientAt (straightenedCoefficient B g ε) z i j)
  refine contDiff_pi.2 fun k => contDiff_pi.2 fun l => ?_
  have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × PDE.Vec (n + n) =>
      (q.1, (g q.1 + spatialY q.2, spatialZ q.2))) :=
    contDiff_fst.prodMk
      (((hg.comp contDiff_fst).add (contDiff_spatialY.comp contDiff_snd)).prodMk
        (contDiff_spatialZ.comp contDiff_snd))
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) l
  · simp only [coefficientAt, straightenedCoefficient_apply,
      viscousBlockMatrix_castAdd_castAdd]
    exact (hB_smooth i j).comp hmap
  all_goals simp only [coefficientAt, straightenedCoefficient_apply,
    viscousBlockMatrix_castAdd_addNat, viscousBlockMatrix_addNat_castAdd,
    viscousBlockMatrix_addNat_addNat, Fin.natAdd_eq_addNat]
  · exact contDiff_const
  · exact contDiff_const
  · exact contDiff_const

/-- The straightened coefficient is pointwise symmetric. -/
theorem isSymm_straightenedCoefficient
    (hB_symm : IsSymmetricFullKineticCoefficient B)
    (g : ℝ → PDE.Vec n) (ε : ℝ) (s : ℝ) (x : PDE.Vec (n + n)) :
    (straightenedCoefficient B g ε s x).IsSymm :=
  viscousBlockMatrix_isSymm (hB_symm s _ _) ε

/-- Lower Loewner bound `min(lam, ε) ≤ diag(B, ε I)`. -/
theorem straightenedCoefficient_lower
    (hB_ell : HasEverywhereLoewnerBounds lam Lam B)
    (g : ℝ → PDE.Vec n) (ε : ℝ) (s : ℝ) (x : PDE.Vec (n + n)) :
    min lam ε • (1 : PDE.Mat (n + n)) ≤ straightenedCoefficient B g ε s x := by
  rw [← viscousBlockMatrix_smul_one (min lam ε)]
  exact viscousBlockMatrix_mono
    ((smul_one_le_smul_one (min_le_left lam ε)).trans (hB_ell s _ _).1) (min_le_right lam ε)

/-- Upper Loewner bound `diag(B, ε I) ≤ max(Lam, ε)`. -/
theorem straightenedCoefficient_upper
    (hB_ell : HasEverywhereLoewnerBounds lam Lam B)
    (g : ℝ → PDE.Vec n) (ε : ℝ) (s : ℝ) (x : PDE.Vec (n + n)) :
    straightenedCoefficient B g ε s x ≤ max Lam ε • (1 : PDE.Mat (n + n)) := by
  rw [← viscousBlockMatrix_smul_one (max Lam ε)]
  exact viscousBlockMatrix_mono
    ((hB_ell s _ _).2.trans (smul_one_le_smul_one (le_max_left Lam ε))) (le_max_right Lam ε)

/-- The straightened drift is smooth; no growth bound on `b` is needed. -/
theorem contDiff_straightenedDrift (hb_smooth : IsSmoothDrift b)
    {g : ℝ → PDE.Vec n} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun q : TimeVelocity (n + n) => straightenedDrift b g q.1 q.2) := by
  refine contDiff_spatialPack ((contDiff_deriv_of_smooth hg).comp contDiff_fst).neg ?_
  exact hb_smooth.comp ((hg.comp contDiff_fst).add (contDiff_spatialY.comp contDiff_snd))

/-- Discharge of the coefficient and drift premises of the classical Dirichlet solvability theorem
for the straightened viscous problem.  The hypotheses are exactly the coefficient and drift
part of the standing source data; the viscosity enters only through the explicit Loewner
bounds `min(lam, ε)` and `max(Lam, ε)`. -/
theorem straightenedCoefficient_bounds_smooth
    (hB_smooth : IsSmoothFullKineticCoefficient B)
    (hB_symm : IsSymmetricFullKineticCoefficient B)
    (hB_ell : HasEverywhereLoewnerBounds lam Lam B)
    (hb_smooth : IsSmoothDrift b)
    (g : ℝ → PDE.Vec n) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (ε : ℝ) :
    IsSmoothCoefficient (straightenedCoefficient B g ε) ∧
    (∀ s x, (straightenedCoefficient B g ε s x).IsSymm) ∧
    (∀ s x, min lam ε • (1 : PDE.Mat (n + n)) ≤ straightenedCoefficient B g ε s x) ∧
    (∀ s x, straightenedCoefficient B g ε s x ≤ max Lam ε • (1 : PDE.Mat (n + n))) ∧
    ContDiff ℝ (⊤ : ℕ∞)
      (fun q : TimeVelocity (n + n) => straightenedDrift b g q.1 q.2) :=
  ⟨isSmoothCoefficient_straightenedCoefficient hB_smooth hg ε,
    isSymm_straightenedCoefficient hB_symm g ε,
    straightenedCoefficient_lower hB_ell g ε,
    straightenedCoefficient_upper hB_ell g ε,
    contDiff_straightenedDrift hb_smooth hg⟩

/-- The two elementary scalar side conditions of the Dirichlet solvability theorem: `0 < min(lam,
ε)` and `min(lam, ε) ≤ max(Lam, ε)`. -/
theorem straightened_ellipticity_constants (hlam : 0 < lam) (hlamLam : lam ≤ Lam) {ε : ℝ}
    (hε : 0 < ε) : 0 < min lam ε ∧ min lam ε ≤ max Lam ε :=
  ⟨lt_min hlam hε, (min_le_left lam ε).trans (hlamLam.trans (le_max_left Lam ε))⟩

end Premises

end HypoellipticAleksandrov.KineticAleksandrov
