module

public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Homeomorph.Defs
public import HypoellipticAleksandrov.KineticAleksandrov.EllipsoidDirichlet
import PDEFoundation.Geometry.EuclideanBall.Topology
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.SpatialBlock
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.StraightenedCoefficients

/-!
# Geometry of the straightened truncation

The truncated straightened domain is the open ellipsoid
`{(Y, z) : |Y|² / r² + |z|² / R² < 1}` of `PDE.Vec (n + n)`, written through the literal
block matrix `diag(r⁻² I, R⁻² I)` and the existing `openEllipsoid`.  This module proves the
block interpretation of that ellipsoid together with positive definiteness of its matrix,
the smoothness and compact support of the transformed terminal datum
`x ↦ F (g(τ) + Y, z)`, and the fact that every compactly supported datum lies in all
sufficiently large truncation ellipsoids.  Together with the coefficient discharge of
`StraightenedCoefficients` this verifies every premise of the smooth-data Dirichlet solvability
theorem (Lieberman, Theorem 5.14) for the straightened problem.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open scoped MatrixOrder ContDiff Matrix

namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The matrix `diag(r⁻² I, R⁻² I)` of the straightened truncation ellipsoid. -/
noncomputable def straightenedEllipsoidMatrix (n : ℕ) (r R : ℝ) : PDE.Mat (n + n) :=
  viscousBlockMatrix ((r ^ 2)⁻¹ • (1 : PDE.Mat n)) ((R ^ 2)⁻¹)

/-- Block form of the quadratic form of the ellipsoid matrix. -/
theorem vecDot_straightenedEllipsoidMatrix_mulVec (n : ℕ) (r R : ℝ) (x : PDE.Vec (n + n)) :
    PDE.vecDot x (straightenedEllipsoidMatrix n r R *ᵥ x) =
      PDE.vecNormSq (spatialY x) / r ^ 2 + PDE.vecNormSq (spatialZ x) / R ^ 2 := by
  rw [straightenedEllipsoidMatrix, vecDot_viscousBlockMatrix_mulVec]
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec, PDE.vecDot, PDE.vecNormSq, Pi.smul_apply,
    smul_eq_mul, div_eq_inv_mul, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The straightened ellipsoid matrix is positive definite and its open ellipsoid is
`{|Y|² / r² + |z|² / R² < 1}`. -/
theorem straightenedEllipsoid_characterization
    (n : ℕ) (r R : ℝ) (hr : 0 < r) (hR : 0 < R) :
    (straightenedEllipsoidMatrix n r R).PosDef ∧
    ∀ x : PDE.Vec (n + n),
      x ∈ openEllipsoid (straightenedEllipsoidMatrix n r R) ↔
        PDE.vecNormSq (spatialY x) / r ^ 2 + PDE.vecNormSq (spatialZ x) / R ^ 2 < 1 := by
  refine ⟨?_, fun x => ?_⟩
  · exact viscousBlockMatrix_posDef (Matrix.PosDef.one.smul (inv_pos.2 (pow_pos hr 2)))
      (inv_pos.2 (pow_pos hR 2))
  · change PDE.vecDot x (straightenedEllipsoidMatrix n r R *ᵥ x) < 1 ↔ _
    rw [vecDot_straightenedEllipsoidMatrix_mulVec]

section TerminalDatum

variable {n : ℕ}

/-- The affine terminal-coordinate homeomorphism `(Y, z) ↦ (c + Y, z)`. -/
def terminalCoordinateHomeomorph (c : PDE.Vec n) :
    PDE.Vec (n + n) ≃ₜ (PDE.Vec n × PDE.Vec n) where
  toFun x := (c + spatialY x, spatialZ x)
  invFun p := spatialPack (p.1 - c) p.2
  left_inv x := by simp
  right_inv p := by simp
  continuous_toFun :=
    ((contDiff_const.add contDiff_spatialY).prodMk (contDiff_spatialZ (m := 0))).continuous
  continuous_invFun :=
    (contDiff_spatialPack (contDiff_fst.sub contDiff_const) contDiff_snd (m := 0)).continuous

/-- The transformed terminal datum `x ↦ F (c + Y, z)` of a smooth datum is smooth. -/
theorem contDiff_terminalDatum (c : PDE.Vec n) {F : PDE.Vec n × PDE.Vec n → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : PDE.Vec (n + n) => F (c + spatialY x, spatialZ x)) :=
  hF.comp ((contDiff_const.add contDiff_spatialY).prodMk contDiff_spatialZ)

/-- The transformed terminal datum of a compactly supported datum has compact support: the
affine terminal-coordinate map is a homeomorphism, hence proper. -/
theorem hasCompactSupport_terminalDatum (c : PDE.Vec n) {F : PDE.Vec n × PDE.Vec n → ℝ}
    (hF : HasCompactSupport F) :
    HasCompactSupport (fun x : PDE.Vec (n + n) => F (c + spatialY x, spatialZ x)) :=
  hF.comp_homeomorph (terminalCoordinateHomeomorph c)

end TerminalDatum

section Exhaustion

variable {n : ℕ}

/-- A compactly supported function has support inside every sufficiently large straightened
ellipsoid, uniformly in both radii. -/
theorem exists_tsupport_subset_straightenedEllipsoid {φ : PDE.Vec (n + n) → ℝ}
    (hφ : HasCompactSupport φ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ r R : ℝ, ρ ≤ r → ρ ≤ R →
      tsupport φ ⊆ openEllipsoid (straightenedEllipsoidMatrix n r R) := by
  obtain ⟨M, hM⟩ := hφ.bddAbove_image (PDE.continuous_vecNormSq (d := n + n)).continuousOn
  refine ⟨|M| + 1, by positivity, fun r R hr hR x hx => ?_⟩
  have hρ : 0 < |M| + 1 := by positivity
  have hr0 : 0 < r := lt_of_lt_of_le hρ hr
  have hR0 : 0 < R := lt_of_lt_of_le hρ hR
  rw [(straightenedEllipsoid_characterization n r R hr0 hR0).2]
  have hxM : PDE.vecNormSq x ≤ M := hM ⟨x, hx, rfl⟩
  have hρ2 : |M| + 1 ≤ (|M| + 1) ^ 2 := by nlinarith [abs_nonneg M]
  have hMlt : PDE.vecNormSq x < (|M| + 1) ^ 2 := by
    nlinarith [le_abs_self M]
  have h1 : PDE.vecNormSq (spatialY x) / r ^ 2 ≤ PDE.vecNormSq (spatialY x) / (|M| + 1) ^ 2 :=
    div_le_div_of_nonneg_left (PDE.vecNormSq_nonneg _) (by positivity)
      (pow_le_pow_left₀ hρ.le hr 2)
  have h2 : PDE.vecNormSq (spatialZ x) / R ^ 2 ≤ PDE.vecNormSq (spatialZ x) / (|M| + 1) ^ 2 :=
    div_le_div_of_nonneg_left (PDE.vecNormSq_nonneg _) (by positivity)
      (pow_le_pow_left₀ hρ.le hR 2)
  calc PDE.vecNormSq (spatialY x) / r ^ 2 + PDE.vecNormSq (spatialZ x) / R ^ 2
      ≤ PDE.vecNormSq (spatialY x) / (|M| + 1) ^ 2 +
          PDE.vecNormSq (spatialZ x) / (|M| + 1) ^ 2 := add_le_add h1 h2
    _ = PDE.vecNormSq x / (|M| + 1) ^ 2 := by rw [vecNormSq_eq_spatial, add_div]
    _ < 1 := (div_lt_one (by positivity)).2 hMlt

end Exhaustion

section AnchorPremises

variable {n : ℕ} {lam Lam : ℝ} {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}

/-- Every premise of the smooth-data Dirichlet solvability theorem
(`exists_isClassicalBackwardDirichletSolution_openEllipsoid_uniqueOn_of_lieberman`) that concerns
the geometry, the straightened coefficient, the drift and the transformed terminal datum, in
dimension `N = n + n`, for the ellipsoid matrix `Q = diag(r⁻² I, R⁻² I)`, the coefficient
`straightenedCoefficient B g ε`, the drift `straightenedDrift b g`, the constants
`min(lam, ε) ≤ max(Lam, ε)` and the datum `φ(x) = F (g(τ) + Y, z)`.  The order of the
conjuncts is that of the theorem's binders `hQ`, `hlam`, `hlamLam`, `haSymm`, `haSmooth`,
`haLower`, `haUpper`, `hbSmooth`, `hφSmooth`, `hφCompact`; the support inclusion
`hφSupport` and `r₀ < r₁` are supplied data and are not repeated. -/
theorem straightened_base_premises
    (hB_smooth : IsSmoothFullKineticCoefficient B)
    (hB_symm : IsSymmetricFullKineticCoefficient B)
    (hB_ell : HasEverywhereLoewnerBounds lam Lam B) (hb_smooth : IsSmoothDrift b)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (r R : ℝ) (hr : 0 < r) (hR : 0 < R)
    (g : ℝ → PDE.Vec n) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (ε : ℝ) (hε : 0 < ε)
    (τ : ℝ) {F : PDE.Vec n × PDE.Vec n → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F) :
    (straightenedEllipsoidMatrix n r R).PosDef ∧
    0 < min lam ε ∧ min lam ε ≤ max Lam ε ∧
    (∀ s x, (straightenedCoefficient B g ε s x).IsSymm) ∧
    IsSmoothCoefficient (straightenedCoefficient B g ε) ∧
    (∀ s x, min lam ε • (1 : PDE.Mat (n + n)) ≤ straightenedCoefficient B g ε s x) ∧
    (∀ s x, straightenedCoefficient B g ε s x ≤ max Lam ε • (1 : PDE.Mat (n + n))) ∧
    ContDiff ℝ (⊤ : ℕ∞)
      (fun q : TimeVelocity (n + n) => straightenedDrift b g q.1 q.2) ∧
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x : PDE.Vec (n + n) => F (g τ + spatialY x, spatialZ x)) ∧
    HasCompactSupport (fun x : PDE.Vec (n + n) => F (g τ + spatialY x, spatialZ x)) := by
  obtain ⟨hsm, hsy, hlo, hup, hdr⟩ :=
    straightenedCoefficient_bounds_smooth hB_smooth hB_symm hB_ell hb_smooth g hg ε
  obtain ⟨h0, h1⟩ := straightened_ellipticity_constants hlam hlamLam hε
  exact ⟨(straightenedEllipsoid_characterization n r R hr hR).1, h0, h1, hsy, hsm, hlo, hup,
    hdr, contDiff_terminalDatum (g τ) hF, hasCompactSupport_terminalDatum (g τ) hFc⟩

end AnchorPremises

end HypoellipticAleksandrov.KineticAleksandrov
