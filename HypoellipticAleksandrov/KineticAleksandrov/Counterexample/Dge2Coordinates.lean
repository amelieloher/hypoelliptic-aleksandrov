module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2Seed
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Geometry
import Mathlib.Tactic.FieldSimp

/-!
# Euclidean coordinates of the homogeneous ansatz

The native vector norm is never used for the source's radial coordinates.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- The unit Euclidean position direction, defined by the literal normalization. -/
def positionDirection {d : ℕ} (x : PDE.Vec d) : PDE.Vec d :=
  (PDE.vecEuclideanNorm x)⁻¹ • x

/-- Velocity normalized by the cube root of the Euclidean position radius. -/
def normalizedVelocity {d : ℕ} (x v : PDE.Vec d) : PDE.Vec d :=
  Real.rpow (PDE.vecEuclideanNorm x) (-(1 / 3 : ℝ)) • v

/-- The literal homogeneous ansatz on nonzero positions. -/
def homogeneousAnsatz {d : ℕ} (alpha : ℝ)
    (phi : PDE.Vec d → PDE.Vec d → ℝ) (x v : PDE.Vec d) : ℝ :=
  Real.rpow (PDE.vecEuclideanNorm x) (alpha / 3) *
    phi (normalizedVelocity x v) (positionDirection x)

/-- The source transport expression, using the ambient derivative in a tangent direction. -/
def ansatzTransport {d : ℕ} (alpha : ℝ)
    (phi : PDE.Vec d → PDE.Vec d → ℝ) (y e : PDE.Vec d) : ℝ :=
  PDE.vecDot y e * (alpha / 3 * phi y e -
    (1 / 3 : ℝ) * fderiv ℝ (fun z => phi z e) y y) +
    fderiv ℝ (fun a => phi y a) e (y - PDE.vecDot y e • e)

/-- Normalizing a nonzero position gives a Euclidean unit vector. -/
theorem positionDirection_normSq {d : ℕ} (x : PDE.Vec d) (hx : x ≠ 0) :
    PDE.vecNormSq (positionDirection x) = 1 := by
  have hp : 0 < PDE.vecEuclideanNorm x := PDE.vecEuclideanNorm_pos_iff.mpr hx
  unfold positionDirection
  rw [PDE.vecNormSq_smul, ← PDE.vecEuclideanNorm_sq]
  field_simp

/-- Positive kinetic scaling preserves the position direction. -/
theorem positionDirection_dilate {d : ℕ} (r : ℝ) (hr : 0 < r) (x : PDE.Vec d) :
    positionDirection (r ^ 3 • x) = positionDirection x := by
  unfold positionDirection
  rw [PDE.vecEuclideanNorm_smul, abs_of_pos (pow_pos hr 3), mul_inv_rev, smul_smul]
  have h : (PDE.vecEuclideanNorm x)⁻¹ * (r ^ 3)⁻¹ * r ^ 3 =
      (PDE.vecEuclideanNorm x)⁻¹ := by
    field_simp
  rw [h]

/-- Positive kinetic scaling preserves the normalized velocity. -/
theorem normalizedVelocity_dilate {d : ℕ} (r : ℝ) (hr : 0 < r)
    (x v : PDE.Vec d) :
    normalizedVelocity (r ^ 3 • x) (r • v) = normalizedVelocity x v := by
  unfold normalizedVelocity
  rw [PDE.vecEuclideanNorm_smul, abs_of_pos (pow_pos hr 3)]
  simp only [Real.rpow_eq_pow]
  rw [Real.mul_rpow (pow_nonneg hr.le 3) (PDE.vecEuclideanNorm_nonneg x),
    ← Real.rpow_natCast_mul hr.le]
  norm_num
  rw [Real.rpow_neg_one, smul_smul]
  congr 1
  field_simp

/-- The homogeneous ansatz has the exact kinetic scaling of Appendix C. -/
theorem homogeneousAnsatz_dilate {d : ℕ} (alpha r : ℝ) (hr : 0 < r)
    (phi : PDE.Vec d → PDE.Vec d → ℝ) (x v : PDE.Vec d) :
    homogeneousAnsatz alpha phi (r ^ 3 • x) (r • v) =
      Real.rpow r alpha * homogeneousAnsatz alpha phi x v := by
  unfold homogeneousAnsatz
  rw [normalizedVelocity_dilate r hr, positionDirection_dilate r hr,
    PDE.vecEuclideanNorm_smul, abs_of_pos (pow_pos hr 3)]
  simp only [Real.rpow_eq_pow]
  rw [Real.mul_rpow (pow_nonneg hr.le 3) (PDE.vecEuclideanNorm_nonneg x),
    ← Real.rpow_natCast_mul hr.le]
  have h : (3 : ℝ) * (alpha / 3) = alpha := by ring
  norm_num only [Nat.cast_ofNat]
  rw [h, mul_assoc]

/-- The seed transport is the explicit source expression with its sphere derivative. -/
theorem ansatzTransport_seed {d : ℕ} (alpha C₀ sigma : ℝ) (hsigma : 0 < sigma)
    (y e : PDE.Vec d) :
    ansatzTransport alpha (seed alpha C₀ sigma) y e =
      PDE.vecDot y e * (alpha / 3 * seed alpha C₀ sigma y e -
        (1 / 3 : ℝ) * (alpha * Real.rpow (seedBase sigma y e) (alpha / 2 - 1) *
          PDE.vecDot (y - e) y)) -
      alpha * Real.rpow (seedBase sigma y e) (alpha / 2 - 1) *
        PDE.vecDot (y - e) (y - PDE.vecDot y e • e) := by
  unfold ansatzTransport
  rw [fderiv_seed_apply alpha C₀ sigma hsigma,
    fderiv_seed_sphere_apply alpha C₀ sigma hsigma]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
