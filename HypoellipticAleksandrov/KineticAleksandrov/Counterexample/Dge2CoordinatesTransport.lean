module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2CoordinatesDifferential
import Mathlib.Tactic.LinearCombination

/-! # Exact transport contraction of the homogeneous ansatz -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- The full joint derivative splits into the two literal slice derivatives. -/
theorem fderiv_uncurry_split {d : ℕ} (phi : PDE.Vec d → PDE.Vec d → ℝ)
    (y e u w : PDE.Vec d) (hphi : DifferentiableAt ℝ (Function.uncurry phi) (y, e)) :
    fderiv ℝ (Function.uncurry phi) (y, e) (u, w) =
      fderiv ℝ (fun z => phi z e) y u + fderiv ℝ (fun z => phi y z) e w := by
  have hiy : HasFDerivAt (fun z : PDE.Vec d => (z, e))
      ((ContinuousLinearMap.id ℝ (PDE.Vec d)).prod
        (0 : PDE.Vec d →L[ℝ] PDE.Vec d)) y := by
    convert (hasFDerivAt_id (𝕜 := ℝ) y).prodMk
      (hasFDerivAt_const (𝕜 := ℝ) e y) using 1
    funext z
    rfl
  have hie : HasFDerivAt (fun z : PDE.Vec d => (y, z))
      ((0 : PDE.Vec d →L[ℝ] PDE.Vec d).prod
        (ContinuousLinearMap.id ℝ (PDE.Vec d))) e := by
    convert (hasFDerivAt_const (𝕜 := ℝ) y e).prodMk
      (hasFDerivAt_id (𝕜 := ℝ) e) using 1
    funext z
    rfl
  have hy := hphi.hasFDerivAt.comp y hiy
  have he := hphi.hasFDerivAt.comp e hie
  have hy' : HasFDerivAt (fun z => phi z e)
      ((fderiv ℝ (Function.uncurry phi) (y, e)).comp
        ((ContinuousLinearMap.id ℝ (PDE.Vec d)).prod 0)) y := by
    convert hy using 1
    funext z
    rfl
  have he' : HasFDerivAt (fun z => phi y z)
      ((fderiv ℝ (Function.uncurry phi) (y, e)).comp
        ((0 : PDE.Vec d →L[ℝ] PDE.Vec d).prod (ContinuousLinearMap.id ℝ (PDE.Vec d)))) e := by
    convert he using 1
    funext z
    rfl
  rw [hy'.fderiv, he'.fderiv]
  have hsplit : (u, w) = ((u, 0) : PDE.Vec d × PDE.Vec d) + (0, w) := by simp
  rw [hsplit, map_add]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, zero_apply]

/-- The normalized velocity differential has the exact inverse-radius factor. -/
theorem normalizedVelocityDifferential_apply {d : ℕ} (x v w : PDE.Vec d) (hx : x ≠ 0) :
    normalizedVelocityDifferential x v w =
      (-(1 / 3 : ℝ) * (PDE.vecEuclideanNorm x)⁻¹ *
        PDE.vecDot (positionDirection x) w) • normalizedVelocity x v := by
  have hr : 0 < PDE.vecEuclideanNorm x := PDE.vecEuclideanNorm_pos_iff.mpr hx
  have hp : Real.rpow (PDE.vecEuclideanNorm x) (-(1 / 3 : ℝ) - 1) =
      (PDE.vecEuclideanNorm x)⁻¹ * Real.rpow (PDE.vecEuclideanNorm x) (-(1 / 3 : ℝ)) := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_sub hr, Real.rpow_one]
    ring
  simp only [normalizedVelocityDifferential, ContinuousLinearMap.smulRight_apply,
    smul_apply, smul_eq_mul, positionRadiusDifferential_apply, normalizedVelocity,
    smul_smul, hp]
  congr 1
  ring

/-- The cube-root physical velocity is recovered exactly from the normalized velocity. -/
theorem velocity_eq_cubeRoot_smul {d : ℕ} (x v : PDE.Vec d) (hx : x ≠ 0) :
    v = Real.rpow (PDE.vecEuclideanNorm x) (1 / 3) • normalizedVelocity x v := by
  have hr := PDE.vecEuclideanNorm_pos_iff.mpr hx
  unfold normalizedVelocity
  rw [smul_smul]
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_add hr]
  norm_num

/-- The exact position derivative gives the angular expression before transport contraction. -/
theorem fderiv_homogeneousAnsatz_position {d : ℕ} (alpha : ℝ)
    (phi : PDE.Vec d → PDE.Vec d → ℝ) (x v w : PDE.Vec d) (hx : x ≠ 0)
    (hphi : DifferentiableAt ℝ (Function.uncurry phi)
      (normalizedVelocity x v, positionDirection x)) :
    fderiv ℝ (fun z => homogeneousAnsatz alpha phi z v) x w =
      Real.rpow (PDE.vecEuclideanNorm x) (alpha / 3 - 1) *
        (PDE.vecDot (positionDirection x) w *
          (alpha / 3 * phi (normalizedVelocity x v) (positionDirection x) -
            (1 / 3 : ℝ) * fderiv ℝ (fun z => phi z (positionDirection x))
              (normalizedVelocity x v) (normalizedVelocity x v)) +
          fderiv ℝ (fun z => phi (normalizedVelocity x v) z) (positionDirection x)
            (w - PDE.vecDot (positionDirection x) w • positionDirection x)) := by
  have hr := PDE.vecEuclideanNorm_pos_iff.mpr hx
  have hp : Real.rpow (PDE.vecEuclideanNorm x) (alpha / 3) *
      (PDE.vecEuclideanNorm x)⁻¹ =
      Real.rpow (PDE.vecEuclideanNorm x) (alpha / 3 - 1) := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_sub hr, Real.rpow_one]
    simp only [div_eq_mul_inv]
  rw [(hasFDerivAt_homogeneousAnsatz_position alpha phi x v hx hphi).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, positionRadiusDifferential_apply,
    normalizedVelocityDifferential_apply x v w hx, positionDirectionDifferential_apply]
  rw [fderiv_uncurry_split phi _ _ _ _ hphi, map_smul, map_smul]
  simp only [smul_eq_mul]
  simp only [Real.rpow_eq_pow] at hp ⊢
  linear_combination
    (PDE.vecDot (positionDirection x) w *
      (-(1 / 3 : ℝ) * fderiv ℝ (fun z => phi z (positionDirection x))
        (normalizedVelocity x v) (normalizedVelocity x v)) +
      fderiv ℝ (fun z => phi (normalizedVelocity x v) z) (positionDirection x)
        (w - PDE.vecDot (positionDirection x) w • positionDirection x)) * hp

/-- Transport and the velocity Hessian have the identical kinetic prefactor. -/
theorem homogeneousAnsatz_transport {d : ℕ} (alpha : ℝ)
    (phi : PDE.Vec d → PDE.Vec d → ℝ) (x v : PDE.Vec d) (hx : x ≠ 0)
    (hphi : DifferentiableAt ℝ (Function.uncurry phi)
      (normalizedVelocity x v, positionDirection x)) :
    fderiv ℝ (fun z => homogeneousAnsatz alpha phi z v) x v =
      Real.rpow (PDE.vecEuclideanNorm x) ((alpha - 2) / 3) *
        ansatzTransport alpha phi (normalizedVelocity x v) (positionDirection x) := by
  have hr := PDE.vecEuclideanNorm_pos_iff.mpr hx
  have hv := velocity_eq_cubeRoot_smul x v hx
  have hdot : PDE.vecDot (positionDirection x) v =
      Real.rpow (PDE.vecEuclideanNorm x) (1 / 3) *
        PDE.vecDot (normalizedVelocity x v) (positionDirection x) := by
    conv_lhs => rhs; rw [hv]
    unfold PDE.vecDot
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have htangent : v - PDE.vecDot (positionDirection x) v • positionDirection x =
      Real.rpow (PDE.vecEuclideanNorm x) (1 / 3) •
        (normalizedVelocity x v -
          PDE.vecDot (normalizedVelocity x v) (positionDirection x) • positionDirection x) := by
    rw [hdot, smul_sub, smul_smul, ← hv]
  have hp : Real.rpow (PDE.vecEuclideanNorm x) (alpha / 3 - 1) *
      Real.rpow (PDE.vecEuclideanNorm x) (1 / 3) =
      Real.rpow (PDE.vecEuclideanNorm x) ((alpha - 2) / 3) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hr]
    congr 1
    ring
  rw [fderiv_homogeneousAnsatz_position alpha phi x v v hx hphi, htangent, hdot, map_smul]
  simp only [smul_eq_mul]
  calc
    _ = (Real.rpow (PDE.vecEuclideanNorm x) (alpha / 3 - 1) *
        Real.rpow (PDE.vecEuclideanNorm x) (1 / 3)) *
        ansatzTransport alpha phi (normalizedVelocity x v) (positionDirection x) := by
      unfold ansatzTransport
      ring
    _ = _ := by rw [hp]

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
