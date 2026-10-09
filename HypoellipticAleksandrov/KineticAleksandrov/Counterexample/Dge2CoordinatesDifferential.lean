module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2Coordinates
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp

/-!
# Frechet differentials of the Euclidean ansatz coordinates

The derivatives live on the native finite product, with its existing calculus.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- The Euclidean radius differential on native coordinates. -/
def positionRadiusDifferential {d : ℕ} (x : PDE.Vec d) : PDE.Vec d →L[ℝ] ℝ :=
  (PDE.vecEuclideanNorm x)⁻¹ • seedDotLinear x

/-- The exact derivative of the Euclidean position radius. -/
theorem hasFDerivAt_positionRadius {d : ℕ} (x : PDE.Vec d) (hx : x ≠ 0) :
    HasFDerivAt (PDE.vecEuclideanNorm (d := d)) (positionRadiusDifferential x) x := by
  have hb : HasFDerivAt (PDE.vecNormSq (d := d)) (2 • seedDotLinear x) x := by
    simpa only [seedBase, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add, sub_zero]
      using hasFDerivAt_seedBase 0 x 0
  have hbase : PDE.vecNormSq x ≠ 0 := PDE.vecNormSq_eq_zero_iff.not.mpr hx
  convert hb.sqrt hbase using 1
  · rfl
  · ext w
    simp only [positionRadiusDifferential, PDE.vecEuclideanNorm, smul_apply,
      smul_eq_mul, two_smul, add_apply]
    field_simp
    ring

/-- The radius derivative applied to a native direction is its Euclidean dot product. -/
theorem positionRadiusDifferential_apply {d : ℕ} (x w : PDE.Vec d) :
    positionRadiusDifferential x w = PDE.vecDot (positionDirection x) w := by
  simp only [positionRadiusDifferential, smul_apply, smul_eq_mul, seedDotLinear_apply]
  unfold positionDirection PDE.vecDot
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

/-- The exact linear differential of the normalized position direction. -/
def positionDirectionDifferential {d : ℕ} (x : PDE.Vec d) : PDE.Vec d →L[ℝ] PDE.Vec d :=
  (PDE.vecEuclideanNorm x)⁻¹ • ContinuousLinearMap.id ℝ (PDE.Vec d) +
    ((-((PDE.vecEuclideanNorm x)⁻¹ ^ 2)) • positionRadiusDifferential x).smulRight x

/-- The normalized position direction has the literal inverse-radius differential. -/
theorem hasFDerivAt_positionDirection {d : ℕ} (x : PDE.Vec d) (hx : x ≠ 0) :
    HasFDerivAt (positionDirection (d := d)) (positionDirectionDifferential x) x := by
  have hr := (hasDerivAt_inv (PDE.vecEuclideanNorm_eq_zero_iff.not.mpr hx)).comp_hasFDerivAt
    x (hasFDerivAt_positionRadius x hx)
  convert hr.smul (hasFDerivAt_id x) using 1
  · rfl
  · simp only [positionDirectionDifferential, Function.comp_apply, id_eq, inv_pow]

/-- The normalized direction differential is the projection onto the tangent hyperplane. -/
theorem positionDirectionDifferential_apply {d : ℕ} (x w : PDE.Vec d) :
    positionDirectionDifferential x w =
      (PDE.vecEuclideanNorm x)⁻¹ •
        (w - PDE.vecDot (positionDirection x) w • positionDirection x) := by
  simp only [positionDirectionDifferential, add_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    positionRadiusDifferential_apply, positionDirection, smul_sub, smul_smul]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The exact linear differential of normalized velocity with fixed physical velocity. -/
def normalizedVelocityDifferential {d : ℕ} (x v : PDE.Vec d) :
    PDE.Vec d →L[ℝ] PDE.Vec d :=
  (((-(1 / 3 : ℝ)) * Real.rpow (PDE.vecEuclideanNorm x) (-(1 / 3 : ℝ) - 1)) •
    positionRadiusDifferential x).smulRight v

/-- The normalized velocity has the source's inverse-cube-root differential. -/
theorem hasFDerivAt_normalizedVelocity {d : ℕ} (x v : PDE.Vec d) (hx : x ≠ 0) :
    HasFDerivAt (fun z => normalizedVelocity z v) (normalizedVelocityDifferential x v) x := by
  exact ((hasFDerivAt_positionRadius x hx).rpow_const
    (p := -(1 / 3 : ℝ)) (Or.inl (PDE.vecEuclideanNorm_eq_zero_iff.not.mpr hx))).smul_const v

/-- The homogeneous ansatz has its full exact position differential before transport contraction. -/
theorem hasFDerivAt_homogeneousAnsatz_position {d : ℕ} (alpha : ℝ)
    (phi : PDE.Vec d → PDE.Vec d → ℝ) (x v : PDE.Vec d) (hx : x ≠ 0)
    (hphi : DifferentiableAt ℝ (Function.uncurry phi)
      (normalizedVelocity x v, positionDirection x)) :
    HasFDerivAt (fun z => homogeneousAnsatz alpha phi z v)
      ((phi (normalizedVelocity x v) (positionDirection x)) •
          ((alpha / 3 * Real.rpow (PDE.vecEuclideanNorm x) (alpha / 3 - 1)) •
            positionRadiusDifferential x) +
        (Real.rpow (PDE.vecEuclideanNorm x) (alpha / 3)) •
          (fderiv ℝ (Function.uncurry phi) (normalizedVelocity x v, positionDirection x)).comp
            ((normalizedVelocityDifferential x v).prod (positionDirectionDifferential x))) x := by
  have hr := (hasFDerivAt_positionRadius x hx).rpow_const
    (p := alpha / 3) (Or.inl (PDE.vecEuclideanNorm_eq_zero_iff.not.mpr hx))
  have hcoord := (hasFDerivAt_normalizedVelocity x v hx).prodMk
    (hasFDerivAt_positionDirection x hx)
  convert hr.mul (hphi.hasFDerivAt.comp x hcoord) using 1
  · rfl
  · ext w
    simp only [add_apply, smul_apply, smul_eq_mul, Real.rpow_eq_pow,
      Function.comp_apply, Function.uncurry_apply_pair]
    ring

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
