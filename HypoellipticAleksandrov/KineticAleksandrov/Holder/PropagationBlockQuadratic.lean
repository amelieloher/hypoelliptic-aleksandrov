module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.CovarianceBoundsOne
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.CovariancePhysical
import Mathlib.Tactic

/-! # Scalar covariance order lifted to the native position and velocity dot products -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Matrix
open scoped BigOperators MatrixOrder

/-- Evaluation of a symmetric scalar block matrix on native Euclidean position and velocity. -/
def blockQuadratic {d : ℕ} (M : Matrix (Fin 2) (Fin 2) ℝ) (y V : PDE.Vec d) : ℝ :=
  M 0 0 * PDE.vecDot y y + 2 * M 0 1 * PDE.vecDot y V + M 1 1 * PDE.vecDot V V

/-- Block evaluation is the sum of its literal two-dimensional coordinate evaluations. -/
theorem blockQuadratic_eq_sum {d : ℕ} (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hM : M.IsSymm) (y V : PDE.Vec d) :
    blockQuadratic M y V = ∑ i, dotProduct ![y i, V i] (M.mulVec ![y i, V i]) := by
  have h10 : M 1 0 = M 0 1 := hM.apply 0 1
  unfold blockQuadratic PDE.vecDot
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, h10]
  ring

/-- Scalar block Loewner order gives the actual native Euclidean quadratic order. -/
theorem blockQuadratic_mono {d : ℕ} {A B : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A.IsSymm) (hB : B.IsSymm) (h : A ≤ B) (y V : PDE.Vec d) :
    blockQuadratic A y V ≤ blockQuadratic B y V := by
  rw [blockQuadratic_eq_sum A hA, blockQuadratic_eq_sum B hB]
  apply Finset.sum_le_sum
  intro i _
  have hp := (Matrix.le_iff.mp h).dotProduct_mulVec_nonneg ![y i, V i]
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub] at hp
  exact sub_nonneg.mp hp

/-- Positive definite block matrices have nonnegative native quadratic evaluations. -/
theorem blockQuadratic_nonneg {d : ℕ} {M : Matrix (Fin 2) (Fin 2) ℝ}
    (hM : M.PosSemidef) (y V : PDE.Vec d) : 0 ≤ blockQuadratic M y V := by
  rw [blockQuadratic_eq_sum M hM.isHermitian.isSymm]
  exact Finset.sum_nonneg fun i _ => by
    simpa only [star_trivial] using hM.dotProduct_mulVec_nonneg ![y i, V i]

/-- Inversion reverses the exact scalar block Loewner order on the definite cone. -/
theorem covariance_inv_antitone {A B : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hAB : A ≤ B) : B⁻¹ ≤ A⁻¹ := by
  let X := B⁻¹ - A⁻¹
  have hX : Xᴴ = X := by
    dsimp only [X]
    rw [Matrix.conjTranspose_sub, hB.inv.isHermitian, hA.inv.isHermitian]
  have hBinv : (B⁻¹)ᴴ = B⁻¹ := hB.inv.isHermitian
  have hp := (hA.posSemidef.conjTranspose_mul_mul_same X).add
    ((Matrix.le_iff.mp hAB).conjTranspose_mul_mul_same B⁻¹)
  rw [hX, hBinv] at hp
  have ha : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  have hb : IsUnit B.det := isUnit_iff_ne_zero.mpr hB.det_pos.ne'
  have he : X * A * X + B⁻¹ * (B - A) * B⁻¹ = A⁻¹ - B⁻¹ := by
    simp only [X, sub_mul, mul_sub, Matrix.mul_assoc, Matrix.mul_nonsing_inv A ha,
      Matrix.nonsing_inv_mul_cancel_left A _ ha, Matrix.mul_nonsing_inv B hb,
      Matrix.mul_one]
    abel_nf
  exact Matrix.le_iff.mpr (he ▸ hp)

/-- The actual physical covariance quadratic is nonnegative on the source cutoff strip. -/
theorem qform_nonneg {d : ℕ} {lam h sigma : ℝ} (hlam : 0 < lam) (hh : 0 < h)
    (hs : -(h / 128) ≤ sigma) (y V : PDE.Vec d) : 0 ≤ qform lam h sigma y V :=
  blockQuadratic_nonneg (posDef_gramian hlam hh hs).inv.posSemidef y V

/-- Native block evaluation commutes with scalar multiplication. -/
theorem blockQuadratic_smul {d : ℕ} (M : Matrix (Fin 2) (Fin 2) ℝ)
    (c : ℝ) (y V : PDE.Vec d) : blockQuadratic (c • M) y V = c * blockQuadratic M y V := by
  unfold blockQuadratic
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

/-- Evaluation of the identity is the sum of the two native squared Euclidean norms. -/
theorem blockQuadratic_one {d : ℕ} (y V : PDE.Vec d) :
    blockQuadratic (1 : Matrix (Fin 2) (Fin 2) ℝ) y V =
      PDE.vecNormSq y + PDE.vecNormSq V := by
  simp [blockQuadratic, PDE.vecNormSq]

end HypoellipticAleksandrov.KineticAleksandrov.Holder
