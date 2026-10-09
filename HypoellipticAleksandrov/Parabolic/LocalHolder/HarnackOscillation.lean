module

public import HypoellipticAleksandrov.Statements.ParabolicHarnack
public import HypoellipticAleksandrov.Parabolic.AffineScalarCalculus

/-! # Homogeneous range contraction

Apply the Harnack theorem to both nonnegative affine transforms at the same
 earlier point. The resulting interval bounds conditions the range on the later slab.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Set

/-- A structural constant contracts every homogeneous unit-cylinder range. -/
theorem exists_unit_homogeneous_range_contraction
    (N : ℕ) (hN : 1 ≤ N) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧
      ∀ (A : CoefficientField N) (v : TimeVelocity N → ℝ),
        IsContinuousCoefficientOn A (Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall 0 1) →
        (∀ z ∈ Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall 0 1, (coefficientAt A z).IsSymm) →
        HasLowerEllipticityOn lam A (Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall 0 1) →
        HasUpperEllipticityOn Lam A (Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall 0 1) →
        IsScalarC12On v (Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall 0 1) →
        (∀ z ∈ Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall 0 1,
          scalarTimeDerivative v z =
            matrixContraction (coefficientAt A z) (scalarSpatialHessian v z)) →
        ∀ l b : ℝ, (∀ z ∈ Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall 0 1, l ≤ v z ∧ v z ≤ b) →
        ∃ l' b' : ℝ, b' - l' = (1 - h) * (b - l) ∧
          ∀ z ∈ Ioo (3 / 4 : ℝ) 1 ×ˢ PDE.euclideanBall 0 (1 / 2 : ℝ),
            l' ≤ v z ∧ v z ≤ b' := by
  obtain ⟨h₀, hh₀, harnack⟩ := parabolic_harnack_unit_cylinder N hN lam hlam Lam hLam
  let h := min h₀ 1
  have hh : 0 < h := lt_min hh₀ zero_lt_one
  refine ⟨h, hh, min_le_right _ _, ?_⟩
  intro A v hA hs hlo hhi hv he l b hbound
  let p : TimeVelocity N := (3 / 8, 0)
  have hp : p ∈ Ioo (1 / 4 : ℝ) (1 / 2 : ℝ) ×ˢ
      PDE.euclideanBall 0 (1 / 2 : ℝ) := by
    constructor
    · norm_num [p]
    · simp [p, PDE.euclideanBall]
  have hpU : p ∈ Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall 0 1 := by
    constructor
    · norm_num [p]
    · simp [p, PDE.euclideanBall]
  have haffine (k c : ℝ) : ∀ z ∈ Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall 0 1,
      scalarTimeDerivative (fun q => k * v q + c) z =
        matrixContraction (coefficientAt A z)
          (scalarSpatialHessian (fun q => k * v q + c) z) := by
    intro z hz
    rw [scalarTimeDerivative_const_mul_add_const, scalarSpatialHessian_const_mul_add_const,
      matrixContraction_smul_right, he z hz]
  have hn (z : TimeVelocity N) (hz : z ∈ Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall 0 1) :
      0 ≤ 1 * v z + -l := by linarith only [(hbound z hz).1]
  have hn' (z : TimeVelocity N) (hz : z ∈ Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall 0 1) :
      0 ≤ -1 * v z + b := by linarith only [(hbound z hz).2]
  refine ⟨l + h * (v p - l), b - h * (b - v p), by ring, ?_⟩
  intro z hz
  have hlow := harnack A (fun q => 1 * v q + -l) hA hs hlo hhi
    (hv.const_mul_add_const 1 (-l)) hn (haffine 1 (-l)) p hp z hz
  have hupp := harnack A (fun q => -1 * v q + b) hA hs hlo hhi
    (hv.const_mul_add_const (-1) b) hn' (haffine (-1) b) p hp z hz
  have hlscale : h * (v p - l) ≤ h₀ * (v p - l) :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) (sub_nonneg.mpr (hbound p hpU).1)
  have huscale : h * (b - v p) ≤ h₀ * (b - v p) :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) (sub_nonneg.mpr (hbound p hpU).2)
  constructor <;> linarith only [hlow, hupp, hlscale, huscale]

end HypoellipticAleksandrov.Parabolic.LocalHolder
