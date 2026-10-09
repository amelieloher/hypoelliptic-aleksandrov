module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationBlockQuadraticBounds
import Mathlib.Tactic

/-! # Endpoint allowance and the source half-height quadratic estimate -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

/-- Cancelling a positive spatial scale preserves the Euclidean endpoint allowance. -/
theorem endpoint_scaled_norm_le {d : ℕ} {a C : ℝ} (ha : 0 < a)
    (y : PDE.Vec d) (hy : PDE.vecEuclideanNorm y ≤ C * a) :
    PDE.vecEuclideanNorm (a⁻¹ • y) ≤ C := by
  rw [PDE.vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr ha)]
  have he := mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr ha.le)
  have heq : a⁻¹ * (C * a) = C := by field_simp
  exact he.trans_eq heq

/-- The source one-eighth endpoint allowance gives q_h at most L squared over two. -/
theorem qform_endpoint_half {d : ℕ} {lam h L : ℝ}
    (hlam : 0 < lam) (hh : 0 < h) (hL : 0 ≤ L) (y V : PDE.Vec d)
    (hy : PDE.vecEuclideanNorm y ≤ (L * Real.sqrt lam / 8) * h ^ (3 / 2 : ℝ))
    (hV : PDE.vecEuclideanNorm V ≤ (L * Real.sqrt lam / 8) * Real.sqrt h) :
    qform lam h h y V ≤ L ^ 2 / 2 := by
  let C := L * Real.sqrt lam / 8
  have hC : 0 ≤ C := by positivity
  have hy' := endpoint_scaled_norm_le (Real.rpow_pos_of_pos hh (3 / 2 : ℝ)) y hy
  have hV' := endpoint_scaled_norm_le (Real.sqrt_pos.mpr hh) V hV
  rw [Real.sqrt_eq_rpow] at hV'
  have hysq := (sq_le_sq₀ (PDE.vecEuclideanNorm_nonneg _) hC).mpr hy'
  have hVsq := (sq_le_sq₀ (PDE.vecEuclideanNorm_nonneg _) hC).mpr hV'
  rw [PDE.vecEuclideanNorm_sq] at hysq hVsq
  have he := qform_endpoint_upper hlam hh y V
  have hn : PDE.vecNormSq ((h ^ (3 / 2 : ℝ))⁻¹ • y) +
      PDE.vecNormSq ((h ^ (1 / 2 : ℝ))⁻¹ • V) ≤ 2 * C ^ 2 := by
    linarith only [hysq, hVsq]
  apply he.trans ((mul_le_mul_of_nonneg_left hn (by positivity)).trans ?_)
  dsimp only [C]
  rw [div_pow, mul_pow, Real.sq_sqrt hlam.le]
  have hl : lam ≠ 0 := hlam.ne'
  field_simp
  nlinarith only [sq_nonneg L]

end HypoellipticAleksandrov.KineticAleksandrov.Holder
