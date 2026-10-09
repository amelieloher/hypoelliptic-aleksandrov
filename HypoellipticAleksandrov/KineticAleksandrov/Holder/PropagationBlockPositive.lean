module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationBlockQuadraticBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationParametersBounds
import Mathlib.Tactic

/-! # Exact source positivity-set bounds for the Gaussian block barrier -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

/-- The source damping coefficient is nonnegative under positive ellipticity. -/
theorem Xi_nonneg (d : ℕ) {lam Lam H h : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hh : 0 < h) : 0 ≤ Xi d lam Lam H h := by
  have hLam0 : 0 ≤ Lam := (hlam.trans_le hLam).le
  unfold Xi
  positivity

/-- Positivity of the whole-carrier barrier forces the definite strip and the source q bound. -/
theorem gaussianBarrier_pos_quadratic {d : ℕ} {lam h : ℝ} (hlam : 0 < lam) (hh : 0 < h)
    (Lam H L ell tminus sblock : ℝ) (hLam : lam ≤ Lam) (hell : 0 ≤ ell)
    (hbudget : Xi d lam Lam H h * h ≤ L ^ 2 / 4)
    (x v : ℝ → PDE.Vec d) (P : KineticPoint d)
    (hpos : 0 < gaussianBarrier lam Lam H h L ell tminus sblock x v P) :
    -(h / 128) < P.time - tminus - sblock ∧
      qform lam h (P.time - tminus - sblock)
        (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus)) <
        (513 / 512 : ℝ) * L ^ 2 := by
  let sigma := P.time - tminus - sblock
  have hs : -(1 / 128 : ℝ) < sigma / h := by
    by_contra hn
    unfold gaussianBarrier at hpos
    rw [ite_eq_right hn] at hpos
    exact lt_irrefl 0 hpos
  have hs' : -(h / 128) < sigma := by
    have he := (lt_div_iff₀ hh).mp hs
    linarith only [he]
  have hXi : 0 ≤ Xi d lam Lam H h := Xi_nonneg d hlam hLam hh
  have hchi := barrierCutoff_bounds (sigma / h)
  rw [gaussianBarrier_eq_formula] at hpos
  dsimp only [gaussianFormula] at hpos
  have hG := pos_of_mul_pos_right hpos (mul_nonneg hell hchi.1)
  have hexp := Real.exp_lt_exp.mp (sub_pos.mp hG)
  have hm := mul_le_mul_of_nonneg_left hs'.le hXi
  constructor
  · exact hs'
  · change qform lam h sigma (P.position - x (P.time - tminus))
      (P.velocity - v (P.time - tminus)) < (513 / 512 : ℝ) * L ^ 2
    linarith only [hexp, hm, hbudget]

/-- The covariance upper bound turns the source q bound into both scaled Euclidean bounds. -/
theorem qform_scaled_norm_bounds {d : ℕ} {lam h sigma L : ℝ}
    (hlam : 0 < lam) (hh : 0 < h) (hL : 0 ≤ L) (hs : -(h / 128) ≤ sigma)
    (ht : |sigma / h| ≤ 1) (y V : PDE.Vec d)
    (hq : qform lam h sigma y V ≤ (513 / 512 : ℝ) * L ^ 2) :
    PDE.vecEuclideanNorm ((h ^ (3 / 2 : ℝ))⁻¹ • y) ≤ (3 / 2 : ℝ) * L * Real.sqrt lam ∧
      PDE.vecEuclideanNorm ((h ^ (1 / 2 : ℝ))⁻¹ • V) ≤ (3 / 2 : ℝ) * L * Real.sqrt lam := by
  let Y := (h ^ (3 / 2 : ℝ))⁻¹ • y
  let U := (h ^ (1 / 2 : ℝ))⁻¹ • V
  let C := (3 / 2 : ℝ) * L * Real.sqrt lam
  have hC : 0 ≤ C := by positivity
  have hb := qform_scaled_normSq_le hlam hh hs ht y V
  have hq' := mul_le_mul_of_nonneg_left hq (show 0 ≤ 2 * lam by positivity)
  have hupper : PDE.vecNormSq Y + PDE.vecNormSq U ≤ C ^ 2 := by
    apply hb.trans (hq'.trans ?_)
    dsimp only [C]
    rw [mul_pow, mul_pow, Real.sq_sqrt hlam.le]
    nlinarith only [mul_nonneg hlam.le (sq_nonneg L)]
  constructor
  · apply (sq_le_sq₀ (PDE.vecEuclideanNorm_nonneg Y) hC).mp
    rw [PDE.vecEuclideanNorm_sq]
    linarith only [hupper, PDE.vecNormSq_nonneg U]
  · apply (sq_le_sq₀ (PDE.vecEuclideanNorm_nonneg U) hC).mp
    rw [PDE.vecEuclideanNorm_sq]
    linarith only [hupper, PDE.vecNormSq_nonneg Y]

/-- Undoing a positive scalar scaling preserves the native Euclidean radius bound exactly. -/
theorem vecEuclideanNorm_le_of_scaled {d : ℕ} {a C : ℝ} (ha : 0 < a)
    (y : PDE.Vec d) (h : PDE.vecEuclideanNorm (a⁻¹ • y) ≤ C) :
    PDE.vecEuclideanNorm y ≤ C * a := by
  rw [PDE.vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr ha)] at h
  have hm := mul_le_mul_of_nonneg_left h ha.le
  simpa only [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul, mul_comm a C] using hm

/-- Both native Euclidean coordinates obey the exact source positivity-set radii. -/
theorem gaussianBarrier_positive_set {d : ℕ} {lam h : ℝ} (hlam : 0 < lam) (hh : 0 < h)
    (Lam H L ell tminus sblock : ℝ) (hLam : lam ≤ Lam) (hell : 0 ≤ ell) (hL : 0 ≤ L)
    (hbudget : Xi d lam Lam H h * h ≤ L ^ 2 / 4)
    (x v : ℝ → PDE.Vec d) (P : KineticPoint d)
    (hs1 : P.time - tminus - sblock ≤ h)
    (hpos : 0 < gaussianBarrier lam Lam H h L ell tminus sblock x v P) :
    PDE.vecEuclideanNorm (P.position - x (P.time - tminus)) ≤
      (3 / 2 : ℝ) * L * Real.sqrt lam * h ^ (3 / 2 : ℝ) ∧
    PDE.vecEuclideanNorm (P.velocity - v (P.time - tminus)) ≤
      (3 / 2 : ℝ) * L * Real.sqrt lam * Real.sqrt h := by
  obtain ⟨hs0, hq⟩ := gaussianBarrier_pos_quadratic hlam hh Lam H L ell tminus sblock
    hLam hell hbudget x v P hpos
  have ht0 : -(1 / 128 : ℝ) < (P.time - tminus - sblock) / h := by
    apply (lt_div_iff₀ hh).mpr
    linarith only [hs0]
  have ht1 : (P.time - tminus - sblock) / h ≤ 1 := (div_le_one hh).mpr hs1
  have ht : |(P.time - tminus - sblock) / h| ≤ 1 :=
    abs_le.mpr ⟨by linarith only [ht0], ht1⟩
  obtain ⟨hy, hV⟩ := qform_scaled_norm_bounds hlam hh hL hs0.le ht _ _ hq.le
  constructor
  · exact vecEuclideanNorm_le_of_scaled (Real.rpow_pos_of_pos hh _)
      (P.position - x (P.time - tminus)) hy
  · have he := vecEuclideanNorm_le_of_scaled (Real.rpow_pos_of_pos hh _)
      (P.velocity - v (P.time - tminus)) hV
    rwa [← Real.sqrt_eq_rpow] at he

end HypoellipticAleksandrov.KineticAleksandrov.Holder
