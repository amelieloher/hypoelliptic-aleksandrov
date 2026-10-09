module

public import HypoellipticAleksandrov.Parabolic.MovingLensCalculus
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-!
# Uniform sign of the moving-lens barrier

This module proves the principal-part, coefficient-uniform strict sign of the
source moving-lens barrier.  It uses only the two pointwise Loewner bounds at
the evaluated point.  In particular it assumes no coefficient regularity or
derivative.

The project convention is `P_A = ∂t - A : Dv²`; hence the conclusion is the
strict inequality `P_A psi < 0`.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

open Matrix
open scoped BigOperators MatrixOrder

/-- The fixed source lens slope used for the principal-part sign argument. -/
def movingLensSignXi (kappa : ℝ) : ℝ :=
  kappa ^ 3 / 2

/-- A uniform upper bound for the signed lower-order bracket in the barrier
identity. -/
def movingLensSignB (d : ℕ) (lam Lam kappa : ℝ) : ℝ :=
  let _ := lam
  movingLensSignXi kappa + 1 + (d : ℝ) * kappa ^ (-4 : ℤ) +
    2 * (d : ℝ) * |Lam|

/-- The two-region radius threshold for the moving-lens sign argument. -/
def movingLensSignR0 (d : ℕ) (lam Lam kappa : ℝ) : ℝ :=
  (movingLensSignB d lam Lam kappa + 2 * lam) /
    (movingLensSignB d lam Lam kappa + 4 * lam)

/-- The natural exponent selected uniformly before every coefficient and lens
datum. -/
def movingLensSignExponent (d : ℕ) (lam Lam kappa : ℝ) : ℕ :=
  1 + ⌈2 * movingLensSignB d lam Lam kappa /
    (movingLensSignXi kappa * (1 - movingLensSignR0 d lam Lam kappa) ^ 2)⌉₊

private theorem movingLensSignXi_pos {kappa : ℝ} (hkappa : 0 < kappa) :
    0 < movingLensSignXi kappa := by
  unfold movingLensSignXi
  positivity

private theorem movingLensSignB_pos (d : ℕ) {lam Lam kappa : ℝ}
    (hkappa : 0 < kappa) :
    0 < movingLensSignB d lam Lam kappa := by
  unfold movingLensSignB
  have hxi := movingLensSignXi_pos hkappa
  have hpow : 0 ≤ kappa ^ (-4 : ℤ) := by positivity
  positivity

private theorem movingLensSignR0_mem_Ioo (d : ℕ) {lam Lam kappa : ℝ}
    (hlam : 0 < lam) (hkappa : 0 < kappa) :
    movingLensSignR0 d lam Lam kappa ∈ Set.Ioo (0 : ℝ) 1 := by
  unfold movingLensSignR0
  have hB := movingLensSignB_pos d (lam := lam) (Lam := Lam) hkappa
  have hden : 0 < movingLensSignB d lam Lam kappa + 4 * lam := by linarith
  constructor
  · exact div_pos (by linarith) hden
  · rw [div_lt_iff₀ hden]
    linarith

private theorem movingLensSignExponent_pos (d : ℕ) (lam Lam kappa : ℝ) :
    0 < movingLensSignExponent d lam Lam kappa := by
  unfold movingLensSignExponent
  omega

private theorem vecDot_mulVec_lower_of_loewner {d : ℕ} {lam : ℝ}
    {M : PDE.Mat d} (hlower : lam • (1 : PDE.Mat d) ≤ M)
    (v : PDE.Vec d) :
    lam * PDE.vecNormSq v ≤ PDE.vecDot v (M *ᵥ v) := by
  have hgap : (M - lam • (1 : PDE.Mat d)).PosSemidef := Matrix.le_iff.mp hlower
  have hquad := hgap.dotProduct_mulVec_nonneg v
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul] at hquad
  simpa only [PDE.vecNormSq, PDE.vecDot, dotProduct, mul_comm] using sub_nonneg.mp hquad

private theorem trace_le_natCast_mul_of_loewner_upper {d : ℕ} {Lam : ℝ}
    {M : PDE.Mat d} (hupper : M ≤ Lam • (1 : PDE.Mat d)) :
    M.trace ≤ (d : ℝ) * Lam := by
  have hgap : (Lam • (1 : PDE.Mat d) - M).PosSemidef := Matrix.le_iff.mp hupper
  have htrace := hgap.trace_nonneg
  simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, smul_eq_mul] at htrace
  linarith

private theorem two_vecDot_le_vecNormSq_add {d : ℕ} (v w : PDE.Vec d) :
    2 * PDE.vecDot v w ≤ PDE.vecNormSq v + PDE.vecNormSq w := by
  have hcs : PDE.vecDot v w ^ 2 ≤ PDE.vecNormSq v * PDE.vecNormSq w :=
    PDE.sq_vecDot_le_vecNormSq_mul_vecNormSq v w
  have hv : 0 ≤ PDE.vecNormSq v := PDE.vecNormSq_nonneg v
  have hw : 0 ≤ PDE.vecNormSq w := PDE.vecNormSq_nonneg w
  nlinarith [sq_nonneg (PDE.vecNormSq v - PDE.vecNormSq w)]

private theorem movingLensRadiusSq_nonneg_of_den_pos {d : ℕ} {xi eps : ℝ}
    {y : PDE.Vec d} {z : TimeVelocity d}
    (hden : 0 < movingLensDenominator xi eps z.1) :
    0 ≤ movingLensRadiusSq xi eps y z := by
  unfold movingLensRadiusSq
  exact div_nonneg (PDE.vecNormSq_nonneg _) hden.le

private theorem vecNormSq_displacement_lt_one_of_normalized_data {d : ℕ}
    {xi eps kappa : ℝ} {y : PDE.Vec d} {z : TimeVelocity d}
    (hden : 0 < movingLensDenominator xi eps z.1)
    (hden_lt : movingLensDenominator xi eps z.1 < kappa ^ 2)
    (hkappa : 0 < kappa) (hkappa_one : kappa ≤ 1)
    (hr : movingLensRadiusSq xi eps y z < 1) :
    PDE.vecNormSq (movingLensDisplacement y z) < 1 := by
  have hradius := (movingLensRadiusSq_lt_one_iff hden).mp hr
  have hkappa_sq : kappa ^ 2 ≤ 1 := by nlinarith
  exact hradius.trans (hden_lt.trans_le hkappa_sq)

private theorem movingLensSign_bracket_le (d : ℕ) {lam Lam kappa eps : ℝ}
    {y : PDE.Vec d} {z : TimeVelocity d}
    (hkappa : 0 < kappa) (hkappa_one : kappa ≤ 1)
    (hden : 0 < movingLensDenominator (movingLensSignXi kappa) eps z.1)
    (hden_lt : movingLensDenominator (movingLensSignXi kappa) eps z.1 < kappa ^ 2)
    (hy : PDE.vecNormSq y ≤ (d : ℝ) * kappa ^ (-4 : ℤ))
    (hr_lt : movingLensRadiusSq (movingLensSignXi kappa) eps y z < 1)
    {M : PDE.Mat d} (hupper : M ≤ Lam • (1 : PDE.Mat d)) :
    movingLensSignXi kappa * movingLensRadiusSq (movingLensSignXi kappa) eps y z +
        2 * PDE.vecDot (movingLensDisplacement y z) y + 2 * M.trace ≤
      movingLensSignB d lam Lam kappa := by
  have hdisp := vecNormSq_displacement_lt_one_of_normalized_data hden hden_lt
    hkappa hkappa_one hr_lt
  have hdot := two_vecDot_le_vecNormSq_add (movingLensDisplacement y z) y
  have htrace := trace_le_natCast_mul_of_loewner_upper hupper
  have habs : Lam ≤ |Lam| := le_abs_self Lam
  have hxi : 0 ≤ movingLensSignXi kappa := (movingLensSignXi_pos hkappa).le
  unfold movingLensSignB
  nlinarith

private theorem movingLensSign_lower_bound {d : ℕ} {lam kappa eps : ℝ}
    {y : PDE.Vec d} {z : TimeVelocity d} {M : PDE.Mat d}
    (hden : 0 < movingLensDenominator (movingLensSignXi kappa) eps z.1)
    (hlower : lam • (1 : PDE.Mat d) ≤ M) :
    8 * (PDE.vecDot (movingLensDisplacement y z)
      (M *ᵥ movingLensDisplacement y z) /
      movingLensDenominator (movingLensSignXi kappa) eps z.1) ≥
      8 * lam * movingLensRadiusSq (movingLensSignXi kappa) eps y z := by
  have hquad := vecDot_mulVec_lower_of_loewner hlower (movingLensDisplacement y z)
  unfold movingLensRadiusSq
  have hdiv := (div_le_div_iff_of_pos_right hden).mpr hquad
  calc
    8 * (PDE.vecDot (movingLensDisplacement y z)
        (M *ᵥ movingLensDisplacement y z) /
        movingLensDenominator (movingLensSignXi kappa) eps z.1) ≥
        8 * (lam * PDE.vecNormSq (movingLensDisplacement y z) /
          movingLensDenominator (movingLensSignXi kappa) eps z.1) := by
      exact mul_le_mul_of_nonneg_left hdiv (by norm_num)
    _ = 8 * lam * (PDE.vecNormSq (movingLensDisplacement y z) /
          movingLensDenominator (movingLensSignXi kappa) eps z.1) := by ring

private theorem movingLensSign_two_region_positive (d : ℕ) {lam Lam kappa : ℝ}
    (hlam : 0 < lam) (hkappa : 0 < kappa)
    {r : ℝ} (hr_nonneg : 0 ≤ r) (hr_lt : r < 1) :
    0 < (movingLensSignExponent d lam Lam kappa : ℝ) * movingLensSignXi kappa *
        (1 - r) ^ 2 + 8 * lam * r -
      2 * movingLensSignB d lam Lam kappa * (1 - r) := by
  have hB := movingLensSignB_pos d (lam := lam) (Lam := Lam) hkappa
  have hxi := movingLensSignXi_pos hkappa
  have hr0 := movingLensSignR0_mem_Ioo d (Lam := Lam) hlam hkappa
  let B := movingLensSignB d lam Lam kappa
  let xi := movingLensSignXi kappa
  let r0 := movingLensSignR0 d lam Lam kappa
  let n := movingLensSignExponent d lam Lam kappa
  have hden : 0 < B + 4 * lam := by dsimp [B]; linarith
  have hlinearR0 : 0 < 8 * lam * r0 - 2 * B * (1 - r0) := by
    have heq : 8 * lam * r0 - 2 * B * (1 - r0) = 4 * lam := by
      dsimp only [r0]
      unfold movingLensSignR0
      field_simp [hden.ne']
      ring
    rw [heq]
    linarith
  by_cases hhigh : r0 < r
  · have hlinear : 0 < 8 * lam * r - 2 * B * (1 - r) := by
      nlinarith [hlinearR0]
    have hpow : 0 ≤ (n : ℝ) * xi * (1 - r) ^ 2 := by positivity
    linarith
  · have hlow : r ≤ r0 := le_of_not_gt hhigh
    have hgap : 0 < 1 - r0 := by linarith [hr0.2]
    have hx : 0 < xi * (1 - r0) ^ 2 := by positivity
    have hceil : 2 * B / (xi * (1 - r0) ^ 2) ≤ (⌈2 * B /
        (xi * (1 - r0) ^ 2)⌉₊ : ℝ) := Nat.le_ceil _
    have hceilMul : 2 * B ≤
        (⌈2 * B / (xi * (1 - r0) ^ 2)⌉₊ : ℝ) *
          (xi * (1 - r0) ^ 2) := by
      have hmul := mul_le_mul_of_nonneg_right hceil hx.le
      rw [div_mul_cancel₀ _ hx.ne'] at hmul
      exact hmul
    have hn : 2 * B < (n : ℝ) * xi * (1 - r0) ^ 2 := by
      simp only [n, movingLensSignExponent, Nat.cast_add, Nat.cast_one]
      nlinarith
    have hmono : (1 - r0) ^ 2 ≤ (1 - r) ^ 2 := by nlinarith
    have hfirst : 2 * B < (n : ℝ) * xi * (1 - r) ^ 2 := by
      exact lt_of_lt_of_le hn (mul_le_mul_of_nonneg_left hmono
        (mul_nonneg (Nat.cast_nonneg n) hxi.le))
    have hlast : 2 * B * (1 - r) ≤ 2 * B := by
      nlinarith
    nlinarith

/-- Under only pointwise two-sided Loewner ellipticity, the fixed source
moving-lens barrier is a strict project-sign subsolution on the normalized
small-denominator lens core. -/
theorem parabolicOperator_movingLensBarrier_lt_zero_of_pointwise_loewner
    (d : ℕ) (lam Lam kappa : ℝ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hkappa : 0 < kappa) (hkappa_one : kappa ≤ 1)
    (A : CoefficientField d) (y : PDE.Vec d) (z : TimeVelocity d) (eps : ℝ)
    (hden_pos : 0 < movingLensDenominator (movingLensSignXi kappa) eps z.1)
    (hden_lt : movingLensDenominator (movingLensSignXi kappa) eps z.1 < kappa ^ 2)
    (hy : PDE.vecNormSq y ≤ (d : ℝ) * kappa ^ (-4 : ℤ))
    (hr_lt : movingLensRadiusSq (movingLensSignXi kappa) eps y z < 1)
    (hlower : lam • (1 : PDE.Mat d) ≤ coefficientAt A z)
    (hupper : coefficientAt A z ≤ Lam • (1 : PDE.Mat d)) :
    parabolicOperator A
      (movingLensBarrier (movingLensSignXi kappa) eps
        (movingLensSignExponent d lam Lam kappa) y) z < 0 := by
  let xi := movingLensSignXi kappa
  let n := movingLensSignExponent d lam Lam kappa
  let r := movingLensRadiusSq xi eps y z
  let q := movingLensDenominator xi eps z.1
  let h := movingLensDisplacement y z
  let M := coefficientAt A z
  have hr_nonneg : 0 ≤ r := by
    dsimp [r, xi, q]
    exact movingLensRadiusSq_nonneg_of_den_pos hden_pos
  have hbracket : xi * r + 2 * PDE.vecDot h y + 2 * M.trace ≤
      movingLensSignB d lam Lam kappa := by
    dsimp [xi, r, q, h, M]
    exact movingLensSign_bracket_le d hkappa hkappa_one hden_pos hden_lt hy hr_lt hupper
  have hquad := movingLensSign_lower_bound (y := y) hden_pos hlower
  have hscalar := movingLensSign_two_region_positive d (Lam := Lam) hlam hkappa
    hr_nonneg hr_lt
  have hqpow : 0 < q ^ (n + 1) := pow_pos hden_pos _
  have _ := hlamLam
  have hidentity := movingLensBarrier_neg_parabolicOperator_identity
    (A := A) (xi := xi) (eps := eps) (n := n) (y := y) (z := z) hden_pos.ne'
  have hfactor : 0 ≤ 2 * (1 - r) := by linarith
  have hbracketTerm : 2 * (r - 1) * (xi * r + 2 * PDE.vecDot h y + 2 * M.trace) ≥
      -2 * movingLensSignB d lam Lam kappa * (1 - r) := by
    have hmul := mul_le_mul_of_nonneg_left hbracket hfactor
    nlinarith
  have hscaled : 0 < q ^ (n + 1) *
      (-parabolicOperator A (movingLensBarrier xi eps n y) z) := by
    rw [hidentity]
    dsimp [xi, n, r, q, h, M] at hquad hscalar hbracket hbracketTerm ⊢
    nlinarith
  have hnegative : 0 < -parabolicOperator A (movingLensBarrier xi eps n y) z :=
    pos_of_mul_pos_right hscaled hqpow.le
  exact neg_pos.mp (by simpa only [xi, n] using hnegative)

end

end HypoellipticAleksandrov.Parabolic
