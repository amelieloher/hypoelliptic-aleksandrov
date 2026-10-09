module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.RetentionPolynomial
public import HypoellipticAleksandrov.Ambient.MatrixContraction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Elliptic contraction bounds for the retention barrier

The standing positive ellipticity hypotheses are retained explicitly.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Matrix
open scoped MatrixOrder BigOperators

private theorem trace_upper {d : ℕ} {Lam : ℝ} {A : PDE.Mat d}
    (hhi : A ≤ Lam • (1 : PDE.Mat d)) : A.trace ≤ (d : ℝ) * Lam := by
  have hgap : (Lam • (1 : PDE.Mat d) - A).PosSemidef := Matrix.le_iff.mp hhi
  have htrace := hgap.trace_nonneg
  simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, smul_eq_mul] at htrace
  linarith

private theorem contraction_one {d : ℕ} (A : PDE.Mat d) :
    matrixContraction A 1 = A.trace := by
  classical
  simp [matrixContraction, Matrix.trace, Matrix.diag, Matrix.one_apply]

private theorem contraction_outer {d : ℕ} (A : PDE.Mat d) (Y : PDE.Vec d) :
    matrixContraction A (Matrix.of (fun i j => Y i * Y j)) = PDE.vecDot Y (A *ᵥ Y) := by
  classical
  unfold matrixContraction PDE.vecDot Matrix.mulVec dotProduct
  simp only [Matrix.of_apply]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The source second-order bound under its standing positive ellipticity assumptions. -/
theorem retention_barrier_second_order {d N : ℕ} (hN : 3 ≤ N)
    (lam Lam s : ℝ) (hs : 0 < s) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (A : PDE.Mat d) (hA : A.IsSymm) (hlo : lam • (1 : PDE.Mat d) ≤ A)
    (hhi : A ≤ Lam • (1 : PDE.Mat d))
    (Y : PDE.Vec d) (hY : Y ∈ PDE.euclideanBall 0 s) :
    -(2 * N * d * Lam / s ^ 2) * barrier N s Y +
      (barrierC d N lam Lam / s ^ 4) *
        (1 - PDE.vecNormSq Y / s ^ 2) ^ (N - 2) * PDE.vecNormSq Y ≤
      matrixContraction A (Hess (barrier N s) Y) := by
  have _hA := hA
  have hLam : 0 ≤ Lam := (hlam.trans_le hlamLam).le
  have hs2 : 0 < s ^ 2 := sq_pos_of_pos hs
  have hR : 0 ≤ PDE.vecNormSq Y := PDE.vecNormSq_nonneg Y
  have hY' : PDE.vecNormSq Y < s ^ 2 := by
    simpa only [PDE.euclideanBall, PDE.euclideanSqDist, Set.mem_ofPred_eq, sub_zero] using hY
  set w := 1 - PDE.vecNormSq Y / s ^ 2 with hw
  have hw0 : 0 ≤ w := by
    have := (div_lt_one hs2).mpr hY'
    dsimp [w]; linarith
  have hw1 : w ≤ 1 := by
    have := div_nonneg hR hs2.le
    dsimp [w]; linarith
  have htrace := trace_upper hhi
  have hquad := vecDot_mulVec_lower_of_loewner hlo Y
  have hgradH := (retention_polynomial_barrier hN s hs).2.2.2.1 Y hY
  rw [hgradH.2, matrixContraction_add_right, matrixContraction_smul_right,
    matrixContraction_smul_right, contraction_one, contraction_outer]
  change _ ≤ (-2 * N / s ^ 2 * w ^ (N - 1)) * A.trace +
    (4 * N * (N - 1 : ℕ) / s ^ 4 * w ^ (N - 2)) * PDE.vecDot Y (A *ᵥ Y)
  have hneg : -2 * (N : ℝ) / s ^ 2 * w ^ (N - 1) ≤ 0 := by
    have hnonneg : 0 ≤ 2 * (N : ℝ) / s ^ 2 * w ^ (N - 1) := by positivity
    convert neg_nonpos.mpr hnonneg using 1; ring
  have hpos : 0 ≤ 4 * (N : ℝ) * (N - 1 : ℕ) / s ^ 4 * w ^ (N - 2) := by
    positivity
  have ht := mul_le_mul_of_nonpos_left htrace hneg
  have hq := mul_le_mul_of_nonneg_left hquad hpos
  apply le_trans _ (add_le_add ht hq)
  have hpow1 : w ^ (N - 1) = w ^ (N - 2) * w := by
    rw [show N - 1 = (N - 2) + 1 by omega, pow_succ]
  have hpow2 : w ^ N = w ^ (N - 2) * w ^ 2 := by
    calc
      w ^ N = w ^ ((N - 2) + 2) := congrArg (fun k => w ^ k) (by omega)
      _ = w ^ (N - 2) * w ^ 2 := pow_add _ _ _
  have hrem : 0 ≤ (2 * (N : ℝ) * d * Lam / s ^ 4) *
      w ^ (N - 2) * PDE.vecNormSq Y * (1 - w) := by
    positivity
  have hid : PDE.vecNormSq Y = s ^ 2 * (1 - w) := by
    dsimp [w]
    field_simp [hs.ne']
    ring
  calc
    _ = (-2 * N / s ^ 2 * w ^ (N - 1)) * ((d : ℝ) * Lam) +
        (4 * N * (N - 1 : ℕ) / s ^ 4 * w ^ (N - 2)) * (lam * PDE.vecNormSq Y) -
        (2 * (N : ℝ) * d * Lam / s ^ 4) * w ^ (N - 2) *
          PDE.vecNormSq Y * (1 - w) := by
      unfold barrier barrierC
      rw [max_eq_left hw0, hpow1, hpow2, hid]
      field_simp [hs.ne']
      ring
    _ ≤ _ := sub_le_self _ hrem


private theorem young_of_square {X U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hX : X ^ 2 ≤ 4 * U * V) : X ≤ U + V := by
  nlinarith [sq_nonneg (U - V)]

private theorem barrier_drift_absorption {d N : ℕ} (hN : 3 ≤ N)
    (lam Lam s H : ℝ) (hs : 0 < s) (hc : 0 < barrierC d N lam Lam)
    (a Y : PDE.Vec d) (ha : PDE.vecEuclideanNorm a ≤ H)
    (hY : Y ∈ PDE.euclideanBall 0 s) :
    PDE.vecDot a (PDE.classicalGradient (barrier N s) Y) ≤
      (barrierC d N lam Lam / s ^ 4) *
        (1 - PDE.vecNormSq Y / s ^ 2) ^ (N - 2) * PDE.vecNormSq Y +
      ((N : ℝ) ^ 2 * H ^ 2 / barrierC d N lam Lam) * barrier N s Y := by
  have hs2 : 0 < s ^ 2 := sq_pos_of_pos hs
  have hR : 0 ≤ PDE.vecNormSq Y := PDE.vecNormSq_nonneg Y
  have hY' : PDE.vecNormSq Y < s ^ 2 := by
    simpa only [PDE.euclideanBall, PDE.euclideanSqDist, Set.mem_ofPred_eq, sub_zero] using hY
  set w := 1 - PDE.vecNormSq Y / s ^ 2 with hw
  have hw0 : 0 ≤ w := by
    have := (div_lt_one hs2).mpr hY'
    dsimp [w]; linarith
  have hH : 0 ≤ H := (PDE.vecEuclideanNorm_nonneg a).trans ha
  have hnorm : PDE.vecNormSq a ≤ H ^ 2 := by
    have hn := PDE.vecEuclideanNorm_nonneg a
    have heq := PDE.vecEuclideanNorm_sq a
    nlinarith
  have hCS : PDE.vecDot a Y ^ 2 ≤ H ^ 2 * PDE.vecNormSq Y :=
    (PDE.sq_vecDot_le_vecNormSq_mul_vecNormSq a Y).trans
      (mul_le_mul_of_nonneg_right hnorm hR)
  have hgrad := (retention_polynomial_barrier hN s hs).2.2.2.1 Y hY
  have hdot : PDE.vecDot a (PDE.classicalGradient (barrier N s) Y) =
      (-2 * N / s ^ 2 * w ^ (N - 1)) * PDE.vecDot a Y := by
    rw [hgrad.1]
    unfold PDE.vecDot
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hψ : barrier N s Y = w ^ N := by
    unfold barrier
    rw [max_eq_left hw0]
  have hpow : (w ^ (N - 1)) ^ 2 = w ^ (N - 2) * w ^ N := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have hsq := mul_le_mul_of_nonneg_left hCS
    (sq_nonneg (-2 * (N : ℝ) / s ^ 2 * w ^ (N - 1)))
  have hid : (-2 * (N : ℝ) / s ^ 2 * w ^ (N - 1)) ^ 2 *
      (H ^ 2 * PDE.vecNormSq Y) =
      4 * ((barrierC d N lam Lam / s ^ 4) * w ^ (N - 2) * PDE.vecNormSq Y) *
        (((N : ℝ) ^ 2 * H ^ 2 / barrierC d N lam Lam) * w ^ N) := by
    rw [mul_pow, hpow]
    field_simp [hs.ne', hc.ne']
    ring
  rw [hdot, hψ]
  apply young_of_square (by positivity) (by positivity)
  rw [mul_pow, hid.symm]
  exact hsq

/-- Young absorption gives the source global drift inequality. -/
theorem retention_barrier_drift_inequality {d N : ℕ} (hN : 3 ≤ N)
    (lam Lam s H : ℝ) (hs : 0 < s) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hc : 0 < barrierC d N lam Lam) (A : PDE.Mat d) (hA : A.IsSymm)
    (hlo : lam • (1 : PDE.Mat d) ≤ A) (hhi : A ≤ Lam • (1 : PDE.Mat d))
    (a Y : PDE.Vec d) (ha : PDE.vecEuclideanNorm a ≤ H) :
    -barrierRate d N lam Lam s H * barrier N s Y ≤
      matrixContraction A (Hess (barrier N s) Y) -
        PDE.vecDot a (PDE.classicalGradient (barrier N s) Y) := by
  by_cases hY : Y ∈ PDE.euclideanBall 0 s
  · have hsecond := retention_barrier_second_order hN lam Lam s hs hlam hlamLam
      A hA hlo hhi Y hY
    have hyoung := barrier_drift_absorption hN lam Lam s H hs hc a Y ha hY
    unfold barrierRate
    linarith
  · obtain ⟨hψ, hgrad, hHess⟩ := (retention_polynomial_barrier hN s hs).2.2.2.2 Y hY
    rw [hψ, hgrad, hHess]
    simp [matrixContraction, PDE.vecDot]

end HypoellipticAleksandrov.KineticAleksandrov.Decay
