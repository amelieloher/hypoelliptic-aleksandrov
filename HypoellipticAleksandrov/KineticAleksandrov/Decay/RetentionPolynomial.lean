module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.SourceNotation
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonRadial
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Polynomial retention barriers

Positive-part powers have vanishing jets at their gluing point.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay

open Set Filter
open scoped Topology

private def positivePower (N : ℕ) (x : ℝ) : ℝ := (max x 0) ^ N

private theorem positivePower_derivative {N : ℕ} (hN : 2 ≤ N) (x : ℝ) :
    HasDerivAt (positivePower N) ((N : ℝ) * positivePower (N - 1) x) x := by
  have hNm : N - 1 ≠ 0 := by omega
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have heq : positivePower N =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [gt_mem_nhds hx] with y hy
      simp [positivePower, max_eq_right hy.le, show N ≠ 0 by omega]
    have hd := (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq heq
    simpa [positivePower, max_eq_right hx.le, hNm] using hd
  · have hp : HasDerivWithinAt (positivePower N) 0 (Ici 0) 0 := by
      have hd := ((hasDerivAt_id (0 : ℝ)).fun_pow N).hasDerivWithinAt (s := Ici 0)
      have hd0 : HasDerivWithinAt (fun x : ℝ => x ^ N) 0 (Ici 0) 0 := by
        simpa only [Pi.pow_apply, id_eq, zero_pow hNm, mul_zero, zero_mul] using hd
      exact hd0.congr (fun y hy => by simp [positivePower, max_eq_left hy])
        (by simp [positivePower])
    have hn : HasDerivWithinAt (positivePower N) 0 (Iic 0) 0 :=
      (hasDerivAt_const (0 : ℝ) (0 : ℝ)).hasDerivWithinAt.congr
        (fun y hy => by simp [positivePower, max_eq_right hy, show N ≠ 0 by omega])
        (by simp [positivePower, show N ≠ 0 by omega])
    have hu := hp.union hn
    rw [Ici_union_Iic] at hu
    simpa [positivePower, hNm] using hasDerivWithinAt_univ.mp hu
  · have heq : positivePower N =ᶠ[𝓝 x] fun y => y ^ N := by
      filter_upwards [lt_mem_nhds hx] with y hy
      simp [positivePower, max_eq_left hy.le]
    simpa [positivePower, max_eq_left hx.le] using
      ((hasDerivAt_id x).pow N).congr_of_eventuallyEq heq

private theorem positivePower_deriv {N : ℕ} (hN : 2 ≤ N) :
    deriv (positivePower N) = fun x => (N : ℝ) * positivePower (N - 1) x := by
  funext x
  exact (positivePower_derivative hN x).deriv

private theorem positivePower_continuous (N : ℕ) : Continuous (positivePower N) := by
  unfold positivePower
  exact (continuous_id.max continuous_const).pow N

private theorem positivePower_contDiff_one {N : ℕ} (hN : 2 ≤ N) :
    ContDiff ℝ 1 (positivePower N) := by
  rw [contDiff_one_iff_deriv, positivePower_deriv hN]
  exact ⟨fun x => (positivePower_derivative hN x).differentiableAt,
    continuous_const.mul (positivePower_continuous _)⟩

private theorem positivePower_contDiff_two {N : ℕ} (hN : 3 ≤ N) :
    ContDiff ℝ 2 (positivePower N) := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun x => (positivePower_derivative (by omega) x).differentiableAt, ?_, ?_⟩
  · norm_num
  · rw [positivePower_deriv (by omega)]
    exact contDiff_const.mul (positivePower_contDiff_one (by omega))


/-- A source-admissible integer gives a strictly positive barrier constant. -/
theorem exists_retention_barrier_order (d : ℕ) (hd : 1 ≤ d)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam) :
    ∃ N : ℕ, 3 ≤ N ∧ 2 * (N - 1 : ℕ) * lam > (d : ℝ) * Lam ∧
      0 < barrierC d N lam Lam := by
  have _hd := hd
  have _hlamLam := hlamLam
  obtain ⟨n, hn⟩ := exists_nat_gt (max 3 ((d : ℝ) * Lam / (2 * lam)))
  have hn3 : (3 : ℝ) < n := (le_max_left _ _).trans_lt hn
  have hnd : (d : ℝ) * Lam / (2 * lam) < n := (le_max_right _ _).trans_lt hn
  have hineq : (d : ℝ) * Lam < (n : ℝ) * (2 * lam) :=
    (div_lt_iff₀ (by positivity)).mp hnd
  refine ⟨n + 1, ?_, ?_, ?_⟩
  · have : 3 < n := by exact_mod_cast hn3
    omega
  · simpa only [Nat.add_sub_cancel] using (by nlinarith :
      2 * (n : ℝ) * lam > (d : ℝ) * Lam)
  · unfold barrierC
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    have hpos : 0 < (n : ℝ) + 1 := by positivity
    nlinarith [mul_pos hpos (show 0 < 2 * (n : ℝ) * lam - (d : ℝ) * Lam by linarith)]

/-- The positive-part polynomial barrier is globally twice continuously differentiable. -/
theorem retention_barrier_contDiff {d N : ℕ} (hN : 3 ≤ N) (s : ℝ) :
    ContDiff ℝ 2 (barrier (d := d) N s) := by
  have hw : ContDiff ℝ 2 (fun Y : PDE.Vec d => 1 - PDE.vecNormSq Y / s ^ 2) :=
    contDiff_const.sub (PDE.contDiff_vecNormSq.of_le (by norm_num) |>.div_const _)
  exact (positivePower_contDiff_two hN).comp hw


private def radialProfile (N : ℕ) (s r : ℝ) : ℝ := positivePower N (1 - r / s ^ 2)

private theorem radialProfile_derivative {N : ℕ} (hN : 2 ≤ N) (s r : ℝ) :
    HasDerivAt (radialProfile N s)
      (-((N : ℝ) / s ^ 2) * positivePower (N - 1) (1 - r / s ^ 2)) r := by
  have hw := ((hasDerivAt_id r).div_const (s ^ 2)).const_sub 1
  have h := (positivePower_derivative hN (1 - r / s ^ 2)).comp r hw
  exact h.congr_deriv (by ring)

private theorem radialProfile_deriv {N : ℕ} (hN : 2 ≤ N) (s : ℝ) :
    deriv (radialProfile N s) =
      fun r => -((N : ℝ) / s ^ 2) * positivePower (N - 1) (1 - r / s ^ 2) := by
  funext r
  exact (radialProfile_derivative hN s r).deriv

private theorem radialProfile_second_deriv {N : ℕ} (hN : 3 ≤ N) (s r : ℝ) :
    deriv (deriv (radialProfile N s)) r =
      ((N : ℝ) / s ^ 2) * ((N - 1 : ℕ) / s ^ 2) *
        positivePower (N - 2) (1 - r / s ^ 2) := by
  rw [radialProfile_deriv (by omega)]
  have h := (radialProfile_derivative (N := N - 1) (by omega) s r).const_mul
    (-((N : ℝ) / s ^ 2))
  have heq : (fun r => -((N : ℝ) / s ^ 2) *
      positivePower (N - 1) (1 - r / s ^ 2)) =
      (fun r => -((N : ℝ) / s ^ 2) * radialProfile (N - 1) s r) := rfl
  rw [heq, h.deriv]
  rw [show N - 1 - 1 = N - 2 by omega]
  ring

private theorem radialProfile_contDiff {N : ℕ} (hN : 3 ≤ N) (s : ℝ) :
    ContDiff ℝ 2 (radialProfile N s) :=
  (positivePower_contDiff_two hN).comp
    (contDiff_const.sub (contDiff_id.div_const _))

/-- The global gradient formula uses the literal positive part, including the boundary. -/
theorem retention_barrier_gradient {d N : ℕ} (hN : 3 ≤ N) (s : ℝ) (Y : PDE.Vec d) :
    PDE.classicalGradient (barrier N s) Y =
      (-2 * N / s ^ 2 * (max (1 - PDE.vecNormSq Y / s ^ 2) 0) ^ (N - 1)) • Y := by
  have h := classicalGradient_comp_vecNormSq_sub
    (m := (0 : PDE.Vec d)) (x := Y)
    ((radialProfile_derivative (by omega : 2 ≤ N) s
      (PDE.vecNormSq (Y - 0))).differentiableAt)
  simp only [sub_zero] at h
  change PDE.classicalGradient (fun y => radialProfile N s (PDE.vecNormSq y)) Y = _
  rw [h, radialProfile_deriv (by omega)]
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_zero, positivePower]
  ring

/-- The global Hessian formula uses the literal positive part through order two. -/
theorem retention_barrier_hessian {d N : ℕ} (hN : 3 ≤ N)
    (s : ℝ) (hs : 0 < s) (Y : PDE.Vec d) :
    Hess (barrier N s) Y =
      (-2 * N / s ^ 2 * (max (1 - PDE.vecNormSq Y / s ^ 2) 0) ^ (N - 1)) • (1 : PDE.Mat d) +
      ((4 * N * (N - 1 : ℕ) / s ^ 4 *
        (max (1 - PDE.vecNormSq Y / s ^ 2) 0) ^ (N - 2)) •
          Matrix.of (fun i j => Y i * Y j) : PDE.Mat d) := by
  have hs0 : s ≠ 0 := hs.ne'
  ext i j
  change sliceHessian (fun y => radialProfile N s (PDE.vecNormSq y)) Y i j = _
  have h := sliceHessian_comp_vecNormSq_sub
    (m := (0 : PDE.Vec d)) (x := Y)
    (radialProfile_contDiff hN s).contDiffAt i j
  simp only [sub_zero] at h
  rw [h, radialProfile_second_deriv hN, radialProfile_deriv (by omega)]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    positivePower, Pi.zero_apply, sub_zero, Matrix.of_apply]
  generalize max (1 - PDE.vecNormSq Y / s ^ 2) 0 = w
  split_ifs <;> field_simp [hs0] <;> ring

/-- The source retention polynomial, including its boundary jets. -/
theorem retention_polynomial_barrier {d N : ℕ} (hN : 3 ≤ N)
    (s : ℝ) (hs : 0 < s) :
    ContDiff ℝ 2 (barrier (d := d) N s) ∧
    (∀ Y : PDE.Vec d, 0 ≤ barrier N s Y ∧ barrier N s Y ≤ 1) ∧ barrier (d := d) N s 0 = 1 ∧
    (∀ Y : PDE.Vec d, Y ∈ PDE.euclideanBall 0 s →
      PDE.classicalGradient (barrier N s) Y =
        (-2 * N / s ^ 2 * (1 - PDE.vecNormSq Y / s ^ 2) ^ (N - 1)) • Y ∧
      Hess (barrier N s) Y =
        (-2 * N / s ^ 2 * (1 - PDE.vecNormSq Y / s ^ 2) ^ (N - 1)) • (1 : PDE.Mat d) +
        ((4 * N * (N - 1 : ℕ) / s ^ 4 *
          (1 - PDE.vecNormSq Y / s ^ 2) ^ (N - 2)) •
            Matrix.of (fun i j => Y i * Y j) : PDE.Mat d)) ∧
    (∀ Y : PDE.Vec d, Y ∉ PDE.euclideanBall 0 s →
      barrier N s Y = 0 ∧ PDE.classicalGradient (barrier N s) Y = 0 ∧
        Hess (barrier N s) Y = 0) := by
  have hs2 : 0 < s ^ 2 := sq_pos_of_pos hs
  have hpow1 : N - 1 ≠ 0 := by omega
  have hpow2 : N - 2 ≠ 0 := by omega
  refine ⟨retention_barrier_contDiff hN s, ?_, ?_, ?_, ?_⟩
  · intro Y
    have h0 : 0 ≤ max (1 - PDE.vecNormSq Y / s ^ 2) 0 := le_max_right _ _
    have h1 : max (1 - PDE.vecNormSq Y / s ^ 2) 0 ≤ 1 := by
      have hsq := PDE.vecNormSq_nonneg Y
      have hdiv := div_nonneg hsq hs2.le
      exact max_le (by linarith) zero_le_one
    exact ⟨pow_nonneg h0 _, pow_le_one₀ h0 h1⟩
  · simp [barrier, PDE.vecNormSq, PDE.vecDot]
  · intro Y hY
    have hY' : PDE.vecNormSq Y < s ^ 2 := by
      simpa only [PDE.euclideanBall, PDE.euclideanSqDist, mem_ofPred_eq, sub_zero] using hY
    have hw : 0 ≤ 1 - PDE.vecNormSq Y / s ^ 2 := by
      have := (div_lt_one hs2).mpr hY'
      linarith
    rw [retention_barrier_gradient hN s Y, retention_barrier_hessian hN s hs Y,
      max_eq_left hw]
    exact ⟨rfl, rfl⟩
  · intro Y hY
    have hY' : s ^ 2 ≤ PDE.vecNormSq Y := by
      simpa only [PDE.euclideanBall, PDE.euclideanSqDist, mem_ofPred_eq,
        sub_zero, not_lt] using hY
    have hw : 1 - PDE.vecNormSq Y / s ^ 2 ≤ 0 := by
      have := (one_le_div hs2).mpr hY'
      linarith
    rw [retention_barrier_gradient hN s Y, retention_barrier_hessian hN s hs Y]
    simp [barrier, max_eq_right hw, show N ≠ 0 by omega, hpow1, hpow2]

end HypoellipticAleksandrov.KineticAleksandrov.Decay
