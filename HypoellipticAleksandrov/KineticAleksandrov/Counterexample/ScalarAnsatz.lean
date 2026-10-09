module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarProfile
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarMatching
import Mathlib.Tactic

/-!
# Scalar ansatz differentiation

The positive-position formula is differentiated in its actual signed similarity variable.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter Set
open scoped Topology ContDiff

/-- The source signed similarity coordinate. -/
def scalarSimilarity (x v : ℝ) : ℝ := -v / Real.rpow x (1 / 3)

/-- The velocity derivative of the signed similarity coordinate. -/
theorem scalarSimilarity_hasDerivAt_v (x v : ℝ) :
    HasDerivAt (scalarSimilarity x) (-(Real.rpow x (1 / 3))⁻¹) v := by
  unfold scalarSimilarity
  simpa only [Pi.neg_def, id_eq, neg_div, one_div] using
    ((hasDerivAt_id v).neg.div_const (Real.rpow x (1 / 3)))

/-- The position derivative of the signed similarity coordinate on x>0. -/
theorem scalarSimilarity_hasDerivAt_x (x v : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y => scalarSimilarity y v) ((v / 3) * Real.rpow x (-(4 / 3))) x := by
  have he : (fun y => scalarSimilarity y v) =ᶠ[𝓝 x]
      fun y => -v * y ^ (-(1 / 3 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simp only [scalarSimilarity, Real.rpow_eq_pow, Real.rpow_neg hy.le, div_eq_mul_inv]
  have hd := (Real.hasDerivAt_rpow_const (p := -(1 / 3 : ℝ)) (Or.inl hx.ne')).const_mul (-v)
  have heD : (-v) * (-(1 / 3 : ℝ) * x ^ (-(1 / 3 : ℝ) - 1)) =
      (v / 3) * Real.rpow x (-(4 / 3)) := by
    simp only [Real.rpow_eq_pow]
    rw [show -(1 / 3 : ℝ) - 1 = -(4 / 3 : ℝ) by norm_num]
    ring
  rw [heD] at hd
  exact hd.congr_of_eventuallyEq he

/-- The first velocity derivative of the source ansatz. -/
theorem scalarAnsatz_hasDerivAt_v (gamma : ScalarGamma) (Lam x v : ℝ)
    (hf : DifferentiableAt ℝ (F gamma Lam) (scalarSimilarity x v)) :
    HasDerivAt (scalarAnsatz gamma Lam x)
      (-(Real.rpow x gamma.1 / Real.rpow x (1 / 3)) *
        deriv (F gamma Lam) (scalarSimilarity x v)) v := by
  have h := (hf.hasDerivAt.comp v (scalarSimilarity_hasDerivAt_v x v)).const_mul
    (Real.rpow x gamma.1)
  unfold scalarAnsatz
  convert h using 1
  · rfl
  · ring

/-- The exact position derivative, before the source leading-term cancellation. -/
theorem scalarAnsatz_hasDerivAt_x (gamma : ScalarGamma) (Lam x v : ℝ) (hx : 0 < x)
    (hf : DifferentiableAt ℝ (F gamma Lam) (scalarSimilarity x v)) :
    HasDerivAt (fun y => scalarAnsatz gamma Lam y v)
      (gamma.1 * Real.rpow x (gamma.1 - 1) * F gamma Lam (scalarSimilarity x v) +
        Real.rpow x gamma.1 * deriv (F gamma Lam) (scalarSimilarity x v) *
          ((v / 3) * Real.rpow x (-(4 / 3)))) x := by
  have h := (Real.hasDerivAt_rpow_const (p := gamma.1) (Or.inl hx.ne')).mul
    (hf.hasDerivAt.comp x (scalarSimilarity_hasDerivAt_x x v hx))
  unfold scalarAnsatz
  convert h using 1
  · rfl
  · simp only [Real.rpow_eq_pow, Function.comp_def]
    ring

/-- The second velocity derivative in the signed similarity variable. -/
theorem scalarAnsatz_deriv2_v (gamma : ScalarGamma) (Lam x v : ℝ)
    (hf : ContDiffAt ℝ 2 (F gamma Lam) (scalarSimilarity x v)) :
    deriv (deriv (scalarAnsatz gamma Lam x)) v =
      (Real.rpow x gamma.1 / (Real.rpow x (1 / 3)) ^ 2) *
        deriv (deriv (F gamma Lam)) (scalarSimilarity x v) := by
  have hc : Continuous (scalarSimilarity x) := by unfold scalarSimilarity; fun_prop
  have he : deriv (scalarAnsatz gamma Lam x) =ᶠ[𝓝 v] fun w =>
      -(Real.rpow x gamma.1 / Real.rpow x (1 / 3)) *
        deriv (F gamma Lam) (scalarSimilarity x w) := by
    have hev := hc.continuousAt.tendsto.eventually (hf.eventually (by norm_num))
    filter_upwards [hev] with w hw
    exact (scalarAnsatz_hasDerivAt_v gamma Lam x w (hw.differentiableAt (by norm_num))).deriv
  have hd := (hf.derivWithin (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).differentiableAt
    (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have h := (hd.hasDerivAt.comp v (scalarSimilarity_hasDerivAt_v x v)).const_mul
    (-(Real.rpow x gamma.1 / Real.rpow x (1 / 3)))
  exact (h.congr_of_eventuallyEq he).deriv.trans (by ring)

/-- The cubic power of the positive similarity scale is exactly the position variable. -/
theorem scalar_similarity_scale_cube (x : ℝ) (hx : 0 < x) :
    (Real.rpow x (1 / 3)) ^ 3 = x := by
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_natCast (x ^ (1 / 3 : ℝ)) 3, ← Real.rpow_mul hx.le]
  norm_num

private theorem scalar_transport_algebra (X k V S Y gamma a f0 f1 f2 : ℝ)
    (hk : k ≠ 0) (hc : k ^ 3 = X) (hs : S = -V / k)
    (ho : a * f2 - S ^ 2 / 3 * f1 + gamma * S * f0 = 0) :
    a * (Y / k ^ 2 * f2) =
      V * (gamma * (Y / X) * f0 + Y * f1 * (V / 3 / (X * k))) := by
  have hv : V = -S * k := by rw [hs]; field_simp
  rw [hv, ← hc]
  field_simp
  linear_combination 3 * Y * ho

/-- Exact transport--diffusion reduction for the positive-position source ansatz. -/
theorem scalar_ansatz_calculus (gamma : ScalarGamma) (Lam a x v : ℝ) (hx : 0 < x)
    (hf : ContDiffAt ℝ 2 (F gamma Lam) (scalarSimilarity x v))
    (hode : a * deriv (deriv (F gamma Lam)) (scalarSimilarity x v) -
      (scalarSimilarity x v) ^ 2 / 3 * deriv (F gamma Lam) (scalarSimilarity x v) +
        gamma.1 * scalarSimilarity x v * F gamma Lam (scalarSimilarity x v) = 0) :
    a * deriv (deriv (scalarAnsatz gamma Lam x)) v =
      v * deriv (fun y => scalarAnsatz gamma Lam y v) x := by
  rw [scalarAnsatz_deriv2_v gamma Lam x v hf,
    (scalarAnsatz_hasDerivAt_x gamma Lam x v hx (hf.differentiableAt (by norm_num))).deriv]
  have hxp : Real.rpow x (gamma.1 - 1) = Real.rpow x gamma.1 / x := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_sub hx, Real.rpow_one]
  have hxn : Real.rpow x (-(4 / 3)) = (x * Real.rpow x (1 / 3))⁻¹ := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_neg hx.le, show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num,
      Real.rpow_add hx, Real.rpow_one]
  rw [hxp, hxn]
  have hk := (Real.rpow_pos_of_pos hx (1 / 3 : ℝ)).ne'
  have h := scalar_transport_algebra x (Real.rpow x (1 / 3)) v (scalarSimilarity x v)
    (Real.rpow x gamma.1) gamma.1 a (F gamma Lam (scalarSimilarity x v))
    (deriv (F gamma Lam) (scalarSimilarity x v))
    (deriv (deriv (F gamma Lam)) (scalarSimilarity x v)) hk
    (scalar_similarity_scale_cube x hx) rfl hode
  convert h using 1
  ring

/-- The signed similarity variable selects exactly the source diffusivity on x>0. -/
theorem scalarSimilarity_pos_iff (x v : ℝ) (hx : 0 < x) :
    0 < scalarSimilarity x v ↔ x * v < 0 := by
  have hk := Real.rpow_pos_of_pos hx (1 / 3 : ℝ)
  simp only [scalarSimilarity, Real.rpow_eq_pow]
  rw [lt_div_iff₀ hk]
  simp only [zero_mul, neg_pos]
  constructor
  · exact mul_neg_of_pos_of_neg hx
  · intro h
    by_contra hv
    exact (not_lt_of_ge (mul_nonneg hx.le (le_of_not_gt hv))) h

/-- The source ansatz satisfies its actual transport--diffusion equation on x>0. -/
theorem scalar_ansatz_ode (gamma : ScalarGamma) (Lam x v : ℝ)
    (hLam : 0 < Lam) (hx : 0 < x) :
    aLambda Lam x v * deriv (deriv (scalarAnsatz gamma Lam x)) v =
      v * deriv (fun y => scalarAnsatz gamma Lam y v) x := by
  apply scalar_ansatz_calculus gamma Lam _ x v hx
    ((F_contDiff_two gamma Lam hLam).contDiffAt)
  simpa only [aLambda, scalarSimilarity_pos_iff x v hx] using
    F_ode gamma Lam (scalarSimilarity x v) hLam

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
