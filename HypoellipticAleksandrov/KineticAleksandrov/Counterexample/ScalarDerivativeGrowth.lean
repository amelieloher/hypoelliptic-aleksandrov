module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarCancellation
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarNormalized
import Mathlib.Tactic

/-! # Actual first and second derivative power bounds on the similarity rays -/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter Asymptotics Set
open scoped Topology ContDiff

/-- The actual second derivative of a positive-ray power remainder. -/
theorem scalar_power_remainder_deriv2 (f : ℝ → ℝ) (alpha c s : ℝ) (hs : 0 < s)
    (hf : ContDiff ℝ 2 f) :
    deriv (deriv (fun t => f t - c * Real.rpow t alpha)) s =
      deriv (deriv f) s - c * alpha * (alpha - 1) * Real.rpow s (alpha - 2) := by
  have he : deriv (fun t => f t - c * Real.rpow t alpha) =ᶠ[𝓝 s]
      fun t => deriv f t - c * alpha * Real.rpow t (alpha - 1) := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    exact scalar_power_remainder_deriv f alpha c t ht (hf.differentiable (by norm_num) t)
  rw [he.deriv_eq]
  have hp := (Real.hasDerivAt_rpow_const (p := alpha - 1) (Or.inl hs.ne')).const_mul
    (c * alpha)
  have hd := (hf.differentiable_deriv_two s).hasDerivAt.sub hp
  simpa only [Real.rpow_eq_pow, Pi.sub_def, Pi.mul_def,
    show alpha - 1 - 1 = alpha - 2 by ring, mul_assoc] using hd.deriv

/-- A differentiated power remainder gives a finite normalized first-derivative limit. -/
theorem scalar_deriv_tail_ratio (f : ℝ → ℝ) (alpha c : ℝ) (hf : ContDiff ℝ 2 f)
    (hr : IsBigO atTop (deriv (fun s => f s - c * Real.rpow s alpha))
      (fun s => Real.rpow s (alpha - 4))) :
    Tendsto (fun s => deriv f s / Real.rpow s (alpha - 1)) atTop (𝓝 (c * alpha)) := by
  have hzero : Tendsto (fun s =>
      deriv (fun t => f t - c * Real.rpow t alpha) s / Real.rpow s (alpha - 1))
      atTop (𝓝 0) := by
    apply scalar_tail_ratio _ (alpha - 1) 0
    simpa only [zero_mul, sub_zero, show alpha - 1 - 3 = alpha - 4 by ring] using hr
  have ht := hzero.add_const (c * alpha)
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  rw [scalar_power_remainder_deriv f alpha c s hs (hf.differentiable (by norm_num) s)]
  have hp : Real.rpow s (alpha - 1) ≠ 0 := by
    simpa only [Real.rpow_eq_pow] using (Real.rpow_pos_of_pos hs (alpha - 1)).ne'
  field_simp
  ring

/-- A twice differentiated remainder gives a finite normalized second-derivative limit. -/
theorem scalar_deriv2_tail_ratio (f : ℝ → ℝ) (alpha c : ℝ) (hf : ContDiff ℝ 2 f)
    (hr : IsBigO atTop (deriv (deriv (fun s => f s - c * Real.rpow s alpha)))
      (fun s => Real.rpow s (alpha - 5))) :
    Tendsto (fun s => deriv (deriv f) s / Real.rpow s (alpha - 2))
      atTop (𝓝 (c * alpha * (alpha - 1))) := by
  have hzero : Tendsto (fun s =>
      deriv (deriv (fun t => f t - c * Real.rpow t alpha)) s /
        Real.rpow s (alpha - 2)) atTop (𝓝 0) := by
    apply scalar_tail_ratio _ (alpha - 2) 0
    simpa only [zero_mul, sub_zero, show alpha - 2 - 3 = alpha - 5 by ring] using hr
  have ht := hzero.add_const (c * alpha * (alpha - 1))
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  rw [scalar_power_remainder_deriv2 f alpha c s hs hf]
  have hp : Real.rpow s (alpha - 2) ≠ 0 := by
    simpa only [Real.rpow_eq_pow] using (Real.rpow_pos_of_pos hs (alpha - 2)).ne'
  field_simp
  ring

/-- The actual positive-ray remainder derivatives agree locally with the U-branch derivatives. -/
theorem F_positive_remainder_derivatives (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam) :
    IsBigO atTop (deriv (fun s => F gamma Lam s -
      Real.rpow (9 * Lam) (-gamma.1) * Real.rpow s (3 * gamma.1)))
      (fun s => Real.rpow s (3 * gamma.1 - 4)) ∧
    IsBigO atTop (deriv (deriv (fun s => F gamma Lam s -
      Real.rpow (9 * Lam) (-gamma.1) * Real.rpow s (3 * gamma.1))))
      (fun s => Real.rpow s (3 * gamma.1 - 5)) := by
  have hp := Fplus_tail_derivatives gamma Lam hLam
  have he (s : ℝ) (hs : 0 < s) : (fun t => Fplus gamma Lam t -
      Real.rpow (9 * Lam) (-gamma.1) * Real.rpow t (3 * gamma.1)) =ᶠ[𝓝 s]
      fun t => F gamma Lam t -
        Real.rpow (9 * Lam) (-gamma.1) * Real.rpow t (3 * gamma.1) := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    simp only [F, show 0 < t from ht, ↓reduceIte]
  constructor
  · apply hp.1.congr' _ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    exact (he s hs).deriv_eq
  · apply hp.2.congr' _ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    exact (he s hs).deriv.deriv_eq

/-- The actual reflected negative-ray remainder derivatives agree with the M branch. -/
theorem F_negative_remainder_derivatives (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (hmatch : Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3)) =
      Real.rpow Lam (-gamma.1)) :
    IsBigO atTop (deriv (fun s => F gamma Lam (-s) -
      Real.rpow (9 * Lam) (-gamma.1) * Real.rpow s (3 * gamma.1)))
      (fun s => Real.rpow s (3 * gamma.1 - 4)) ∧
    IsBigO atTop (deriv (deriv (fun s => F gamma Lam (-s) -
      Real.rpow (9 * Lam) (-gamma.1) * Real.rpow s (3 * gamma.1))))
      (fun s => Real.rpow s (3 * gamma.1 - 5)) := by
  have hn := Fminus_negative_ray_tail_derivatives_of_M_jets
    Kummer.M_negative_expansion_jet gamma Lam hLam
  rw [scalar_matching_trace_coefficient gamma Lam hLam hmatch] at hn
  have he (s : ℝ) (hs : 0 < s) : (fun t => Fminus gamma Lam (-t) -
      Real.rpow (9 * Lam) (-gamma.1) * Real.rpow t (3 * gamma.1)) =ᶠ[𝓝 s]
      fun t => F gamma Lam (-t) -
        Real.rpow (9 * Lam) (-gamma.1) * Real.rpow t (3 * gamma.1) := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    simp only [F, neg_neg_of_pos (show 0 < t from ht),
      not_lt.mpr (neg_neg_of_pos (show 0 < t from ht)).le, ↓reduceIte]
  constructor
  · apply hn.1.congr' _ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    exact (he s hs).deriv_eq
  · apply hn.2.congr' _ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    exact (he s hs).deriv.deriv_eq

/-- A finite power-normalized limit gives the corresponding actual Big-O estimate. -/
theorem scalar_isBigO_of_power_ratio (f : ℝ → ℝ) (beta c : ℝ)
    (ht : Tendsto (fun s => f s / Real.rpow s beta) atTop (𝓝 c)) :
    IsBigO atTop f (fun s => Real.rpow s beta) := by
  refine isBigO_of_div_tendsto_nhds ?_ c ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    have hp : Real.rpow s beta ≠ 0 := by
      simpa only [Real.rpow_eq_pow] using (Real.rpow_pos_of_pos hs beta).ne'
    exact fun hz => False.elim (hp hz)
  · simpa only [Pi.div_def] using ht

/-- Both actual velocity derivative orders have their leading power bounds on the positive ray. -/
theorem F_derivatives_isBigO_atTop (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam) :
    IsBigO atTop (deriv (F gamma Lam)) (fun s => Real.rpow s (3 * gamma.1 - 1)) ∧
    IsBigO atTop (deriv (deriv (F gamma Lam))) (fun s => Real.rpow s (3 * gamma.1 - 2)) := by
  have hj := F_positive_remainder_derivatives gamma Lam hLam
  have hf := F_contDiff_two gamma Lam hLam
  constructor
  · exact scalar_isBigO_of_power_ratio _ _ _
      (scalar_deriv_tail_ratio _ _ _ hf hj.1)
  · exact scalar_isBigO_of_power_ratio _ _ _
      (scalar_deriv2_tail_ratio _ _ _ hf hj.2)

/-- Both actual derivative orders have their leading power bounds on the negative ray. -/
theorem F_derivatives_isBigO_atBot (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (hmatch : Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3)) =
      Real.rpow Lam (-gamma.1)) :
    IsBigO atBot (deriv (F gamma Lam)) (fun s => Real.rpow |s| (3 * gamma.1 - 1)) ∧
    IsBigO atBot (deriv (deriv (F gamma Lam)))
      (fun s => Real.rpow |s| (3 * gamma.1 - 2)) := by
  let f : ℝ → ℝ := fun s => F gamma Lam (-s)
  have hj := F_negative_remainder_derivatives gamma Lam hLam hmatch
  have hf : ContDiff ℝ 2 f := (F_contDiff_two gamma Lam hLam).comp contDiff_id.neg
  have h1 : IsBigO atTop (deriv f) (fun s => Real.rpow s (3 * gamma.1 - 1)) :=
    scalar_isBigO_of_power_ratio _ _ _ (scalar_deriv_tail_ratio f _ _ hf hj.1)
  have h2 : IsBigO atTop (deriv (deriv f)) (fun s => Real.rpow s (3 * gamma.1 - 2)) :=
    scalar_isBigO_of_power_ratio _ _ _ (scalar_deriv2_tail_ratio f _ _ hf hj.2)
  constructor
  · have hb := (h1.comp_tendsto tendsto_neg_atBot_atTop).neg_left
    apply hb.congr' _ _
    · exact Eventually.of_forall fun s => by
        simp only [f, Function.comp_def, deriv_comp_neg, neg_neg]
    · filter_upwards [eventually_lt_atBot (0 : ℝ)] with s hs
      simp only [Function.comp_def, abs_of_neg hs]
  · have hb := h2.comp_tendsto tendsto_neg_atBot_atTop
    apply hb.congr' _ _
    · exact Eventually.of_forall fun s => by
        simp only [f, Function.comp_def, scalar_deriv2_comp_neg, neg_neg]
    · filter_upwards [eventually_lt_atBot (0 : ℝ)] with s hs
      simp only [Function.comp_def, abs_of_neg hs]

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
