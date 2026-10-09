module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Real Laplace moments and exponential tails

These estimates control the discarded tails in the negative-axis Euler integral.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

open MeasureTheory Set Filter Asymptotics

/-- The positive Gamma moment kernel at Laplace scale X. -/
def laplaceMoment (a X t : ℝ) : ℝ := t ^ (a - 1) * Real.exp (-(X * t))

/-- The positive-scale Gamma moment is integrable. -/
theorem integrable_laplaceMoment (a X : ℝ) (ha : 0 < a) (hX : 0 < X) :
    IntegrableOn (laplaceMoment a X) (Ioi 0) volume := by
  change IntegrableOn (fun t : ℝ => t ^ (a - 1) * Real.exp (-(X * t))) (Ioi 0) volume
  simpa only [Real.rpow_one, neg_mul] using
    integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a - 1)
      (b := X) (by linarith only [ha]) zero_lt_one hX

/-- Nonnegativity of the moment kernel. -/
theorem laplaceMoment_nonneg (a X t : ℝ) (ht : 0 ≤ t) : 0 ≤ laplaceMoment a X t :=
  mul_nonneg (Real.rpow_nonneg ht _) (Real.exp_pos _).le

/-- The full Gamma moment at positive Laplace scale. -/
theorem integral_laplaceMoment (a X : ℝ) (ha : 0 < a) (hX : 0 < X) :
    (∫ t in Ioi (0 : ℝ), laplaceMoment a X t) = X ^ (-a) * Real.Gamma a := by
  change (∫ t in Ioi (0 : ℝ), t ^ (a - 1) * Real.exp (-(X * t))) = _
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi ha hX,
    one_div, Real.inv_rpow hX.le, Real.rpow_neg hX.le]

/-- Pointwise exponential gain on the discarded half-line. -/
theorem laplaceMoment_tail_pointwise (a X t : ℝ) (hX : 0 ≤ X) (ht : 1 / 2 ≤ t) :
    laplaceMoment a X t ≤ Real.exp (-(X / 4)) * laplaceMoment a (X / 2) t := by
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht
  have he : -(X * t) ≤ -(X / 4) - (X / 2) * t := by
    nlinarith only [mul_nonneg hX (sub_nonneg.mpr ht)]
  have heq : Real.exp (-(X / 4) - (X / 2) * t) =
      Real.exp (-(X / 4)) * Real.exp (-((X / 2) * t)) := by
    rw [← Real.exp_add, sub_eq_add_neg]
  have hh2 := Real.exp_le_exp.mpr he
  rw [heq] at hh2
  simpa only [laplaceMoment, mul_left_comm] using
    mul_le_mul_of_nonneg_left hh2 (Real.rpow_nonneg ht0 (a - 1))

/-- The discarded half-line moment has an explicit exponential bound. -/
theorem laplaceMoment_tail_bound (a X : ℝ) (ha : 0 < a) (hX : 0 < X) :
    (∫ t in Ioi (1 / 2 : ℝ), laplaceMoment a X t) ≤
      Real.exp (-(X / 4)) * ((X / 2) ^ (-a) * Real.Gamma a) := by
  have hi := integrable_laplaceMoment a X ha hX
  have hi2 := integrable_laplaceMoment a (X / 2) ha (half_pos hX)
  have hsub : Ioi (1 / 2 : ℝ) ⊆ Ioi 0 := Ioi_subset_Ioi (by norm_num)
  have hn : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ laplaceMoment a (X / 2) t :=
    ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => laplaceMoment_nonneg a _ t ht.le)
  calc
    _ ≤ ∫ t in Ioi (1 / 2 : ℝ), Real.exp (-(X / 4)) * laplaceMoment a (X / 2) t := by
      apply setIntegral_mono_on (hi.mono_set hsub)
        ((hi2.mono_set hsub).const_mul (Real.exp (-(X / 4)))) measurableSet_Ioi
      intro t ht
      exact laplaceMoment_tail_pointwise a X t hX.le ht.le
    _ = Real.exp (-(X / 4)) * ∫ t in Ioi (1 / 2 : ℝ), laplaceMoment a (X / 2) t :=
      integral_const_mul _ _
    _ ≤ Real.exp (-(X / 4)) * ∫ t in Ioi (0 : ℝ), laplaceMoment a (X / 2) t := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact setIntegral_mono_set hi2 hn (Filter.Eventually.of_forall hsub)
    _ = _ := by rw [integral_laplaceMoment a (X / 2) ha (half_pos hX)]

/-- Every discarded Gamma moment is smaller than any prescribed algebraic order. -/
theorem laplaceMoment_tail_isBigO (a r : ℝ) (ha : 0 < a) :
    IsBigO atTop (fun X => ∫ t in Ioi (1 / 2 : ℝ), laplaceMoment a X t)
      (fun X => X ^ r) := by
  have he : IsBigO atTop (fun X : ℝ => Real.exp (-(X / 4)))
      (fun X => X ^ (r + a)) := by
    simpa only [neg_div, div_eq_mul_inv, mul_comm, one_mul, mul_neg] using
      (isLittleO_exp_neg_mul_rpow_atTop (a := 1 / 4) (by norm_num) (r + a)).isBigO
  have hp : IsBigO atTop (fun X : ℝ => (X / 2) ^ (-a) * Real.Gamma a)
      (fun X => X ^ (-a)) := by
    refine IsBigO.of_bound ((|(2 : ℝ) ^ (-a)|)⁻¹ * |Real.Gamma a|) ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    rw [Real.div_rpow hX.le (by norm_num), Real.norm_eq_abs, Real.norm_eq_abs,
      abs_mul, abs_div, div_eq_mul_inv]
    ring_nf
    rfl
  have hh := he.mul_atTop_rpow_of_isBigO_rpow (r + a) (-a) r hp (by linarith)
  apply IsBigO.trans ?_ hh
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  have hn : 0 ≤ ∫ t in Ioi (1 / 2 : ℝ), laplaceMoment a X t := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro t ht
    apply laplaceMoment_nonneg a X t
    change 1 / 2 < t at ht
    linarith only [ht]
  have hb := laplaceMoment_tail_bound a X ha hX
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg hn, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (Real.rpow_nonneg (half_pos hX).le _)
        (Real.Gamma_pos_of_pos ha).le)), one_mul]
  exact hb

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
