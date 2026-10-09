module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# Scalar connection constants and the matching diffusivity

Literal Appendix C constants and the finite matching ratio, for `0 < gamma < 1/3`.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter Set
open scoped Topology

/-- The constant term in the connection formula. -/
def gammaA (gamma : ℝ) : ℝ := Real.Gamma (1 / 3) / Real.Gamma (1 / 3 - gamma)

/-- The linear coefficient in the connection formula. -/
def gammaB (gamma : ℝ) : ℝ := Real.Gamma (-(1 / 3)) / Real.Gamma (-gamma)

/-- The first negative-axis leading coefficient. -/
def Pgamma (gamma : ℝ) : ℝ :=
  Real.cos (Real.pi * gamma) - Real.sin (Real.pi * gamma) / Real.sqrt 3

/-- The second negative-axis leading coefficient. -/
def Qgamma (gamma : ℝ) : ℝ := 2 * Real.sin (Real.pi * gamma) / Real.sqrt 3

private theorem gamma_neg_of_mem (s : ℝ) (hs : -1 < s) (hs0 : s < 0) :
    Real.Gamma s < 0 := by
  have hp := Real.Gamma_pos_of_pos (show 0 < s + 1 by linarith only [hs])
  rw [Real.Gamma_add_one hs0.ne] at hp
  exact neg_of_mul_pos_right hp hs0.le

/-- Both connection constants are strictly positive. -/
theorem gamma_constants_pos (gamma : ℝ) (hg : 0 < gamma) (hg1 : gamma < 1 / 3) :
    0 < gammaA gamma ∧ 0 < gammaB gamma := by
  constructor
  · exact div_pos (Real.Gamma_pos_of_pos (by norm_num))
      (Real.Gamma_pos_of_pos (by linarith only [hg1]))
  · exact div_pos_of_neg_of_neg (gamma_neg_of_mem (-(1 / 3)) (by norm_num)
      (by norm_num)) (gamma_neg_of_mem (-gamma) (by linarith only [hg1]) (neg_neg_of_pos hg))

/-- The trigonometric leading coefficients have the signs needed by matching. -/
theorem PQ_pos (gamma : ℝ) (hg : 0 < gamma) (hg1 : gamma < 1 / 3) :
    0 < Pgamma gamma ∧ 0 < Qgamma gamma := by
  have ht : 0 < Real.pi * gamma := mul_pos Real.pi_pos hg
  have ht1 : Real.pi * gamma < Real.pi / 3 := by
    nlinarith only [mul_lt_mul_of_pos_left hg1 Real.pi_pos]
  have hs := Real.sin_pos_of_pos_of_lt_pi ht (by linarith only [ht1, Real.pi_pos])
  have hroot : 0 < Real.sqrt 3 := by positivity
  have hc : 0 < Real.cos (Real.pi * gamma + Real.pi / 6) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith only [ht, Real.pi_pos],
      by linarith only [ht1]⟩
  rw [Real.cos_add, Real.cos_pi_div_six, Real.sin_pi_div_six] at hc
  constructor
  · unfold Pgamma
    apply sub_pos.mpr
    apply (div_lt_iff₀ hroot).mpr
    nlinarith only [hc]
  · exact div_pos (mul_pos (by norm_num) hs) hroot

/-- At the unit diffusivity the matching difference is strictly negative. -/
theorem matching_difference_one_neg (gamma : ℝ) (hg : 0 < gamma)
    (hg1 : gamma < 1 / 3) : Pgamma gamma - Qgamma gamma - 1 < 0 := by
  have hq := (PQ_pos gamma hg hg1).2
  have hs := Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hg)
    (by nlinarith only [mul_lt_mul_of_pos_left hg1 Real.pi_pos, Real.pi_pos])
  have hp : Pgamma gamma ≤ 1 := by
    unfold Pgamma
    have hnon := div_nonneg hs.le (Real.sqrt_nonneg 3)
    linarith only [Real.cos_le_one (Real.pi * gamma), hnon]
  linarith only [hp, hq]

/-- There is a finite diffusivity ratio greater than one matching the two traces. -/
theorem exists_matching_ratio (gamma : ℝ) (hg : 0 < gamma) (hg1 : gamma < 1 / 3) :
    ∃ Lam : ℝ, 1 < Lam ∧
      Pgamma gamma - Qgamma gamma * Real.rpow Lam (-(1 / 3)) =
        Real.rpow Lam (-gamma) := by
  let f : ℝ → ℝ := fun L =>
    Pgamma gamma - Qgamma gamma * L ^ (-(1 / 3 : ℝ)) - L ^ (-gamma)
  have hf1 : f 1 < 0 := by
    simpa only [f, Real.one_rpow, mul_one] using matching_difference_one_neg gamma hg hg1
  have hlim : Tendsto f atTop (𝓝 (Pgamma gamma)) := by
    convert (tendsto_const_nhds.sub
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul
        (Qgamma gamma))).sub (tendsto_rpow_neg_atTop hg) using 1
    simp only [mul_zero, sub_zero]
  have he : ∀ᶠ L in atTop, 0 < f L :=
    hlim.eventually (Ioi_mem_nhds (PQ_pos gamma hg hg1).1)
  obtain ⟨L, hL, hpos⟩ := (he.and (eventually_gt_atTop (1 : ℝ))).exists
  have hc : ContinuousOn f (Icc 1 L) := by
    apply ContinuousOn.sub
    · apply continuousOn_const.sub
      apply continuousOn_const.mul
      exact continuousOn_id.rpow_const (fun x hx =>
        Or.inl (ne_of_gt (show 0 < id x from lt_of_lt_of_le zero_lt_one hx.1)))
    · exact continuousOn_id.rpow_const (fun x hx =>
      Or.inl (ne_of_gt (show 0 < id x from lt_of_lt_of_le zero_lt_one hx.1)))
  obtain ⟨Lam, hLam, hz⟩ := intermediate_value_Icc hpos.le hc ⟨hf1.le, hL.le⟩
  refine ⟨Lam, lt_of_le_of_ne hLam.1 ?_, ?_⟩
  · intro heq
    have : Lam = 1 := heq.symm
    rw [this] at hz
    rw [hz] at hf1
    exact lt_irrefl _ hf1
  · change Pgamma gamma - Qgamma gamma * Lam ^ (-(1 / 3 : ℝ)) -
      Lam ^ (-gamma) = 0 at hz
    exact sub_eq_zero.mp hz

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
