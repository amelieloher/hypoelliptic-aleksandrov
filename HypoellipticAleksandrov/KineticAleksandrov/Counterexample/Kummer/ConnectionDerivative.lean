module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.ConnectionLimits
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.UAsymptoticsDerivatives
import Mathlib.Tactic

/-!
# The scaled derivative at the singular endpoint

An additional factor of the Laplace parameter restores dominated convergence for the first moment.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

open Set Filter MeasureTheory
open scoped Topology

/-- Renormalized first moment, with its small Laplace parameter included. -/
def connectionMoment (c z : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), (z * t) * Real.exp (-(z * t)) * connectionKernel c t

/-- The first moment multiplier is bounded by one for a nonnegative argument. -/
theorem mul_exp_neg_le_one (y : ℝ) : y * Real.exp (-y) ≤ 1 :=
  (Real.mul_exp_neg_le_exp_neg_one y).trans (Real.exp_le_one_iff.mpr (by norm_num))

/-- Integrability of the renormalized first moment. -/
theorem integrableOn_connectionMoment (c z : ℝ) (hc : 0 < c) (hc1 : c < 1 / 3)
    (hz : 0 ≤ z) :
    IntegrableOn (fun t => (z * t) * Real.exp (-(z * t)) * connectionKernel c t) (Ioi 0) := by
  apply (integrableOn_connectionKernel c hc hc1).mono'
  · exact ContinuousOn.aestronglyMeasurable
      ((by fun_prop : Continuous (fun t : ℝ => (z * t) * Real.exp (-(z * t)))).continuousOn.mul
        (continuousOn_connectionKernel c)) measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_of_nonneg (mul_nonneg
      (mul_nonneg (mul_nonneg hz ht.le) (Real.exp_pos _).le)
      (connectionKernel_nonneg c t hc1.le ht))]
    exact mul_le_of_le_one_left (connectionKernel_nonneg c t hc1.le ht)
      (mul_exp_neg_le_one (z * t))

/-- Dominated convergence for the renormalized first moment. -/
theorem tendsto_connectionMoment_zero (c : ℝ) (hc : 0 < c) (hc1 : c < 1 / 3) :
    Tendsto (connectionMoment c) (𝓝[>] 0) (𝓝 0) := by
  have hl : Tendsto (connectionMoment c) (𝓝[>] 0)
      (𝓝 (∫ _t in Ioi (0 : ℝ), (0 : ℝ))) := by
    apply tendsto_integral_filter_of_dominated_convergence (connectionKernel c)
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact (integrableOn_connectionMoment c z hc hc1 hz.le).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with z hz
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_of_nonneg (mul_nonneg
        (mul_nonneg (mul_nonneg hz.le ht.le) (Real.exp_pos _).le)
        (connectionKernel_nonneg c t hc1.le ht))]
      exact mul_le_of_le_one_left (connectionKernel_nonneg c t hc1.le ht)
        (mul_exp_neg_le_one (z * t))
    · exact integrableOn_connectionKernel c hc hc1
    · filter_upwards with t
      have h : ContinuousAt
          (fun z : ℝ => (z * t) * Real.exp (-(z * t)) * connectionKernel c t) 0 := by
        fun_prop
      simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  simpa using hl

/-- Moment decomposition using the same finite-part kernel. -/
theorem laplaceIntegral_connectionMoment (c : ℝ) (hc : 0 < c) (hc1 : c < 1 / 3)
    (z : ℝ) (hz : 0 < z) :
    z * laplaceIntegral (c + 1) (7 / 3) z =
      z ^ (-(1 / 3 : ℝ)) * Real.Gamma (4 / 3) + connectionMoment c z := by
  have hl := integrableOn_laplaceKernelReal (c + 1) (7 / 3) z (by linarith) hz
  have hg := integrableOn_gammaKernel (4 / 3 : ℝ) z (by norm_num) hz
  have hm := integrableOn_connectionMoment c z hc hc1 hz.le
  have he : ∀ t ∈ Ioi (0 : ℝ), z * laplaceKernelReal (c + 1) (7 / 3) z t =
      z * (Real.exp (-(z * t)) * t ^ ((4 / 3 : ℝ) - 1)) +
        (z * t) * Real.exp (-(z * t)) * connectionKernel c t := by
    intro t ht
    dsimp [laplaceKernelReal, connectionKernel]
    have hp : t ^ c = t * t ^ (c - 1) := by
      conv_rhs => lhs; rw [← Real.rpow_one t]
      rw [← Real.rpow_add ht]
      congr 1
      ring
    have hq : t ^ ((4 / 3 : ℝ) - 1) = t * t ^ (-(2 / 3 : ℝ)) := by
      conv_rhs => lhs; rw [← Real.rpow_one t]
      rw [← Real.rpow_add ht]
      congr 1
      ring
    rw [show c + 1 - 1 = c by ring,
      show (7 / 3 : ℝ) - (c + 1) - 1 = 1 / 3 - c by ring, hp, hq]
    ring
  change z * (∫ t in Ioi (0 : ℝ), laplaceKernelReal (c + 1) (7 / 3) z t) = _
  rw [← integral_const_mul, setIntegral_congr_fun measurableSet_Ioi he,
    integral_add (hg.const_mul z) hm, integral_const_mul,
    integral_gammaKernel (4 / 3 : ℝ) z (by norm_num) hz]
  have hp : z * z ^ (-(4 / 3 : ℝ)) = z ^ (-(1 / 3 : ℝ)) := by
    conv_lhs => lhs; rw [← Real.rpow_one z]
    rw [← Real.rpow_add hz]
    congr 1
    ring
  rw [← mul_assoc, hp]
  rfl

/-- A scaled derivative identity where both finite-part transforms have endpoint limits. -/
theorem UNr_scaled_deriv (a : NegThird) (z : ℝ) (hz : 0 < z) :
    z * deriv (UNr a) z = z ^ (1 / 3 : ℝ) * (Real.Gamma (a.1 + 1 / 3))⁻¹ *
      ((1 / 3 : ℝ) * connectionIntegral (a.1 + 1 / 3) z -
        connectionMoment (a.1 + 1 / 3) z) := by
  have hc : 0 < a.1 + 1 / 3 := by linarith [a.2.1]
  have hc1 : a.1 + 1 / 3 < 1 / 3 := by linarith [a.2.2]
  have hui := hasDerivAt_UIr ⟨a.1 + 1 / 3, hc⟩ (4 / 3) z hz
  have hd := hasDerivAt_power_mul (UIr ⟨a.1 + 1 / 3, hc⟩ (4 / 3))
    (1 / 3 : ℝ) z hz hui.differentiableAt.hasDerivAt
  rw [hui.deriv] at hd
  have he : deriv (UNr a) z =
      (1 / 3 : ℝ) * z ^ ((1 / 3 : ℝ) - 1) * UIr ⟨a.1 + 1 / 3, hc⟩ (4 / 3) z +
      z ^ (1 / 3 : ℝ) * (-(Real.Gamma (a.1 + 1 / 3))⁻¹ *
        laplaceIntegral (a.1 + 1 / 3 + 1) (4 / 3 + 1) z) := hd.deriv
  rw [he, UIr_connection_decomposition _ hc1 z hz]
  have hm := laplaceIntegral_connectionMoment _ hc hc1 z hz
  rw [show (4 / 3 : ℝ) + 1 = 7 / 3 by ring] 
  have hp : z * z ^ ((1 / 3 : ℝ) - 1) = z ^ (1 / 3 : ℝ) := by
    conv_lhs => lhs; rw [← Real.rpow_one z]
    rw [← Real.rpow_add hz]
    congr 1
    ring
  have hg := Real.Gamma_add_one (by norm_num : (1 / 3 : ℝ) ≠ 0)
  rw [show (1 / 3 : ℝ) + 1 = 4 / 3 by ring] at hg
  calc
    _ = z ^ (1 / 3 : ℝ) * (Real.Gamma (a.1 + 1 / 3))⁻¹ *
        ((1 / 3 : ℝ) * (z ^ (-(1 / 3 : ℝ)) * Real.Gamma (1 / 3) +
          connectionIntegral (a.1 + 1 / 3) z) -
          z * laplaceIntegral (a.1 + 1 / 3 + 1) (7 / 3) z) := by
            rw [← hp]
            ring
    _ = _ := by rw [hm, hg]; ring

/-- The scaled first derivative tends to zero at the singular endpoint. -/
theorem tendsto_UNr_scaled_deriv_zero (a : NegThird) :
    Tendsto (fun z : ℝ => z * deriv (UNr a) z) (𝓝[>] 0) (𝓝 0) := by
  have hc : 0 < a.1 + 1 / 3 := by linarith [a.2.1]
  have hc1 : a.1 + 1 / 3 < 1 / 3 := by linarith [a.2.2]
  have hp : Tendsto (fun z : ℝ => z ^ (1 / 3 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (Real.continuousAt_rpow_const 0 (1 / 3 : ℝ)
      (Or.inr (by norm_num))).tendsto.mono_left nhdsWithin_le_nhds
  have hl := (hp.mul_const (Real.Gamma (a.1 + 1 / 3))⁻¹).mul
    (((tendsto_connectionIntegral_zero _ hc hc1).const_mul (1 / 3 : ℝ)).sub
      (tendsto_connectionMoment_zero _ hc hc1))
  simp only [zero_mul] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (UNr_scaled_deriv a z hz).symm

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
