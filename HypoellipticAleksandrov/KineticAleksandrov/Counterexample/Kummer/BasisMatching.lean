module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.BasisEndpoint
import Mathlib.Tactic

/-!
# Matching a classical solution to the M basis

The positive second solution permits reduction of order without division at a zero.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

open Set Filter
open scoped Topology

/-- The regular M solution has zero scaled derivative at the singular endpoint. -/
theorem tendsto_M_scaled_deriv_zero (a : ℝ) (b : Pos) :
    Tendsto (fun z : ℝ => z * deriv (M a b) z) (𝓝[>] 0) (𝓝 0) := by
  have hc : ContinuousAt (fun z : ℝ => z * deriv (M a b) z) 0 := by
    simp_rw [deriv_M]
    exact continuousAt_id.mul
      (continuousAt_const.mul (hasDerivAt_M _ _ 0).continuousAt)
  simpa using hc.tendsto.mono_left nhdsWithin_le_nhds

/-- The two literal M solutions have a nonzero normalized Wronskian. -/
theorem weightedWronskian_M_secondM (a z : ℝ) (hz : 0 < z) :
    weightedWronskian (2 / 3) (M a b23) (secondM a) z = -(1 / 3 : ℝ) := by
  have hm : ContDiffOn ℝ (⊤ : ℕ∞) (M a b23) (Ioi 0) :=
    ((analyticOnNhd_M a b23).contDiffOn uniqueDiffOn_univ).mono (subset_univ _)
  have hm0 : Tendsto (M a b23) (𝓝[>] 0) (𝓝 1) := by
    simpa using (hasDerivAt_M a b23 0).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  simpa only [mul_one] using weightedWronskian_secondM_eq a (M a b23) 1 hm
    (by intro w _; simpa only [b23] using M_ode a b23 w) hm0
    (tendsto_M_scaled_deriv_zero _ _) z hz

/-- Every classical solution with the two endpoint limits is a linear combination of the M basis. -/
theorem exists_secondM_coefficient (a : NegThird) (f : ℝ → ℝ) (F : ℝ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Ioi 0))
    (ho : ∀ z > 0, z * deriv (deriv f) z + (2 / 3 - z) * deriv f z - a.1 * f z = 0)
    (hlim : Tendsto f (𝓝[>] 0) (𝓝 F))
    (hdlim : Tendsto (fun z : ℝ => z * deriv f z) (𝓝[>] 0) (𝓝 0)) :
    ∃ B : ℝ, ∀ z > 0, f z = F * M a.1 b23 z + B * secondM a.1 z := by
  have hm : ContDiffOn ℝ (⊤ : ℕ∞) (M a.1 b23) (Ioi 0) :=
    ((analyticOnNhd_M a.1 b23).contDiffOn uniqueDiffOn_univ).mono (subset_univ _)
  have hm0 : Tendsto (M a.1 b23) (𝓝[>] 0) (𝓝 1) := by
    simpa using (hasDerivAt_M a.1 b23 0).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hwf (z : ℝ) (hz : 0 < z) :=
    weightedWronskian_secondM_eq a.1 f F hf ho hlim hdlim z hz
  have hwm (z : ℝ) (hz : 0 < z) := weightedWronskian_secondM_eq a.1 (M a.1 b23) 1 hm
    (by intro z _; simpa only [b23] using M_ode a.1 b23 z) hm0
      (tendsto_M_scaled_deriv_zero _ _) z hz
  let q : ℝ → ℝ := fun z => (f z - F * M a.1 b23 z) / secondM a.1 z
  have hd (z : ℝ) (hz : z ∈ Ioi (0 : ℝ)) : HasDerivAt q 0 z := by
    have hdf := (hf.differentiableOn (by simp)).differentiableAt
      (isOpen_Ioi.mem_nhds hz)
    have hdm := (hasDerivAt_M a.1 b23 z).differentiableAt
    have hdg := ((contDiffOn_secondM a.1).differentiableOn (by simp)).differentiableAt
      (isOpen_Ioi.mem_nhds hz)
    have h := (hdf.hasDerivAt.sub (hdm.hasDerivAt.const_mul F)).div hdg.hasDerivAt
      (ne_of_gt (secondM_pos a z hz))
    convert h using 1
    · have hw : deriv f z * secondM a.1 z - f z * deriv (secondM a.1) z =
          F * (deriv (M a.1 b23) z * secondM a.1 z -
            M a.1 b23 z * deriv (secondM a.1) z) := by
        have he := hwf z hz
        have hm' := hwm z hz
        dsimp only [weightedWronskian] at he hm'
        have hp : Real.exp (-z) * z ^ (2 / 3 : ℝ) ≠ 0 := ne_of_gt
          (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hz _))
        apply (mul_left_cancel₀ hp)
        linear_combination he - F * hm'
      dsimp only [Pi.sub_apply]
      symm
      rw [div_eq_zero_iff]
      left
      linear_combination hw
  obtain ⟨B, hB⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero
    (convex_Ioi (0 : ℝ)).isPreconnected
    (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd z hz).deriv)
  refine ⟨B, fun z hz => ?_⟩
  have h := hB z hz
  dsimp [q] at h
  have he := (div_eq_iff (ne_of_gt (secondM_pos a z hz))).mp h
  linarith only [he]

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
