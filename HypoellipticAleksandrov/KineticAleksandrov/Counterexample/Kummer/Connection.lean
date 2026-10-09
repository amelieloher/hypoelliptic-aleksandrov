module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.BasisMatching
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.ConnectionDerivative
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

/-!
# The Kummer U connection formula

The literal positive integral solution matches the two literal M series, with Gamma coefficients
identified by convergent endpoint limits.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

open Set Filter
open scoped Topology

/-- The regular M increment vanishes after division by the fractional power. -/
theorem tendsto_M_fractional_increment_zero (a : ℝ) (b : Pos) :
    Tendsto (fun z : ℝ => (M a b z - 1) / z ^ (1 / 3 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
  have hs := (hasDerivAt_M a b 0).tendsto_slope_zero_right
  simp only [zero_add, M_zero, mul_one, smul_eq_mul] at hs
  have hp : Tendsto (fun z : ℝ => z ^ (2 / 3 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (Real.continuousAt_rpow_const 0 (2 / 3 : ℝ)
      (Or.inr (by norm_num))).tendsto.mono_left nhdsWithin_le_nhds
  have hl := hs.mul hp
  simp only [mul_zero] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have he : z ^ (2 / 3 : ℝ) * z ^ (1 / 3 : ℝ) = z := by
    rw [← Real.rpow_add hz, show (2 / 3 : ℝ) + 1 / 3 = 1 by ring, Real.rpow_one]
  have hn := ne_of_gt (Real.rpow_pos_of_pos hz (1 / 3 : ℝ))
  apply (eq_div_iff hn).mpr
  rw [mul_assoc, he]
  field_simp [ne_of_gt hz]

/-- Connection formula for the source's negative first-parameter range. -/
theorem UNr_connection (a : NegThird) (z : ℝ) (hz : 0 < z) :
    UNr a z =
      Real.Gamma (1 / 3) / Real.Gamma (a.1 + 1 / 3) * M a.1 b23 z +
      Real.Gamma (-(1 / 3)) / Real.Gamma a.1 * Real.rpow z (1 / 3) *
        M (a.1 + 1 / 3) b43 z := by
  let A : ℝ := Real.Gamma (1 / 3) / Real.Gamma (a.1 + 1 / 3)
  obtain ⟨B, hB⟩ := exists_secondM_coefficient a (UNr a) A (contDiffOn_UNr a)
    (UNr_ode a) (tendsto_UNr_zero a) (tendsto_UNr_scaled_deriv_zero a)
  have hm : Tendsto (M (a.1 + 1 / 3) b43) (𝓝[>] 0) (𝓝 1) := by
    simpa using (hasDerivAt_M (a.1 + 1 / 3) b43 0).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hl := ((tendsto_M_fractional_increment_zero a.1 b23).const_mul A).add
    (hm.const_mul B)
  simp only [mul_zero, mul_one, zero_add] at hl
  have he : Tendsto (fun w : ℝ => (UNr a w - A) / w ^ (1 / 3 : ℝ))
      (𝓝[>] 0) (𝓝 B) := by
    apply hl.congr'
    filter_upwards [self_mem_nhdsWithin] with w hw
    rw [hB w hw, secondM]
    have hp := ne_of_gt (Real.rpow_pos_of_pos hw (1 / 3 : ℝ))
    field_simp [hp]
    ring
  have hcoeff : B = Real.Gamma (-(1 / 3 : ℝ)) / Real.Gamma a.1 :=
    tendsto_nhds_unique he (tendsto_UNr_finitePart_zero a)
  rw [hB z hz, hcoeff, secondM, Real.rpow_eq_pow]
  dsimp only [A]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
