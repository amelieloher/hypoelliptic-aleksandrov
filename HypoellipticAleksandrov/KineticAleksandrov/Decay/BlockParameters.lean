module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.SourceNotation
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Constants of the unit-frequency block

The literal source constants of the proof of the contraction at unit frequency
((3.15), (3.16)):

```
L₀ = 2 + 2π / m,   ρ = min {1, (128 L_b)^(-1/3)},   η = min {ρ / 4, 1 / (8 L_b L₀)},
L = L₀ + 4 ρ²,   R_* = 1 + 4ρ,   m₀ = exp (-C_* (η⁻² + 1/4) L₀).
```

`tent L₀ t = min {t, 1, L₀ - t}` is the source profile `𝖿`.  `block_parameters`
(Proposition 3.9) proves positivity and the three smallness inequalities used in
Steps 1-4 of the source proof.  The constants `C_*`, `h`, `q₀` are the previously obtained
source constants and enter only as positive reals.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay

theorem blockL0_pos {m : ℝ} (hm : 0 < m) : 0 < blockL0 m := by
  unfold blockL0
  have : 0 < 2 * Real.pi / m := by positivity
  linarith

theorem two_le_blockL0 {m : ℝ} (hm : 0 < m) : 2 ≤ blockL0 m := by
  unfold blockL0
  have : 0 < 2 * Real.pi / m := by positivity
  linarith

theorem blockRho_pos {Lb : ℝ} (hLb : 0 < Lb) : 0 < blockRho Lb := by
  unfold blockRho
  exact lt_min one_pos (Real.rpow_pos_of_pos (by positivity) _)

theorem blockRho_le_one (Lb : ℝ) : blockRho Lb ≤ 1 := min_le_left _ _

theorem blockRho_pow_three_le {Lb : ℝ} (hLb : 0 < Lb) :
    blockRho Lb ^ 3 ≤ 1 / (128 * Lb) := by
  have h128 : 0 < 128 * Lb := by positivity
  have h0 : 0 ≤ blockRho Lb := (blockRho_pos hLb).le
  have hle : blockRho Lb ≤ (128 * Lb) ^ (-(1 / 3 : ℝ)) := min_le_right _ _
  calc blockRho Lb ^ 3 ≤ ((128 * Lb) ^ (-(1 / 3 : ℝ))) ^ 3 := pow_le_pow_left₀ h0 hle 3
    _ = (128 * Lb) ^ (-(1 / 3 : ℝ) * (3 : ℕ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul h128.le]
    _ = 1 / (128 * Lb) := by
        rw [show -(1 / 3 : ℝ) * ((3 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one, one_div]

theorem blockEta_pos {m Lb : ℝ} (hm : 0 < m) (hLb : 0 < Lb) : 0 < blockEta m Lb := by
  unfold blockEta
  have hL0 := blockL0_pos hm
  exact lt_min (by have := blockRho_pos hLb; positivity) (by positivity)

theorem blockEta_le_rho_div_four (m Lb : ℝ) : blockEta m Lb ≤ blockRho Lb / 4 :=
  min_le_left _ _

theorem blockEta_lt_rho {m Lb : ℝ} (hLb : 0 < Lb) :
    blockEta m Lb < blockRho Lb := by
  have := blockRho_pos hLb
  have := blockEta_le_rho_div_four m Lb
  linarith

theorem blockEta_le_quarter {m Lb : ℝ} : blockEta m Lb ≤ 1 / 4 := by
  have := blockRho_le_one Lb
  have := blockEta_le_rho_div_four m Lb
  linarith

theorem Lb_mul_blockEta_mul_blockL0_le {m Lb : ℝ} (hm : 0 < m) (hLb : 0 < Lb) :
    Lb * blockEta m Lb * blockL0 m ≤ 1 / 8 := by
  have hL0 := blockL0_pos hm
  have hη : blockEta m Lb ≤ 1 / (8 * Lb * blockL0 m) := min_le_right _ _
  have h8 : 0 < 8 * Lb * blockL0 m := by positivity
  calc Lb * blockEta m Lb * blockL0 m = (blockEta m Lb) * (Lb * blockL0 m) := by ring
    _ ≤ 1 / (8 * Lb * blockL0 m) * (Lb * blockL0 m) :=
        mul_le_mul_of_nonneg_right hη (by positivity)
    _ = 1 / 8 := by field_simp

theorem sixteen_Lb_mul_blockRho_pow_three_le {Lb : ℝ} (hLb : 0 < Lb) :
    16 * Lb * blockRho Lb ^ 3 ≤ 1 / 8 := by
  have h := blockRho_pow_three_le hLb
  calc 16 * Lb * blockRho Lb ^ 3 ≤ 16 * Lb * (1 / (128 * Lb)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 1 / 8 := by field_simp; norm_num

/-- Proposition 3.9, (3.15), (3.16): positivity and the
smallness inequalities of the source block constants. -/
theorem block_parameters (Cstar h q0 m Lb : ℝ)
    (hC : 0 < Cstar) (hh : 0 < h) (hq : 0 < q0) (hm : 0 < m) (hmLb : m ≤ Lb) :
    0 < blockRho Lb ∧ blockRho Lb ≤ 1 ∧
    0 < blockEta m Lb ∧ blockEta m Lb ≤ blockRho Lb / 4 ∧
    blockEta m Lb < blockRho Lb ∧ blockEta m Lb ≤ 1 / 4 ∧
    0 < blockTime m Lb ∧ 0 < blockOuter Lb ∧ 0 < blockMass Cstar m Lb ∧
    Lb * blockEta m Lb * blockL0 m ≤ 1 / 8 ∧ 16 * Lb * blockRho Lb ^ 3 ≤ 1 / 8 ∧
    Lb * blockEta m Lb * blockL0 m + 16 * Lb * blockRho Lb ^ 3 ≤ 1 / 4 ∧
    0 < (3 / 4) * blockMass Cstar m Lb * h * q0 := by
  have hLb : 0 < Lb := hm.trans_le hmLb
  have hρ := blockRho_pos hLb
  have hmass : 0 < blockMass Cstar m Lb := Real.exp_pos _
  have h1 := Lb_mul_blockEta_mul_blockL0_le hm hLb
  have h2 := sixteen_Lb_mul_blockRho_pow_three_le hLb
  refine ⟨hρ, blockRho_le_one Lb, blockEta_pos hm hLb, blockEta_le_rho_div_four m Lb,
    blockEta_lt_rho hLb, blockEta_le_quarter, ?_, ?_, hmass, h1, h2, by linarith, ?_⟩
  · unfold blockTime; have := blockL0_pos hm; positivity
  · unfold blockOuter; positivity
  · positivity

end HypoellipticAleksandrov.KineticAleksandrov.Decay
