module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileHolds
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith

/-! # Positive flattening scales and vanishing stationary source norms -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter MeasureTheory

/-- One scale threshold ensures both the height margin and the fixed zero collar. -/
theorem construction_small_scale_threshold (alpha : ℝ) (ha : 0 < alpha) :
    ∃ r0 : ℝ, 0 < r0 ∧ ∀ r : ℝ, 0 < r → r < r0 →
      flatteningOffset * Real.rpow r alpha ≤ 1 / 4 ∧
      2 * Real.rpow r alpha ≤ 7 / 8 := by
  have hc : 0 < flatteningOffset := zero_lt_one.trans flatteningOffset_bounds.1
  let a : ℝ := 1 / (4 * flatteningOffset)
  have hap : 0 < a := div_pos zero_lt_one (mul_pos (by norm_num) hc)
  let r0 : ℝ := Real.rpow a alpha⁻¹
  have hr0 : 0 < r0 := Real.rpow_pos_of_pos hap _
  have hpower : Real.rpow r0 alpha = a := Real.rpow_inv_rpow hap.le ha.ne'
  refine ⟨r0, hr0, ?_⟩
  intro r hr hrr
  have hp := Real.rpow_le_rpow hr.le hrr.le ha.le
  change Real.rpow r alpha ≤ Real.rpow r0 alpha at hp
  rw [hpower] at hp
  have hca : flatteningOffset * a = 1 / 4 := by dsimp [a]; field_simp
  have hb : flatteningOffset * Real.rpow r alpha ≤ 1 / 4 := by
    calc
      _ ≤ flatteningOffset * a := mul_le_mul_of_nonneg_left hp hc.le
      _ = _ := hca
  have hpow := (Real.rpow_pos_of_pos hr alpha).le
  have hco := mul_le_mul_of_nonneg_right flatteningOffset_bounds.1.le hpow
  constructor
  · exact hb
  · simp only [Real.rpow_eq_pow] at hb hpow hco ⊢
    nlinarith

/-- Any positive scales tending to zero give the exact stationary source norm decay. -/
theorem construction_flat_source_decay_of_profile {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (p : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hp : 1 ≤ p)
    (hexponent : 0 < alpha - 2 + 4 * (d : ℝ) / p)
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) (hlim : Tendsto r atTop (nhds 0)) :
    Tendsto (fun j => eLpNorm
      (flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha (r j))
      (ENNReal.ofReal p) (volume.restrict {q | profileFunction h q < 1}))
      atTop (nhds 0) := by
  obtain ⟨C, r0, hC, hr0, hb⟩ := flat_source_eLpNorm_le_of_profile d alpha p ha ha1 hp h
  have he : ∀ᶠ j in atTop, r j < r0 := hlim.eventually (gt_mem_nhds hr0)
  have hpow := (Real.continuous_rpow_const hexponent.le).tendsto (0 : ℝ) |>.comp hlim
  have hpow0 : Tendsto (fun j => Real.rpow (r j) (alpha - 2 + 4 * (d : ℝ) / p))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.rpow_eq_pow, Real.zero_rpow hexponent.ne'] using hpow
  have hup : Tendsto (fun j => ENNReal.ofReal
      (C * Real.rpow (r j) (alpha - 2 + 4 * (d : ℝ) / p))) atTop (nhds 0) := by
    simpa only [Function.comp_def, mul_zero, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (hpow0.const_mul C)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
  · exact Eventually.of_forall (fun _ => bot_le)
  · filter_upwards [he] with j hj
    exact hb (r j) (hr j) hj

/-- A concrete positive sequence stays strictly below a prescribed positive threshold. -/
theorem construction_exists_scales (r0 : ℝ) (hr0 : 0 < r0) :
    ∃ r : ℕ → ℝ, (∀ j, 0 < r j ∧ r j < r0) ∧ Tendsto r atTop (nhds 0) := by
  let r : ℕ → ℝ := fun j => r0 * (1 / ((j : ℝ) + 2))
  refine ⟨r, ?_, ?_⟩
  · intro j
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
    constructor
    · exact mul_pos hr0 (div_pos zero_lt_one (by linarith))
    · change r0 * (1 / ((j : ℝ) + 2)) < r0
      have hi : 1 / ((j : ℝ) + 2) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
      simpa only [mul_one] using mul_lt_mul_of_pos_left hi hr0
  · have hh := (tendsto_add_atTop_iff_nat 1).2
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hh' : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 2)) atTop (nhds 0) := by
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hh
    simpa only [mul_zero] using hh'.const_mul r0

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
