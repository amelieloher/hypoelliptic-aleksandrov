module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.SourceNotation
import Mathlib.Algebra.Order.Floor.Semiring

/-! # The exact floor and exponential estimates in the source decay iteration -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay

/-- The floor estimate includes the zero-block case without a lower bound on duration. -/
theorem decay_floor_power {a x : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    a ^ Nat.floor x ≤ a ^ (x - 1) := by
  rw [← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_ge ha ha1
  have hf := Nat.lt_floor_add_one x
  linarith only [hf]

/-- The source real power is exactly its exponential with prefactor a inverse. -/
theorem decay_power_exponential {a L : ℝ} (ha : 0 < a) (hL : 0 < L) (t N : ℝ) :
    a ^ (t * N / L - 1) = a⁻¹ * Real.exp (-(-Real.log a / L) * t * N) := by
  rw [Real.rpow_sub ha, Real.rpow_one, div_eq_mul_inv, mul_comm _ a⁻¹,
    Real.rpow_def_of_pos ha]
  congr 2
  field_simp

/-- Block constants produce a prefactor at least one and a positive decay rate. -/
theorem decay_constants {δ L : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hL : 0 < L) :
    1 ≤ (1 - δ)⁻¹ ∧ 0 < -Real.log (1 - δ) / L := by
  have ha : 0 < 1 - δ := sub_pos.mpr hδ1
  constructor
  · exact (one_le_inv₀ ha).mpr (by linarith only [hδ])
  · exact div_pos (neg_pos.mpr (Real.log_neg ha (by linarith only [hδ]))) hL

end HypoellipticAleksandrov.KineticAleksandrov.Decay
