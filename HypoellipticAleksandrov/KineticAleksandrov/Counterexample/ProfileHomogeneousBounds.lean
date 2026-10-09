module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileBounds
import Mathlib.Tactic.Linarith

/-! # Bounds for homogeneous derivative components -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Set

/-- Compact bounds on the unit gauge surface give the global homogeneous power bound. -/
theorem homogeneous_component_bound {d : ℕ} (f : XV d → ℝ) (beta : ℝ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ q, f (dilate r q) = Real.rpow r beta * f q)
    (hbound : ∀ K : Set (XV d), IsCompact K → 0 ∉ K →
      ∃ M : ℝ, ∀ q ∈ K, |f q| ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : XV d, q ≠ 0 → |f q| ≤ C * Real.rpow (rho q) beta := by
  let K : Set (XV d) := {q | rho q = 1}
  have hK : IsCompact K := (isCompact_rho_sublevel d 1).of_isClosed_subset
    (isClosed_eq (continuous_rho d) continuous_const) (fun q hq => hq.le)
  have hzero : (0 : XV d) ∉ K := by simp [K]
  obtain ⟨M, hM⟩ := hbound K hK hzero
  refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro q hq
  have hp : 0 < rho q := lt_of_le_of_ne (rho_nonneg q)
    (Ne.symm (mt (rho_eq_zero_iff q).mp hq))
  have hn : dilate (rho q)⁻¹ q ∈ K := by
    change rho (dilate (rho q)⁻¹ q) = 1
    rw [rho_dilate _ (inv_pos.mpr hp), inv_mul_cancel₀ hp.ne']
  have h := (hM _ hn).trans (le_max_left M 1)
  rw [hhom _ (inv_pos.mpr hp), abs_mul] at h
  simp only [Real.rpow_eq_pow] at h ⊢
  rw [abs_of_pos (Real.rpow_pos_of_pos (inv_pos.mpr hp) beta)] at h
  have hi : Real.rpow (rho q)⁻¹ beta * Real.rpow (rho q) beta = 1 := by
    simp only [Real.rpow_eq_pow]
    rw [Real.inv_rpow hp.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hp beta).ne']
  have hh := mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hp.le beta)
  calc
    |f q| = (Real.rpow (rho q)⁻¹ beta * |f q|) * Real.rpow (rho q) beta := by
      rw [mul_right_comm, hi, one_mul]
    _ ≤ max M 1 * Real.rpow (rho q) beta := hh

/-- Homogeneous components of degree above minus four are locally integrable. -/
theorem homogeneous_component_locallyIntegrable (d : ℕ) (hd : 1 ≤ d)
    (f : XV d → ℝ) (hf : Measurable f) (beta : ℝ) (hb : -4 < beta) (hb0 : beta ≤ 0)
    (hhom : ∀ r : ℝ, 0 < r → ∀ q, f (dilate r q) = Real.rpow r beta * f q)
    (hbound : ∀ K : Set (XV d), IsCompact K → 0 ∉ K →
      ∃ M : ℝ, ∀ q ∈ K, |f q| ≤ M) : LocallyIntegrable f volume := by
  obtain ⟨C, hC, h⟩ := homogeneous_component_bound f beta hhom hbound
  apply locallyIntegrable_of_rho_bound d hd beta hb hb0 f hf C hC.le
  filter_upwards [coordinates_ne_zero_ae d hd] with q hq
  exact h q (fun hz => hq.1 (congrArg Prod.fst hz))

/-- Compact bounds on the unit gauge surface give the global homogeneous power bound. -/
theorem homogeneous_component_bound_off_origin {d : ℕ} (f : XV d → ℝ) (beta : ℝ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ q, q ≠ 0 → f (dilate r q) = Real.rpow r beta * f q)
    (hbound : ∀ K : Set (XV d), IsCompact K → 0 ∉ K →
      ∃ M : ℝ, ∀ q ∈ K, |f q| ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : XV d, q ≠ 0 → |f q| ≤ C * Real.rpow (rho q) beta := by
  let K : Set (XV d) := {q | rho q = 1}
  have hK : IsCompact K := (isCompact_rho_sublevel d 1).of_isClosed_subset
    (isClosed_eq (continuous_rho d) continuous_const) (fun q hq => hq.le)
  have hzero : (0 : XV d) ∉ K := by simp [K]
  obtain ⟨M, hM⟩ := hbound K hK hzero
  refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro q hq
  have hp : 0 < rho q := lt_of_le_of_ne (rho_nonneg q)
    (Ne.symm (mt (rho_eq_zero_iff q).mp hq))
  have hn : dilate (rho q)⁻¹ q ∈ K := by
    change rho (dilate (rho q)⁻¹ q) = 1
    rw [rho_dilate _ (inv_pos.mpr hp), inv_mul_cancel₀ hp.ne']
  have h := (hM _ hn).trans (le_max_left M 1)
  rw [hhom _ (inv_pos.mpr hp) q hq, abs_mul] at h
  simp only [Real.rpow_eq_pow] at h ⊢
  rw [abs_of_pos (Real.rpow_pos_of_pos (inv_pos.mpr hp) beta)] at h
  have hi : Real.rpow (rho q)⁻¹ beta * Real.rpow (rho q) beta = 1 := by
    simp only [Real.rpow_eq_pow]
    rw [Real.inv_rpow hp.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hp beta).ne']
  have hh := mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hp.le beta)
  calc
    |f q| = (Real.rpow (rho q)⁻¹ beta * |f q|) * Real.rpow (rho q) beta := by
      rw [mul_right_comm, hi, one_mul]
    _ ≤ max M 1 * Real.rpow (rho q) beta := hh

/-- Homogeneous components of degree above minus four are locally integrable. -/
theorem homogeneous_component_locallyIntegrable_off_origin (d : ℕ) (hd : 1 ≤ d)
    (f : XV d → ℝ) (hf : Measurable f) (beta : ℝ) (hb : -4 < beta) (hb0 : beta ≤ 0)
    (hhom : ∀ r : ℝ, 0 < r → ∀ q, q ≠ 0 → f (dilate r q) = Real.rpow r beta * f q)
    (hbound : ∀ K : Set (XV d), IsCompact K → 0 ∉ K →
      ∃ M : ℝ, ∀ q ∈ K, |f q| ≤ M) : LocallyIntegrable f volume := by
  obtain ⟨C, hC, h⟩ := homogeneous_component_bound_off_origin f beta hhom hbound
  apply locallyIntegrable_of_rho_bound d hd beta hb hb0 f hf C hC.le
  filter_upwards [coordinates_ne_zero_ae d hd] with q hq
  exact h q (fun hz => hq.1 (congrArg Prod.fst hz))

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
