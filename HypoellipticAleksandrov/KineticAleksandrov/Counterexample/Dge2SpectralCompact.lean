module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2Spectral
public import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Positivity

/-!
# Compactness choices for the Appendix C spectral weights

These are elementary compactness lemmas. Their application to the actual cutoff
Hessian must establish all sign hypotheses from its derivatives.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- A single finite negative weight makes the trace numerator positive on a compact set. -/
theorem exists_spectral_weight_on_compact {X : Type*} [TopologicalSpace X]
    (K : Set X) (hK : IsCompact K) (b m : X → ℝ)
    (hb : ContinuousOn b K) (hm : ContinuousOn m K)
    (hm0 : ∀ x ∈ K, 0 ≤ m x) (hzero : ∀ x ∈ K, m x = 0 → 0 < b x) :
    ∃ cminus : ℝ, 1 ≤ cminus ∧ ∀ x ∈ K, 0 < b x + cminus * m x := by
  by_cases hne : K.Nonempty
  · let g := fun x => m x + max 0 (b x)
    have hg : ContinuousOn g K := hm.add (continuousOn_const.sup hb)
    have hgpos : ∀ x ∈ K, 0 < g x := by
      intro x hx
      by_cases hmx : m x = 0
      · have hbx := hzero x hx hmx
        simpa [g, hmx, max_eq_right hbx.le] using hbx
      · exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne (hm0 x hx) (Ne.symm hmx))
          (le_max_left _ _)
    obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne hg
    have hd : 0 < g x₀ := hgpos x₀ hx₀
    obtain ⟨B₀, hB₀⟩ := hK.bddAbove_image hb.abs
    let B := max 0 B₀
    have hB : 0 ≤ B := le_max_left _ _
    have hbound : ∀ x ∈ K, |b x| ≤ B := by
      intro x hx
      exact (hB₀ ⟨x, hx, rfl⟩).trans (le_max_right _ _)
    let cminus := 1 + B / g x₀
    have hc : 1 ≤ cminus := by
      dsimp [cminus]
      exact le_add_of_nonneg_right (div_nonneg hB hd.le)
    have hc0 : 0 < cminus := lt_of_lt_of_le zero_lt_one hc
    have heq : cminus * g x₀ = g x₀ + B := by
      dsimp [cminus]
      field_simp
    refine ⟨cminus, hc, ?_⟩
    intro x hx
    by_cases hbx : 0 < b x
    · exact add_pos_of_pos_of_nonneg hbx (mul_nonneg hc0.le (hm0 x hx))
    · have hmx : g x₀ ≤ m x := by
        have hh := hmin hx
        simpa [g, max_eq_left (le_of_not_gt hbx)] using hh
      have hh : g x₀ + B ≤ cminus * m x := by
        rw [← heq]
        exact mul_le_mul_of_nonneg_left hmx hc0.le
      have hlow : -B ≤ b x := (abs_le.mp (hbound x hx)).1
      linarith
  · refine ⟨1, le_rfl, ?_⟩
    intro x hx
    exact (hne ⟨x, hx⟩).elim

/-- A positive continuous scalar weight on a compact set has joint positive finite bounds. -/
theorem exists_positive_bounds_on_compact {X : Type*} [TopologicalSpace X]
    (K : Set X) (hK : IsCompact K) (w : X → ℝ) (hw : ContinuousOn w K)
    (hpos : ∀ x ∈ K, 0 < w x) :
    ∃ lower upper : ℝ, 0 < lower ∧ lower ≤ upper ∧
      ∀ x ∈ K, lower ≤ w x ∧ w x ≤ upper := by
  by_cases hne : K.Nonempty
  · obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn hne hw
    obtain ⟨b, hb, hmax⟩ := hK.exists_isMaxOn hne hw
    refine ⟨w a, w b, hpos a ha, hmin hb, ?_⟩
    intro x hx
    exact ⟨hmin hx, hmax hx⟩
  · refine ⟨1, 1, zero_lt_one, le_rfl, ?_⟩
    intro x hx
    exact (hne ⟨x, hx⟩).elim

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
