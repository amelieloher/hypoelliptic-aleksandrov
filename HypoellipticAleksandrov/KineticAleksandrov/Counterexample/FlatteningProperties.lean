module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningValues

/-! # Joint value and plateau properties with one small-scale threshold -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter

/-- One positive threshold gives all the source's literal flattening properties. -/
theorem flatProfile_properties_of_profile {d : ℕ} {alpha : ℝ} (ha : 0 < alpha)
    (h : CounterProfileStatement d alpha) :
    ∃ r0 : ℝ, 0 < r0 ∧ ∀ r : ℝ, 0 < r → r < r0 →
      Continuous (selectedFlatProfile h r) ∧
      (∀ q, profileFunction h q ≤ 1 →
        0 ≤ selectedFlatProfile h r q ∧ selectedFlatProfile h r q ≤ 1) ∧
      (∀ q, profileFunction h q = 1 → selectedFlatProfile h r q = 0) ∧
      (selectedFlatProfile h r =ᶠ[nhds 0]
        (fun _ => 1 - flatteningOffset * Real.rpow r alpha)) ∧
      (∀ q, 2 * Real.rpow r alpha ≤ profileFunction h q →
        selectedFlatProfile h r q = 1 - profileFunction h q) ∧
      selectedFlatProfile h r 0 = 1 - flatteningOffset * Real.rpow r alpha := by
  let r0 : ℝ := (1 / 2 : ℝ) ^ alpha⁻¹
  have hr0 : 0 < r0 := Real.rpow_pos_of_pos (by norm_num) _
  have hpower : Real.rpow r0 alpha = 1 / 2 := by
    change ((1 / 2 : ℝ) ^ alpha⁻¹) ^ alpha = 1 / 2
    rw [← Real.rpow_mul (by norm_num), inv_mul_cancel₀ ha.ne', Real.rpow_one]
  refine ⟨r0, hr0, ?_⟩
  intro r hr hrr0
  have hsmall : 2 * Real.rpow r alpha ≤ 1 := by
    have hh := Real.rpow_le_rpow hr.le hrr0.le ha.le
    change Real.rpow r alpha ≤ Real.rpow r0 alpha at hh
    rw [hpower] at hh
    linarith
  refine ⟨continuous_selectedFlatProfile h r, ?_, ?_,
    selectedFlatProfile_plateau_of_profile h r hr, ?_, ?_⟩
  · intro q hq
    exact ⟨selectedFlatProfile_nonneg_of_profile h r hr hsmall q hq,
      selectedFlatProfile_le_one_of_profile h r hr q⟩
  · exact selectedFlatProfile_boundary_of_profile h r hr hsmall
  · intro q hq
    exact flatProfile_eq_one_sub _ _ _ hr q hq
  · have hz := (selectedProfile_spec h).2.2.2.2.2.2.2.1
    exact flatProfile_eq_constant _ _ _ hr 0 (by rw [hz]; exact (Real.rpow_pos_of_pos hr alpha).le)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
