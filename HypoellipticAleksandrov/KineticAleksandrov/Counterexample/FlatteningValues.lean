module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningProfile
import Mathlib.Tactic.Linarith

/-! # Values and plateau of the selected flattened profile -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter

/-- The fixed flattening primitive grows at most linearly on the whole real line. -/
theorem abs_flatteningPsi_le (s : ℝ) : |flatteningPsi s| ≤ |s| := by
  have hb (t : ℝ) : ‖deriv flatteningPsi t‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (flatteningPsi_deriv_bounds t).1]
    exact (flatteningPsi_deriv_bounds t).2
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun t (_ : t ∈ (Set.univ : Set ℝ)) =>
      (contDiff_flatteningPsi.differentiable (by simp)) t)
    (fun t _ => hb t) convex_univ (Set.mem_univ (0 : ℝ)) (Set.mem_univ s)
  simpa only [flatteningPsi_eq_zero 0 (by norm_num), sub_zero, one_mul, Real.norm_eq_abs] using h

/-- A scalar bound on the unflattened value gives a uniform bound on its literal flattening. -/
theorem abs_flatProfile_le {d : ℕ} (H : XV d → ℝ) (alpha r : ℝ) (hr : 0 < r)
    (q : XV d) :
    |flatProfile H flatteningPsi flatteningOffset alpha r q| ≤
      1 + |flatteningOffset| * Real.rpow r alpha + |H q| := by
  let a := Real.rpow r alpha
  have hp : 0 < a := Real.rpow_pos_of_pos hr alpha
  have hb := mul_le_mul_of_nonneg_left (abs_flatteningPsi_le (H q / a)) hp.le
  have he : a * |H q / a| = |H q| := by
    rw [abs_div, abs_of_pos hp, mul_div_cancel₀ _ hp.ne']
  rw [he] at hb
  unfold flatProfile
  calc
    _ ≤ |1 - flatteningOffset * a| + |a * flatteningPsi (H q / a)| := abs_sub _ _
    _ ≤ 1 + |flatteningOffset| * a + |H q| := by
      have hfirst := abs_sub (1 : ℝ) (flatteningOffset * a)
      rw [abs_one, abs_mul, abs_of_pos hp] at hfirst
      rw [abs_mul, abs_of_pos hp]
      exact add_le_add hfirst hb

/-- The literal flattening never exceeds one. -/
theorem selectedFlatProfile_le_one_of_profile {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r) (q : XV d) :
    selectedFlatProfile h r q ≤ 1 := by
  have hpow := (Real.rpow_pos_of_pos hr alpha).le
  have hoff := flatteningOffset_bounds.1.le
  have hpsi := flatteningPsi_nonneg (profileFunction h q / Real.rpow r alpha)
  unfold selectedFlatProfile flatProfile
  simp only [Real.rpow_eq_pow] at hpsi ⊢
  linarith [mul_nonneg (le_trans zero_le_one hoff) hpow, mul_nonneg hpow hpsi]

/-- The literal flattening is nonnegative in its unit sublevel for sufficiently small scales. -/
theorem selectedFlatProfile_nonneg_of_profile {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    (hsmall : 2 * Real.rpow r alpha ≤ 1) (q : XV d) (hq : profileFunction h q ≤ 1) :
    0 ≤ selectedFlatProfile h r q := by
  have hp := Real.rpow_pos_of_pos hr alpha
  by_cases hhigh : 2 * Real.rpow r alpha ≤ profileFunction h q
  · rw [selectedFlatProfile, flatProfile_eq_one_sub _ _ _ hr q hhigh]
    linarith
  · have hlow : profileFunction h q / Real.rpow r alpha ≤ 2 := by
      exact (div_le_iff₀ hp).mpr (le_of_lt (lt_of_not_ge hhigh))
    have hpsi := monotone_flatteningPsi hlow
    have hm := mul_le_mul_of_nonneg_left hpsi hp.le
    unfold selectedFlatProfile flatProfile flatteningOffset
    simp only [Real.rpow_eq_pow] at hsmall hm ⊢
    nlinarith

/-- The selected flattening vanishes on the unit profile level. -/
theorem selectedFlatProfile_boundary_of_profile {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    (hsmall : 2 * Real.rpow r alpha ≤ 1) (q : XV d) (hq : profileFunction h q = 1) :
    selectedFlatProfile h r q = 0 := by
  rw [selectedFlatProfile, flatProfile_eq_one_sub _ _ _ hr q (hq ▸ hsmall), hq]
  ring

/-- The origin belongs to a constant plateau of the selected literal flattening. -/
theorem selectedFlatProfile_plateau_of_profile {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r) :
    selectedFlatProfile h r =ᶠ[nhds 0]
      (fun _ => 1 - flatteningOffset * Real.rpow r alpha) := by
  have hH := (selectedProfile_spec h).2.2.2.2.2.2.1
  have hzero := (selectedProfile_spec h).2.2.2.2.2.2.2.1
  have hnear : ∀ᶠ q in nhds (0 : XV d), profileFunction h q < Real.rpow r alpha :=
    hH.continuousAt.eventually (gt_mem_nhds (hzero ▸ Real.rpow_pos_of_pos hr alpha))
  filter_upwards [hnear] with q hq
  exact flatProfile_eq_constant _ _ _ hr q hq.le

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
