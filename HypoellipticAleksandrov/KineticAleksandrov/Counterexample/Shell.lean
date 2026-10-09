module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Profile
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ShellGeometry
import Mathlib.Tactic.Linarith

/-! # Shell volume with the exact homogeneous dimension `4d` -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Set

/-- The closed shell that contains the stationary source. -/
def profileShell {d : ℕ} (H : XV d → ℝ) (alpha r : ℝ) : Set (XV d) :=
  {q | Real.rpow r alpha ≤ H q ∧ H q ≤ 2 * Real.rpow r alpha}

/-- Comparison with a positive gauge power traps any fixed upper profile sublevel. -/
theorem profile_sublevel_subset_rho {d : ℕ} (H : XV d → ℝ) (alpha c M : ℝ)
    (ha : 0 < alpha) (hc : 0 < c) (hM : 0 < M)
    (hlo : ∀ q, c * Real.rpow (rho q) alpha ≤ H q) :
    {q | H q ≤ M} ⊆ {q | rho q ≤ Real.rpow (M / c) alpha⁻¹} := by
  intro q hq
  have hb : Real.rpow (rho q) alpha ≤ M / c :=
    (le_div_iff₀ hc).2 (by simpa only [mul_comm] using (hlo q).trans hq)
  have hbase : 0 < M / c := div_pos hM hc
  have hroot := Real.rpow_pos_of_pos hbase alpha⁻¹
  apply (Real.rpow_le_rpow_iff (rho_nonneg q) hroot.le ha).mp
  simp only [Real.rpow_eq_pow] at hb ⊢
  rw [Real.rpow_inv_rpow hbase.le ha.ne']
  exact hb

/-- A continuous comparable profile has finite-volume upper sublevels. -/
theorem profile_sublevel_volume_lt_top {d : ℕ} (H : XV d → ℝ) (alpha c M : ℝ)
    (ha : 0 < alpha) (hc : 0 < c) (hM : 0 < M)
    (hlo : ∀ q, c * Real.rpow (rho q) alpha ≤ H q) :
    volume {q | H q ≤ M} < ⊤ := by
  exact lt_of_le_of_lt
    (measure_mono (profile_sublevel_subset_rho H alpha c M ha hc hM hlo))
    (isCompact_rho_sublevel d (Real.rpow (M / c) alpha⁻¹)).measure_lt_top

/-- Homogeneity identifies the radius-r shell as the inverse-dilation preimage. -/
theorem profileShell_eq_preimage {d : ℕ} (H : XV d → ℝ) (alpha r : ℝ)
    (hr : 0 < r)
    (hhom : ∀ s : ℝ, 0 < s → ∀ q,
      H (dilate s q) = Real.rpow s alpha * H q) :
    profileShell H alpha r = dilate r⁻¹ ⁻¹' {q | 1 ≤ H q ∧ H q ≤ 2} := by
  ext q
  simp only [profileShell, mem_ofPred_eq, mem_preimage]
  rw [hhom r⁻¹ (inv_pos.mpr hr) q]
  simp only [Real.rpow_eq_pow]
  rw [Real.inv_rpow hr.le, inv_mul_eq_div]
  have hp := Real.rpow_pos_of_pos hr alpha
  constructor
  · rintro ⟨hlo, hhi⟩
    exact ⟨(le_div_iff₀ hp).2 (by simpa only [one_mul] using hlo),
      (div_le_iff₀ hp).2 hhi⟩
  · rintro ⟨hlo, hhi⟩
    exact ⟨by simpa only [one_mul] using (le_div_iff₀ hp).1 hlo,
      (div_le_iff₀ hp).1 hhi⟩

/-- The source shell has exactly the expected kinetic dilation factor. -/
theorem profileShell_volume {d : ℕ} (H : XV d → ℝ) (alpha r : ℝ)
    (hH : Continuous H) (hr : 0 < r)
    (hhom : ∀ s : ℝ, 0 < s → ∀ q,
      H (dilate s q) = Real.rpow s alpha * H q) :
    volume (profileShell H alpha r) =
      ENNReal.ofReal (r ^ (4 * d)) * volume {q | 1 ≤ H q ∧ H q ≤ 2} := by
  have hm : MeasurableSet {q : XV d | 1 ≤ H q ∧ H q ≤ 2} :=
    ((isClosed_le continuous_const hH).inter (isClosed_le hH continuous_const)).measurableSet
  rw [profileShell_eq_preimage H alpha r hr hhom]
  rw [← Measure.map_apply (by unfold dilate; fun_prop) hm,
    map_dilate_volume d r⁻¹ (inv_pos.mpr hr), inv_inv,
    Measure.smul_apply, smul_eq_mul]

/-- A comparable homogeneous profile gives a radius-uniform shell-volume constant. -/
theorem shell_volume_bound {d : ℕ} (H : XV d → ℝ) (alpha c : ℝ)
    (ha : 0 < alpha) (hc : 0 < c) (hH : Continuous H)
    (hlo : ∀ q, c * Real.rpow (rho q) alpha ≤ H q)
    (hhom : ∀ s : ℝ, 0 < s → ∀ q,
      H (dilate s q) = Real.rpow s alpha * H q) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r →
      volume (profileShell H alpha r) ≤ ENNReal.ofReal (C * r ^ (4 * d)) := by
  let m := volume {q : XV d | 1 ≤ H q ∧ H q ≤ 2}
  have hm : m < ⊤ := lt_of_le_of_lt
    (measure_mono (show {q : XV d | 1 ≤ H q ∧ H q ≤ 2} ⊆ {q | H q ≤ 2} from
      fun _ hq => hq.2))
    (profile_sublevel_volume_lt_top H alpha c 2 ha hc (by norm_num) hlo)
  refine ⟨m.toReal + 1, by positivity, ?_⟩
  intro r hr
  rw [profileShell_volume H alpha r hH hr hhom,
    ENNReal.ofReal_mul (by positivity : 0 ≤ m.toReal + 1), mul_comm]
  exact mul_le_mul_left
    ((le_of_eq (ENNReal.ofReal_toReal hm.ne).symm).trans
      (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right zero_le_one))) _

/-- Shell-volume construction conditional only on the shared profile theorem surface. -/
theorem shell_volume_bound_of_profile (d : ℕ) (alpha : ℝ) (ha : 0 < alpha)
    (hprofile : CounterProfileStatement d alpha) :
    ∃ C r₀ : ℝ, 0 < C ∧ 0 < r₀ ∧
      ∀ r : ℝ, 0 < r → r < r₀ →
        volume (profileShell (profileFunction hprofile) alpha r) ≤
          ENNReal.ofReal (C * r ^ (4 * d)) := by
  obtain ⟨_, _, hc, _, _, _, hH, _, hhom, hcomp, _⟩ := selectedProfile_spec hprofile
  obtain ⟨C, hC, hb⟩ := shell_volume_bound (profileFunction hprofile) alpha
    (profileLowerComparison hprofile) ha hc hH
    (fun q => (hcomp q).1) hhom
  exact ⟨C, 1, hC, zero_lt_one, fun r hr _ => hb r hr⟩

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
