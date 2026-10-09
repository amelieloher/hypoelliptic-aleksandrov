module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningValues
import Mathlib.Tactic.GCongr

/-! # Compact bounds on all flattened derivative representatives -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Set MeasureTheory

/-- The flattened explicit jets are locally bounded, also on compact sets containing the origin. -/
theorem flatProfile_jets_compact_bound_of_profile {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    (K : Set (XV d)) (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ q ∈ K,
      ‖flatProfilePositionJet h r q‖ ≤ M ∧ ‖flatProfileVelocityJet h r q‖ ≤ M ∧
        ∀ i k, |flatProfileHessian h r q i k| ≤ M := by
  have hH := (selectedProfile_spec h).2.2.2.2.2.2.1
  have hzero := (selectedProfile_spec h).2.2.2.2.2.2.2.1
  have hbounds := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  let L := K ∩ {q | Real.rpow r alpha ≤ profileFunction h q}
  have hL : IsCompact L := hK.inter_right (isClosed_le continuous_const hH)
  have hz : (0 : XV d) ∉ L := by
    intro hmem
    have hp := hmem.2
    change Real.rpow r alpha ≤ profileFunction h 0 at hp
    rw [hzero] at hp
    exact (Real.rpow_pos_of_pos hr alpha).not_ge hp
  obtain ⟨M₀, hM₀⟩ := hbounds L hL hz
  let M := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  obtain ⟨P, hP, hPbound⟩ := flatteningPsi_deriv2_bound
  let D := Real.rpow r (-alpha) * P
  have hD : 0 ≤ D := mul_nonneg (Real.rpow_pos_of_pos hr (-alpha)).le hP.le
  refine ⟨M + D * M ^ 2, by positivity, ?_⟩
  intro q hq
  have hMB : M ≤ M + D * M ^ 2 := le_add_of_nonneg_right (by positivity)
  by_cases hl : Real.rpow r alpha ≤ profileFunction h q
  · have hb := hM₀ q ⟨hq, hl⟩
    have hmx : ‖profilePositionJet h q‖ ≤ M := hb.1.trans (le_max_left _ _)
    have hmv : ‖profileVelocityJet h q‖ ≤ M := hb.2.1.trans (le_max_left _ _)
    have hmh (i k : Fin d) : |profileHessian h q i k| ≤ M :=
      (hb.2.2 i k).trans (le_max_left _ _)
    let s := profileFunction h q / Real.rpow r alpha
    have hs : |deriv flatteningPsi s| ≤ 1 := by
      rw [abs_of_nonneg (flatteningPsi_deriv_bounds s).1]
      exact (flatteningPsi_deriv_bounds s).2
    have hjet (g : PDE.Vec d) (hg : ‖g‖ ≤ M) : ‖-deriv flatteningPsi s • g‖ ≤ M := by
      rw [norm_smul, Real.norm_eq_abs, abs_neg]
      calc
        _ ≤ 1 * M := mul_le_mul hs hg (norm_nonneg _) (by norm_num)
        _ = M := one_mul _
    refine ⟨(hjet _ hmx).trans hMB, (hjet _ hmv).trans hMB, ?_⟩
    intro i k
    have hvi : |profileVelocityJet h q i| ≤ M := by
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm _ i).trans hmv
    have hvk : |profileVelocityJet h q k| ≤ M := by
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm _ k).trans hmv
    have ht : |deriv (deriv flatteningPsi) s| ≤ P := by
      rw [abs_of_nonneg (flatteningPsi_deriv2_nonneg s)]
      exact hPbound s
    unfold flatProfileHessian
    calc
      _ ≤ |(-deriv flatteningPsi s) * profileHessian h q i k| +
          |Real.rpow r (-alpha) * deriv (deriv flatteningPsi) s *
            profileVelocityJet h q i * profileVelocityJet h q k| := abs_sub _ _
      _ ≤ M + D * M ^ 2 := by
        rw [abs_mul, abs_neg, abs_mul, abs_mul, abs_mul]
        simp only [Real.rpow_eq_pow]
        rw [abs_of_pos (Real.rpow_pos_of_pos hr (-alpha))]
        have hfirst : |deriv flatteningPsi s| * |profileHessian h q i k| ≤ M := by
          calc
            _ ≤ 1 * M := mul_le_mul hs (hmh i k) (abs_nonneg _) (by norm_num)
            _ = M := one_mul _
        have hsecond : Real.rpow r (-alpha) * |deriv (deriv flatteningPsi) s| *
            |profileVelocityJet h q i| * |profileVelocityJet h q k| ≤ D * M ^ 2 := by
          dsimp [D]
          rw [pow_two]
          have hpow : 0 ≤ r ^ (-alpha) := (Real.rpow_pos_of_pos hr (-alpha)).le
          calc
            _ ≤ r ^ (-alpha) * P * M * M := by gcongr
            _ = _ := by ring
        exact add_le_add hfirst hsecond
  · have hs : profileFunction h q / Real.rpow r alpha < 1 :=
      (div_lt_one (Real.rpow_pos_of_pos hr alpha)).mpr (lt_of_not_ge hl)
    have hfirst : deriv flatteningPsi (profileFunction h q / Real.rpow r alpha) = 0 := by
      rw [deriv_flatteningPsi]
      exact Real.smoothTransition.zero_of_nonpos (by linarith)
    have hsecond := flatteningPsi_deriv2_eq_zero_of_lt _ hs
    have hx : flatProfilePositionJet h r q = 0 := by
      ext i
      unfold flatProfilePositionJet
      rw [hfirst]
      simp
    have hv : flatProfileVelocityJet h r q = 0 := by
      ext i
      unfold flatProfileVelocityJet
      rw [hfirst]
      simp
    have hh (i k : Fin d) : flatProfileHessian h r q i k = 0 := by
      unfold flatProfileHessian
      rw [hfirst, hsecond]
      ring
    simp only [hx, hv, hh, norm_zero, abs_zero]
    exact ⟨hM.trans hMB, hM.trans hMB, fun _ _ => hM.trans hMB⟩

/-- Measurable real functions bounded on each compact set are locally integrable. -/
theorem locallyIntegrable_of_compact_bound {d : ℕ} (f : XV d → ℝ) (hf : Measurable f)
    (hb : ∀ K : Set (XV d), IsCompact K →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ q ∈ K, |f q| ≤ M) : LocallyIntegrable f volume := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  obtain ⟨M, hM, hbM⟩ := hb K hK
  have hi : IntegrableOn (fun _ : XV d => M) K volume := integrableOn_const hK.measure_ne_top
  change Integrable (fun _ : XV d => M) (volume.restrict K) at hi
  change Integrable f (volume.restrict K)
  apply hi.mono hf.aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem hK.measurableSet] with q hq
  simpa only [Real.norm_eq_abs, abs_of_nonneg hM] using hbM q hq

/-- All selected flattened derivative components are locally integrable. -/
theorem flatProfile_jets_locallyIntegrable_of_profile {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r) :
    (∀ i, LocallyIntegrable (fun q => flatProfilePositionJet h r q i) volume) ∧
    (∀ i, LocallyIntegrable (fun q => flatProfileVelocityJet h r q i) volume) ∧
    (∀ i k, LocallyIntegrable (fun q => flatProfileHessian h r q i k) volume) := by
  obtain ⟨hmx, hmv, hmh⟩ := measurable_flatProfile_jets h r
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply locallyIntegrable_of_compact_bound (fun q => flatProfilePositionJet h r q i)
      ((measurable_pi_apply i).comp hmx)
    intro K hK
    obtain ⟨M, hM, hb⟩ := flatProfile_jets_compact_bound_of_profile h r hr K hK
    refine ⟨M, hM, ?_⟩
    intro q hq
    simpa only [Real.norm_eq_abs] using
      (norm_le_pi_norm (flatProfilePositionJet h r q) i).trans (hb q hq).1
  · intro i
    apply locallyIntegrable_of_compact_bound (fun q => flatProfileVelocityJet h r q i)
      ((measurable_pi_apply i).comp hmv)
    intro K hK
    obtain ⟨M, hM, hb⟩ := flatProfile_jets_compact_bound_of_profile h r hr K hK
    refine ⟨M, hM, ?_⟩
    intro q hq
    simpa only [Real.norm_eq_abs] using
      (norm_le_pi_norm (flatProfileVelocityJet h r q) i).trans (hb q hq).2.1
  · intro i k
    apply locallyIntegrable_of_compact_bound (fun q => flatProfileHessian h r q i k) (hmh i k)
    intro K hK
    obtain ⟨M, hM, hb⟩ := flatProfile_jets_compact_bound_of_profile h r hr K hK
    exact ⟨M, hM, fun q hq => (hb q hq).2.2 i k⟩

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
