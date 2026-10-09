module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Profile
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-! # Regularity of the higher-dimensional profile witnesses -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Set Filter

/-- The total position derivative selectors are measurable, even at singular points. -/
theorem measurable_dx {d : ℕ} (H : XV d → ℝ) : Measurable (dx H) := by
  apply Measurable.of_eval
  intro i
  exact measurable_fderiv_apply_const ℝ H (Pi.single i 1, 0)

/-- The total velocity derivative selectors are measurable, even at singular points. -/
theorem measurable_dv {d : ℕ} (H : XV d → ℝ) : Measurable (dv H) := by
  apply Measurable.of_eval
  intro i
  exact measurable_fderiv_apply_const ℝ H (0, Pi.single i 1)

/-- The total second velocity derivative selectors are entrywise measurable. -/
theorem measurable_dvv {d : ℕ} (H : XV d → ℝ) (i k : Fin d) :
    Measurable (fun q => dvv H q i k) :=
  measurable_fderiv_apply_const ℝ (fun q => dv H q k) (0, Pi.single i 1)

/-- Smoothness off the origin gives smooth position derivative components there. -/
theorem contDiffAt_dx_off_origin {d : ℕ} (H : XV d → ℝ)
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ : Set (XV d)))
    (q : XV d) (hq : q ≠ 0) (i : Fin d) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z => dx H z i) q := by
  have h := hs.contDiffAt (isOpen_compl_singleton.mem_nhds (by simpa using hq))
  exact (h.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffAt_const

/-- Smoothness off the origin gives smooth velocity derivative components there. -/
theorem contDiffAt_dv_off_origin {d : ℕ} (H : XV d → ℝ)
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ : Set (XV d)))
    (q : XV d) (hq : q ≠ 0) (i : Fin d) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z => dv H z i) q := by
  have h := hs.contDiffAt (isOpen_compl_singleton.mem_nhds (by simpa using hq))
  exact (h.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffAt_const

/-- Smoothness off the origin gives smooth second velocity derivative components there. -/
theorem contDiffAt_dvv_off_origin {d : ℕ} (H : XV d → ℝ)
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ : Set (XV d)))
    (q : XV d) (hq : q ≠ 0) (i k : Fin d) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z => dvv H z i k) q := by
  exact ((contDiffAt_dv_off_origin H hs q hq k).fderiv_right
    (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffAt_const

/-- The full first derivative vectors are continuous away from the origin. -/
theorem continuousOn_profile_jets {d : ℕ} (H : XV d → ℝ)
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ : Set (XV d))) :
    ContinuousOn (dx H) ({0}ᶜ : Set (XV d)) ∧
    ContinuousOn (dv H) ({0}ᶜ : Set (XV d)) ∧
    ContinuousOn (dvv H) ({0}ᶜ : Set (XV d)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    apply continuousWithinAt_pi.mpr
    intro i
    exact (contDiffAt_dx_off_origin H hs q (by simpa using hq) i).continuousAt.continuousWithinAt
  · intro q hq
    apply continuousWithinAt_pi.mpr
    intro i
    exact (contDiffAt_dv_off_origin H hs q (by simpa using hq) i).continuousAt.continuousWithinAt
  · intro q hq
    apply continuousWithinAt_pi.mpr
    intro i
    apply continuousWithinAt_pi.mpr
    intro k
    exact (contDiffAt_dvv_off_origin H hs q (by simpa using hq) i k).continuousAt.continuousWithinAt

/-- All classical jet components are bounded on each compact set avoiding the origin. -/
theorem profile_jets_compact_bound {d : ℕ} (H : XV d → ℝ)
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ : Set (XV d)))
    (K : Set (XV d)) (hK : IsCompact K) (hz : 0 ∉ K) :
    ∃ M : ℝ, ∀ q ∈ K,
      ‖dx H q‖ ≤ M ∧ ‖dv H q‖ ≤ M ∧ ∀ i k, |dvv H q i k| ≤ M := by
  have hsub : K ⊆ ({0}ᶜ : Set (XV d)) := by
    intro q hq
    change q ≠ 0
    intro he
    subst q
    exact hz hq
  obtain ⟨Mx, hx⟩ := hK.exists_bound_of_continuousOn
    ((continuousOn_profile_jets H hs).1.mono hsub)
  obtain ⟨Mv, hv⟩ := hK.exists_bound_of_continuousOn
    ((continuousOn_profile_jets H hs).2.1.mono hsub)
  let B : XV d → (Fin d × Fin d → ℝ) := fun q ik => dvv H q ik.1 ik.2
  have hB : ContinuousOn B K := by
    intro q hq
    apply continuousWithinAt_pi.mpr
    intro ik
    exact (contDiffAt_dvv_off_origin H hs q (fun he => hz (he ▸ hq))
      ik.1 ik.2).continuousAt.continuousWithinAt
  obtain ⟨Mh, hh⟩ := hK.exists_bound_of_continuousOn hB
  refine ⟨max Mx (max Mv Mh), ?_⟩
  intro q hq
  refine ⟨(hx q hq).trans (le_max_left _ _),
    (hv q hq).trans ((le_max_left _ _).trans (le_max_right _ _)), ?_⟩
  intro i k
  have hc := norm_le_pi_norm (B q) (i, k)
  have hc' : |dvv H q i k| ≤ ‖B q‖ := by
    simpa only [B, Real.norm_eq_abs] using hc
  exact hc'.trans ((hh q hq).trans ((le_max_right _ _).trans (le_max_right _ _)))

/-- Positive gauge comparability and smoothness away from zero imply continuity everywhere. -/
theorem continuous_profile_of_comparison {d : ℕ} (H : XV d → ℝ)
    (alpha c C : ℝ) (ha : 0 < alpha) (hc : 0 ≤ c) (hzero : H 0 = 0)
    (hcomp : ∀ q, c * Real.rpow (rho q) alpha ≤ H q ∧
      H q ≤ C * Real.rpow (rho q) alpha)
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ : Set (XV d))) : Continuous H := by
  apply continuous_iff_continuousAt.mpr
  intro q
  by_cases hq : q = 0
  · subst q
    have hmajor : Continuous (fun q : XV d => C * Real.rpow (rho q) alpha) :=
      continuous_const.mul ((continuous_rho d).rpow_const (fun _ => Or.inr ha.le))
    have hm : Tendsto (fun q : XV d => C * Real.rpow (rho q) alpha) (nhds 0) (nhds 0) := by
      simpa only [rho_zero, Real.rpow_eq_pow, Real.zero_rpow ha.ne', mul_zero] using
        hmajor.tendsto 0
    have hz := squeeze_zero (fun q =>
      (mul_nonneg hc (Real.rpow_nonneg (rho_nonneg q) alpha)).trans (hcomp q).1)
      (fun q => (hcomp q).2) hm
    simpa only [ContinuousAt, hzero] using hz
  · exact hsmooth.continuousOn.continuousAt
      (isOpen_compl_singleton.mem_nhds (by simpa using hq))

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
