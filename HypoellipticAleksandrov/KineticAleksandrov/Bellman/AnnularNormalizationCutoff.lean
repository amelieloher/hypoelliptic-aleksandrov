module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AnnularNormalizationGeometry
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.UniquenessMeasure
import Mathlib.Tactic

/-! # One smooth radial cutoff for all homogeneous pairs -/

@[expose] public section
noncomputable section
open Set
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- One smooth radial cutoff equals one on the unit annulus and avoids the origin. -/
theorem exists_bellman_annular_cutoff :
    ∃ chi : (ℝ × ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) chi ∧ HasCompactSupport chi ∧
      tsupport chi ⊆ {q | 1 / 2 < bellmanGauge q ∧ bellmanGauge q < 4} ∧
      (∀ q, 0 ≤ chi q ∧ chi q ≤ 1) ∧
      (∀ q, 1 ≤ bellmanGauge q → bellmanGauge q ≤ 2 → chi q = 1) ∧
      (∃ chi0 : ℝ → ℝ, ∀ q, chi q = chi0 (bellmanGauge q)) := by
  obtain ⟨psi, hp, _hpc, hps, hpr, hp1⟩ := SectionTwo.exists_smooth_cutoff
    (C := Icc (1 : ℝ) 64) (V := Ioo (1 / 64 : ℝ) 4096) isCompact_Icc isOpen_Ioo
    (by intro x hx; constructor <;> linarith only [hx.1, hx.2])
  let chi : (ℝ × ℝ) → ℝ := psi ∘ bellmanGaugePower
  have hs : tsupport chi ⊆ bellmanGaugePower ⁻¹' tsupport psi :=
    fun _ hq => tsupport_comp_subset_preimage psi bellmanGaugePower_continuous hq
  have hb : tsupport chi ⊆ {q | bellmanGaugePower q ≤ 4096} := by
    intro q hq
    exact (hps (hs hq)).2.le
  have hcompact : HasCompactSupport chi :=
    (bellmanGaugePower_sublevel_isCompact 4096 (by norm_num)).of_isClosed_subset
      (isClosed_tsupport chi) hb
  refine ⟨chi, hp.comp bellmanGaugePower_contDiff, hcompact, ?_,
    fun q => hpr _, ?_, ?_⟩
  · intro q hq
    have hn := hps (hs hq)
    have he := bellmanGauge_pow_six q
    constructor
    · by_contra h
      have hh : bellmanGauge q ≤ 1 / 2 := le_of_not_gt h
      have hx := pow_le_pow_left₀ (bellmanGauge_nonneg q) hh 6
      rw [he] at hx
      norm_num at hx
      linarith only [hn.1, hx]
    · exact lt_of_pow_lt_pow_left₀ 6 (by norm_num : (0 : ℝ) ≤ 4) (by
        rw [he]
        norm_num
        exact hn.2)
  · intro q hq1 hq2
    apply hp1
    have hl := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hq1 6
    have hu := pow_le_pow_left₀ (bellmanGauge_nonneg q) hq2 6
    rw [bellmanGauge_pow_six] at hl hu
    norm_num at hl hu
    exact ⟨hl, hu⟩
  · exact ⟨fun r => psi (r ^ 6), fun q => by
      change psi (bellmanGaugePower q) = psi (bellmanGauge q ^ 6)
      rw [bellmanGauge_pow_six]⟩

end HypoellipticAleksandrov.KineticAleksandrov
