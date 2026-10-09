module

public import HypoellipticAleksandrov.Parabolic.ScalarDirichletData
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.UniquenessMeasure

/-! # Smooth signed source decomposition

A compact smooth signed source is a difference of nonnegative compact smooth sources,
using a smooth cutoff equal to one on its support.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Set

/-- Smooth signed compact sources have a nonnegative smooth decomposition in the same open set. -/
theorem exists_nonnegative_smooth_source_decomposition
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : E → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hc : HasCompactSupport F)
    {U : Set E} (hU : IsOpen U) (hs : tsupport F ⊆ U) :
    ∃ Fp Fn : E → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) Fp ∧ ContDiff ℝ (⊤ : ℕ∞) Fn ∧
      HasCompactSupport Fp ∧ HasCompactSupport Fn ∧
      tsupport Fp ⊆ U ∧ tsupport Fn ⊆ U ∧
      (∀ z, 0 ≤ Fp z) ∧ (∀ z, 0 ≤ Fn z) ∧ ∀ z, Fp z - Fn z = F z := by
  obtain ⟨χ, hχ, hχc, hχU, hχrange, hχone⟩ :=
    KineticAleksandrov.SectionTwo.exists_smooth_cutoff hc hU hs
  obtain ⟨C, hC⟩ := hF.continuous.bounded_above_of_compact_support hc
  let M := max C 0
  have hM : 0 ≤ M := le_max_right C 0
  have hb : ∀ z, |F z| ≤ M := by
    intro z
    have hcz : |F z| ≤ C := by simpa using hC z
    exact hcz.trans (le_max_left C 0)
  let Fn : E → ℝ := fun z => M * χ z
  let Fp : E → ℝ := fun z => F z + Fn z
  have hn : ContDiff ℝ (⊤ : ℕ∞) Fn := contDiff_const.mul hχ
  have hnc : HasCompactSupport Fn := hχc.mul_left
  have hnU : tsupport Fn ⊆ U := tsupport_mul_subset_right.trans hχU
  have hpU : tsupport Fp ⊆ U := (tsupport_add _ _).trans (union_subset hs hnU)
  refine ⟨Fp, Fn, hF.add hn, hn, hc.add hnc, hnc, hpU, hnU, ?_, ?_, ?_⟩
  · intro z
    by_cases hz : F z = 0
    · change 0 ≤ F z + M * χ z
      rw [hz, zero_add]
      exact mul_nonneg hM (hχrange z).1
    · have hone := hχone z (subset_tsupport F hz)
      change 0 ≤ F z + M * χ z
      rw [hone, mul_one]
      linarith only [neg_abs_le (F z), hb z]
  · intro z
    exact mul_nonneg hM (hχrange z).1
  · intro z
    exact add_sub_cancel_right (F z) (Fn z)

end HypoellipticAleksandrov.Parabolic.LocalHolder
