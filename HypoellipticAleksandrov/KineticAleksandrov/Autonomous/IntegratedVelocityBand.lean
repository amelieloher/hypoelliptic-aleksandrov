module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.IntegratedVelocityGreen
import Mathlib.Tactic

/-! # Measurable velocity-band occupation from smooth convex sources -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Set MeasureTheory Filter
open SectionTwo
open scoped ENNReal

/-- Velocity band in raw evolution spacetime coordinates. -/
def velocityRawBand (r : ℝ) : Set (ℝ × EvolutionAmbientState 1) :=
  {q | |q.2.1 0| ≤ 3 * r}

/-- The raw velocity band is measurable. -/
theorem velocityRawBand_measurable (r : ℝ) : MeasurableSet (velocityRawBand r) := by
  apply measurableSet_le
  · exact continuous_abs.measurable.comp ((measurable_pi_apply 0).comp measurable_snd.fst)
  · exact measurable_const

/-- A unit test of restricted band occupation is bounded by its actual convex source. -/
theorem velocityGreenRaw_band_test_le (hH : HormanderHypoellipticityStatement)
    {lam Lam r T : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (hr : 0 < r) (hT : 0 < T) (z : Z)
    (f : ℝ × EvolutionAmbientState 1 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ {q | q.1 < T})
    (hf01 : ∀ q, 0 ≤ f q ∧ f q ≤ 1) :
    (∫ q in velocityRawBand r, f q ∂velocityGreenRaw E T hT z) ≤
      (64 * r / lam) * Real.sqrt (2 * Lam * T) := by
  let mu := velocityGreenRaw E T hT z
  let g := fun q : ℝ × EvolutionAmbientState 1 =>
    f q * (lam * velocityOccupationDensity r (q.2.1 0))
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hf.mul
    (contDiff_const.mul ((velocityOccupationDensity_contDiff hr).comp
      ((contDiff_apply ℝ ℝ 0).comp contDiff_snd.fst)))
  have hgc : HasCompactSupport g := hfc.mul_right
  have hi : Integrable g mu := hg.continuous.integrable_of_hasCompactSupport hgc
  have hfint : Integrable f mu := hf.continuous.integrable_of_hasCompactSupport hfc
  have hc0 : 0 ≤ 64 * r / lam := by positivity
  have hm : (∫ q in velocityRawBand r, f q ∂mu) ≤
      (64 * r / lam) * ∫ q, g q ∂mu := by
    rw [← integral_indicator (velocityRawBand_measurable r), ← integral_const_mul]
    apply integral_mono (hfint.indicator (velocityRawBand_measurable r)) (hi.const_mul _)
    intro q
    by_cases hq : q ∈ velocityRawBand r
    · rw [indicator_of_mem hq]
      have hd := velocityConvexProfile_band_lower hr hq
      have hl : 1 ≤ (64 * r / lam) *
          (lam * velocityOccupationDensity r (q.2.1 0)) := by
        have he : (64 * r / lam) * (lam * velocityOccupationDensity r (q.2.1 0)) =
            (64 * r) * velocityOccupationDensity r (q.2.1 0) := by
          field_simp
        rw [he]
        simpa only [velocityOccupationDensity, mul_comm] using
          (div_le_iff₀ (by positivity : 0 < 64 * r)).mp hd
      have hh := mul_le_mul_of_nonneg_left hl (hf01 q).1
      dsimp only [g]
      nlinarith only [hh]
    · rw [indicator_of_notMem hq]
      exact mul_nonneg hc0 (mul_nonneg (hf01 q).1
        (mul_nonneg hlam.le (velocityOccupationDensity_nonneg r _)))
  exact hm.trans (mul_le_mul_of_nonneg_left
    (velocityGreenRaw_source_integral_le hH hlam hLam A E hE hr hT z f hf hfc hfU hf01) hc0)

/-- Uniform measurable-band occupation bound, with a constant depending only on ellipticity. -/
theorem velocityGreenRaw_band_mass_le (hH : HormanderHypoellipticityStatement)
    {lam Lam r T : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (hr : 0 < r) (hT : 0 < T) (z : Z) :
    velocityGreenRaw E T hT z (velocityRawBand r) ≤
      ENNReal.ofReal ((64 * r / lam) * Real.sqrt (2 * Lam * T)) := by
  let mu := (velocityGreenRaw E T hT z).restrict (velocityRawBand r)
  have hs : mu.restrict {q | q.1 < T} = mu := by
    dsimp only [mu]
    rw [Measure.restrict_comm, velocityGreenRaw_restrict_past]
    exact measurableSet_lt measurable_fst measurable_const
  have h := measure_mass_le_of_smooth_unit_tests mu
    (isOpen_lt continuous_fst continuous_const) hs
    ((64 * r / lam) * Real.sqrt (2 * Lam * T))
    (fun f hf hfc hfU hf01 =>
      velocityGreenRaw_band_test_le hH hlam hLam A E hE hr hT z f hf hfc hfU hf01)
  simpa only [mu, Measure.restrict_apply MeasurableSet.univ, univ_inter] using h

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
