module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Smooth cutoffs and uniform mollification

Two elementary approximation facts in a finite-dimensional real normed space, used to build
the smooth majorants of the kinetic Aleksandrov maximum principle.

* `exists_smooth_cutoff`: a compact set `K` inside an open set `U` carries a smooth cutoff
  `χ : E → [0,1]` equal to `1` on `K` and vanishing off `cthickening ε₀ K`, where
  `cthickening (2 * ε₀) K ⊆ U`.
* `exists_smooth_uniform_approx`: a continuous compactly supported nonnegative function is
  uniformly approximated, within any `η > 0`, by a nonnegative smooth function that vanishes
  off an arbitrarily small thickening of the support set.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov

open MeasureTheory Set Metric
open scoped Pointwise Convolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A compact set inside an open set carries a smooth `[0,1]`-valued cutoff equal to `1` on
the set and vanishing off a thickening whose double still lies in the open set. -/
theorem exists_smooth_cutoff {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ cthickening (2 * ε₀) K ⊆ U ∧
      ∃ χ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) ∧
        (∀ z ∈ K, χ z = 1) ∧ ∀ z, z ∉ cthickening ε₀ K → χ z = 0 := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  refine ⟨δ / 2, half_pos hδ, by rwa [mul_div_cancel₀ _ two_ne_zero], ?_⟩
  have hs : IsClosed (thickening (δ / 2) K)ᶜ := isOpen_thickening.isClosed_compl
  have hd : Disjoint (thickening (δ / 2) K)ᶜ K :=
    disjoint_compl_left_iff.2 (self_subset_thickening (half_pos hδ) K)
  obtain ⟨χ, hχ, hrange, hzero, hone⟩ :=
    exists_contDiff_zero_iff_one_iff_of_isClosed (n := (⊤ : ℕ∞)) hs hK.isClosed hd
  refine ⟨χ, hχ, fun z => hrange (mem_range_self z), fun z hz => (hone z).1 hz, fun z hz => ?_⟩
  refine (hzero z).1 ?_
  exact fun hz' => hz (thickening_subset_cthickening _ _ hz')

variable [MeasurableSpace E] [BorelSpace E]

/-- A continuous, compactly supported, nonnegative function is uniformly approximated by a
nonnegative smooth function vanishing off the `r`-thickening of any set carrying the
function. -/
theorem exists_smooth_uniform_approx (μ : Measure E) [μ.IsAddHaarMeasure]
    {H : E → ℝ} (hH : Continuous H) (hHc : HasCompactSupport H) (hnn : ∀ z, 0 ≤ H z)
    {S : Set E} (hS : ∀ z, z ∉ S → H z = 0) {r : ℝ} (hr : 0 < r) {η : ℝ} (hη : 0 < η) :
    ∃ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧ (∀ z, 0 ≤ ψ z) ∧ (∀ z, |ψ z - H z| ≤ η) ∧
      ∀ z, z ∉ cthickening r S → ψ z = 0 := by
  obtain ⟨δ', hδ', hu⟩ := Metric.uniformContinuous_iff.1
    (hHc.uniformContinuous_of_continuous hH) η hη
  set rad : ℝ := min r δ' with hrad
  have hrad_pos : 0 < rad := lt_min hr hδ'
  let φ : ContDiffBump (0 : E) := ⟨rad / 2, rad, half_pos hrad_pos, half_lt_self hrad_pos⟩
  refine ⟨φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] H, ?_, ?_, ?_, ?_⟩
  · exact φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
      hH.locallyIntegrable
  · intro z
    rw [convolution_def]
    refine integral_nonneg fun t => ?_
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    exact mul_nonneg (φ.nonneg_normed t) (hnn _)
  · intro z
    have := φ.dist_normed_convolution_le (μ := μ) (x₀ := z) (ε := η)
      hH.aestronglyMeasurable (fun x hx => (hu (lt_of_lt_of_le (mem_ball.1 hx)
        (min_le_right _ _))).le)
    simpa only [Real.dist_eq] using this
  · intro z hz
    by_contra hne
    have hmem := support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ) (μ := μ)
      (f := φ.normed μ) (g := H) hne
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.1 hmem
    rw [φ.support_normed_eq] at ha
    have hbS : b ∈ S := by
      by_contra hbS
      exact hb (hS b hbS)
    refine hz (mem_cthickening_of_dist_le _ b r S hbS ?_)
    have : ‖a‖ < rad := by simpa using ha
    rw [dist_add_self_left, ← dist_zero_right] at *
    exact (this.trans_le (min_le_left _ _)).le

end HypoellipticAleksandrov.KineticAleksandrov
