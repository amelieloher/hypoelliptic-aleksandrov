module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.DensityFromTestsLocalDensity
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Sharp density theorem from positive smooth compact tests

For a finite measure concentrated on an open slab, a uniform conjugate smooth-test
bound forces absolute continuity and an `Lʳ` density for every finite `r > 1`.
The reference measure is explicitly restricted to the open slab; endpoint atoms are
excluded by the concentration assumption. No density or absolute-continuity input is used.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set Filter
open scoped ENNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- An open set has compact interior subsets eventually containing each of its points. -/
theorem exists_compact_interior_exhaustion {U : Set E} (hU : IsOpen U) :
    ∃ K : ℕ → Set E, (∀ n, IsCompact (K n)) ∧ (∀ n, K n ⊆ U) ∧
      ∀ x ∈ U, ∀ᶠ n in atTop, x ∈ K n := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let k : CompactExhaustion U := CompactExhaustion.choice U
  let K : ℕ → Set E := fun n => Subtype.val '' k n
  refine ⟨K, fun n => (k.isCompact n).image continuous_subtype_val,
    fun n x hx => ?_, ?_⟩
  · obtain ⟨y, _, rfl⟩ := hx
    exact y.property
  · intro x hx
    have hxall : (⟨x, hx⟩ : U) ∈ ⋃ n, k n := by rw [k.iUnion_eq]; trivial
    obtain ⟨N, hN⟩ := mem_iUnion.mp hxall
    filter_upwards [eventually_ge_atTop N] with n hn
    exact ⟨⟨x, hx⟩, k.subset hn hN, rfl⟩

/-- A conjugate positive smooth-test bound gives a measurable nonnegative sharp `Lʳ` density.
The finite tested measure is concentrated on the open region `U`; all norms use `ν.restrict U`.
The same density has its exact `L¹` mass and represents every real test integral. -/
theorem exists_density_of_smooth_tests (ν μ : Measure E)
    [ν.IsAddHaarMeasure] [IsFiniteMeasure μ] {U : Set E} (hU : IsOpen U)
    (hμU : μ Uᶜ = 0) {r C : ℝ} (hr : 1 < r) (hC : 0 ≤ C)
    (htest : ∀ f : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      tsupport f ⊆ U → (∀ x, 0 ≤ f x) →
      (∫ x, f x ∂μ) ≤ C *
        (eLpNorm f (ENNReal.ofReal (r / (r - 1))) (ν.restrict U)).toReal) :
    μ ≪ ν.restrict U ∧ ∃ g : E → ℝ,
      Measurable g ∧ (∀ x, 0 ≤ g x) ∧ Integrable g (ν.restrict U) ∧
      MemLp g (ENNReal.ofReal r) (ν.restrict U) ∧
      (eLpNorm g (ENNReal.ofReal r) (ν.restrict U)).toReal ≤ C ∧
      (∫ x, g x ∂ν.restrict U) = (μ univ).toReal ∧
      ∀ f : E → ℝ, (∫ x, f x * g x ∂ν.restrict U) = ∫ x, f x ∂μ := by
  have hp : 1 ≤ ENNReal.ofReal (r / (r - 1)) := by
    apply ENNReal.one_le_ofReal.mpr
    exact (le_div_iff₀ (by linarith)).2 (by linarith)
  have hac := absolutelyContinuous_of_smooth_tests ν μ hU hμU hp
    ENNReal.ofReal_ne_top hC htest
  have hprops := rnDensity_of_smooth_tests ν μ hU hμU hp ENNReal.ofReal_ne_top hC htest
  let g := fun x => (μ.rnDeriv (ν.restrict U) x).toReal
  obtain ⟨K, hK, hKU, hcover⟩ := exists_compact_interior_exhaustion hU
  have hlocal (n : ℕ) := rnDensity_compact_norm_le ν μ hU hμU hr hC htest (hK n) (hKU n)
  have hnorm (n : ℕ) :
      eLpNorm ((K n).indicator g) (ENNReal.ofReal r) (ν.restrict U) ≤
        ENNReal.ofReal C := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict (hK n).measurableSet]
    exact (ENNReal.toReal_le_toReal (hlocal n).1.eLpNorm_ne_top
      ENNReal.ofReal_ne_top).mp (by simpa only [ENNReal.toReal_ofReal hC] using (hlocal n).2)
  have hlim : ∀ᵐ x ∂ν.restrict U,
      Tendsto (fun n => (K n).indicator g x) atTop (𝓝 (g x)) := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [hcover x hx] with n hn
    exact (indicator_of_mem hn g).symm
  have hglobal : eLpNorm g (ENNReal.ofReal r) (ν.restrict U) ≤ ENNReal.ofReal C := by
    refine (Lp.eLpNorm_lim_le_liminf_eLpNorm
      (fun n => hprops.1.aestronglyMeasurable.indicator (hK n).measurableSet)
      g hprops.1.aestronglyMeasurable hlim).trans ?_
    exact liminf_le_of_frequently_le (Frequently.of_forall hnorm)
  refine ⟨hac, g, hprops.1, hprops.2.1, hprops.2.2.1,
    hglobal.trans_lt ENNReal.ofReal_lt_top, ?_, hprops.2.2.2.2, hprops.2.2.2.1⟩
  simpa only [ENNReal.toReal_ofReal hC] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hglobal

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
