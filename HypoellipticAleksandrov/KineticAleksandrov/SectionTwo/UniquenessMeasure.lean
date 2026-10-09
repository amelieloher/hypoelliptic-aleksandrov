module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Smooth compactly supported tests determine finite measures

Two finite Borel measures on a finite-dimensional real normed space which both
vanish off an open set `U` are equal as soon as they have the same integral
against every smooth `[0,1]`-valued function with compact support inside `U`.
-/

@[expose] public section

open MeasureTheory Set Topology

namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- A smooth cutoff, compactly supported in an open set, equal to one on a compact set. -/
theorem exists_smooth_cutoff {C V : Set E} (hC : IsCompact C) (hV : IsOpen V) (hCV : C ⊆ V) :
    ∃ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ V ∧
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧ ∀ x ∈ C, φ x = 1 := by
  obtain ⟨W, hW, hCW, hWV, hWc⟩ := exists_open_between_and_isCompact_closure hC hV hCV
  obtain ⟨φ, hφ, hrange, hsupp, hone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hW hC.isClosed hCW
  have hts : tsupport φ = closure W := by rw [tsupport, hsupp]
  refine ⟨φ, hφ, ?_, ?_, fun x => hrange (mem_range_self x), fun x hx => (hone x).mp hx⟩
  · rw [HasCompactSupport, hts]; exact hWc
  · rw [hts]; exact hWV

/-- Compact sets inside an open set carrying the test identity are dominated. -/
theorem measure_compact_le_of_smooth {μ ν : Measure E} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {U : Set E}
    (h : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) → ∫ x, φ x ∂μ = ∫ x, φ x ∂ν)
    {C V : Set E} (hC : IsCompact C) (hV : IsOpen V) (hCV : C ⊆ V) (hVU : V ⊆ U) :
    μ C ≤ ν V := by
  obtain ⟨φ, hφ, hφc, hφV, hφr, hφ1⟩ := exists_smooth_cutoff hC hV hCV
  have hcont : Continuous φ := hφ.continuous
  have hint : ∀ (m : Measure E) [IsFiniteMeasure m], Integrable φ m := fun m _ =>
    hcont.integrable_of_hasCompactSupport hφc
  have h1 : μ.real C ≤ ∫ x, φ x ∂μ := by
    calc μ.real C = ∫ x, C.indicator (1 : E → ℝ) x ∂μ := by
          rw [integral_indicator_one hC.measurableSet]
      _ ≤ ∫ x, φ x ∂μ := by
          refine integral_mono ((integrable_const (1 : ℝ)).indicator hC.measurableSet) (hint μ) ?_
          intro x
          by_cases hx : x ∈ C
          · simp [hx, hφ1 x hx]
          · simpa [hx] using (hφr x).1
  have h2 : ∫ x, φ x ∂ν ≤ ν.real V := by
    calc ∫ x, φ x ∂ν ≤ ∫ x, V.indicator (1 : E → ℝ) x ∂ν := by
          refine integral_mono (hint ν) ((integrable_const (1 : ℝ)).indicator hV.measurableSet) ?_
          intro x
          by_cases hx : x ∈ V
          · simpa [hx] using (hφr x).2
          · have : φ x = 0 := by
              by_contra hne
              exact hx (hφV (subset_tsupport φ hne))
            simp [hx, this]
      _ = ν.real V := by rw [integral_indicator_one hV.measurableSet]
  have h3 : μ.real C ≤ ν.real V := h1.trans ((h φ hφ hφc (hφV.trans hVU) hφr).le.trans h2)
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp h3

/-- Finite measures vanishing off an open set `U` are determined by smooth compact tests in `U`. -/
theorem measure_eq_of_smooth_integral_eq {μ ν : Measure E} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {U : Set E} (hU : IsOpen U) (hμ : μ Uᶜ = 0) (hν : ν Uᶜ = 0)
    (h : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) → ∫ x, φ x ∂μ = ∫ x, φ x ∂ν) :
    μ = ν := by
  have hle : ∀ {μ ν : Measure E} [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      (∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
        (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) → ∫ x, φ x ∂μ = ∫ x, φ x ∂ν) →
      ∀ V, IsOpen V → V ⊆ U → μ V ≤ ν V := by
    intro μ ν _ _ h V hV hVU
    refine le_of_forall_lt fun r hr => ?_
    obtain ⟨C, hCV, hCc, hrC⟩ := hV.exists_lt_isCompact hr
    exact hrC.trans_le (measure_compact_le_of_smooth h hCc hV hCV hVU)
  have hopen : ∀ {m : Measure E}, m Uᶜ = 0 → ∀ O : Set E, m O = m (O ∩ U) := by
    intro m hm O
    refine le_antisymm ?_ (measure_mono inter_subset_left)
    calc m O ≤ m ((O ∩ U) ∪ Uᶜ) := measure_mono (fun x hx => by
          by_cases hxU : x ∈ U
          · exact Or.inl ⟨hx, hxU⟩
          · exact Or.inr hxU)
      _ ≤ m (O ∩ U) + m Uᶜ := measure_union_le _ _
      _ = m (O ∩ U) := by rw [hm, add_zero]
  have key : ∀ O : Set E, IsOpen O → μ O = ν O := by
    intro O hO
    rw [hopen hμ, hopen hν]
    have hOU : IsOpen (O ∩ U) := hO.inter hU
    exact le_antisymm (hle h _ hOU inter_subset_right)
      (hle (fun φ a b c d => (h φ a b c d).symm) _ hOU inter_subset_right)
  exact ext_of_generate_finite {s : Set E | IsOpen s} (BorelSpace.measurable_eq)
    isPiSystem_isOpen (fun O hO => key O hO) (key univ isOpen_univ)

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
