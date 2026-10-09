module

public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Tactic

/-! # Locally finite slices of a measure invariant under radial translation -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Measure Set

/-- The first-coordinate marginal with the second coordinate restricted to B. -/
def bellmanFirstSlice (ρ : Measure (ℝ × ℝ)) (B : Set ℝ) : Measure ℝ :=
  Measure.map Prod.fst (ρ.restrict (univ ×ˢ B))

/-- The angular section obtained by restricting log radius to the unit interval. -/
def bellmanUnitSection (ρ : Measure (ℝ × ℝ)) : Measure ℝ :=
  Measure.map Prod.snd (ρ.restrict (Ioc (0 : ℝ) 1 ×ˢ univ))

/-- The first slice evaluates a rectangle of the original measure. -/
theorem bellmanFirstSlice_apply (ρ : Measure (ℝ × ℝ)) {A B : Set ℝ}
    (hA : MeasurableSet A) :
    bellmanFirstSlice ρ B A = ρ (A ×ˢ B) := by
  rw [bellmanFirstSlice, Measure.map_apply measurable_fst hA,
    Measure.restrict_apply (measurable_fst hA)]
  congr 1
  ext q
  simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, true_and]

/-- The unit section evaluates the unit-radius rectangle of the original measure. -/
theorem bellmanUnitSection_apply (ρ : Measure (ℝ × ℝ)) {B : Set ℝ}
    (hB : MeasurableSet B) :
    bellmanUnitSection ρ B = ρ (Ioc (0 : ℝ) 1 ×ˢ B) := by
  rw [bellmanUnitSection, Measure.map_apply measurable_snd hB,
    Measure.restrict_apply (measurable_snd hB)]
  congr 1
  ext q
  simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true]
  tauto

/-- A compact angular slice has finite mass on compact radial sets. -/
theorem bellmanFirstSlice_finiteOnCompacts (ρ : Measure (ℝ × ℝ))
    [IsFiniteMeasureOnCompacts ρ] {B : Set ℝ} (hB : IsCompact B) :
    IsFiniteMeasureOnCompacts (bellmanFirstSlice ρ B) where
  lt_top_of_isCompact A hA := by
    rw [bellmanFirstSlice_apply ρ hA.measurableSet]
    exact (hA.prod hB).measure_lt_top

/-- The unit-radius angular section is locally finite. -/
theorem bellmanUnitSection_finiteOnCompacts (ρ : Measure (ℝ × ℝ))
    [IsFiniteMeasureOnCompacts ρ] : IsFiniteMeasureOnCompacts (bellmanUnitSection ρ) where
  lt_top_of_isCompact B hB := by
    rw [bellmanUnitSection_apply ρ hB.measurableSet]
    exact lt_of_le_of_lt (measure_mono (prod_mono Ioc_subset_Icc_self Subset.rfl))
      (isCompact_Icc.prod hB).measure_lt_top

/-- Translating only the first coordinate commutes with restricting the angular coordinate. -/
theorem bellmanFirstSlice_invariant (ρ : Measure (ℝ × ℝ))
    (hρ : ∀ a : ℝ, Measure.map (fun q : ℝ × ℝ => (a + q.1, q.2)) ρ = ρ)
    {B : Set ℝ} (hB : MeasurableSet B) : IsAddLeftInvariant (bellmanFirstSlice ρ B) := by
  constructor
  intro a
  let τ : ℝ × ℝ → ℝ × ℝ := fun q => (a + q.1, q.2)
  have ht : Measurable τ := by fun_prop
  have hpre : τ ⁻¹' (univ ×ˢ B) = univ ×ˢ B := by
    ext q
    simp only [mem_preimage, mem_prod, mem_univ, true_and, τ]
  have hm : Measure.map τ (ρ.restrict (univ ×ˢ B)) = ρ.restrict (univ ×ˢ B) := by
    calc
      _ = (Measure.map τ ρ).restrict (univ ×ˢ B) := by
        rw [Measure.restrict_map ht (MeasurableSet.univ.prod hB), hpre]
      _ = _ := by rw [hρ a]
  change Measure.map (fun x : ℝ => a + x)
    (Measure.map Prod.fst (ρ.restrict (univ ×ˢ B))) = _
  rw [Measure.map_map (by fun_prop) measurable_fst]
  calc
    _ = Measure.map Prod.fst (Measure.map τ (ρ.restrict (univ ×ˢ B))) := by
      rw [Measure.map_map measurable_fst ht]
      rfl
    _ = _ := by rw [hm]; rfl

/-- Haar uniqueness determines every rectangle with compact angular side. -/
theorem bellman_translation_rectangle (ρ : Measure (ℝ × ℝ))
    [IsFiniteMeasureOnCompacts ρ]
    (hρ : ∀ a : ℝ, Measure.map (fun q : ℝ × ℝ => (a + q.1, q.2)) ρ = ρ)
    {A B : Set ℝ} (hA : MeasurableSet A) (hB : IsCompact B) :
    ρ (A ×ˢ B) = volume A * bellmanUnitSection ρ B := by
  let ν := bellmanFirstSlice ρ B
  let : IsFiniteMeasureOnCompacts ν := bellmanFirstSlice_finiteOnCompacts ρ hB
  let : IsAddLeftInvariant ν := bellmanFirstSlice_invariant ρ hρ hB.measurableSet
  have he : ν = addHaarScalarFactor ν volume • volume :=
    isAddLeftInvariant_eq_smul ν volume
  have hc : addHaarScalarFactor ν volume = bellmanUnitSection ρ B := by
    have h := congrArg (fun m : Measure ℝ => m (Ioc (0 : ℝ) 1)) he
    rw [Measure.smul_apply, Real.volume_Ioc] at h
    norm_num at h
    rw [bellmanUnitSection_apply ρ hB.measurableSet]
    exact (bellmanFirstSlice_apply ρ measurableSet_Ioc).symm.trans h
      |>.symm
  rw [← bellmanFirstSlice_apply ρ hA]
  change ν A = _
  rw [he, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, hc, mul_comm]

end HypoellipticAleksandrov.KineticAleksandrov
