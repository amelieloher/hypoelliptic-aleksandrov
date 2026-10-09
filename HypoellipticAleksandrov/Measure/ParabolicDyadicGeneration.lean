module

public import HypoellipticAleksandrov.Measure.ParabolicDyadicFiltration
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Tactic.Linarith

/-!
# Generation by the finite parabolic dyadic filtration

This file proves that the scheduled finite parabolic dyadic filtration
generates the actual measurable space on the half-open reference-cell subtype.
The proof recovers the time and velocity coordinates from countable unions of
addressed half-open cells whose dyadic widths shrink to zero.
-/

@[expose] public section

open Filter MeasureTheory Set

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

private theorem measurableSet_parabolicDyadicRestrictedCell_iSup
    (d n : ℕ) (index : ParabolicDyadicIndex d n) :
    MeasurableSet[⨆ k : ℕ, parabolicDyadicFiltration d k]
      (parabolicDyadicRestrictedCell index) := by
  obtain ⟨z, hz⟩ := parabolicDyadicHalfOpenCell_nonempty index
  let z' : ParabolicDyadicReferenceSpace d :=
    ⟨z, parabolicDyadicHalfOpenCell_subset_reference index hz⟩
  have hz' : z' ∈ parabolicDyadicRestrictedCell index := by
    change z ∈ parabolicDyadicHalfOpenCell index
    exact hz
  have hatom : MeasurableSet[parabolicDyadicFiltration d ((d + 2) * n)]
      (memPartitionSet (parabolicDyadicGenerator d) ((d + 2) * n) z') :=
    ProbabilityTheory.measurableSet_partitionFiltration_memPartitionSet
      (measurableSet_parabolicDyadicGenerator d) ((d + 2) * n) z'
  rw [memPartitionSet_parabolicDyadicFiltration_checkpoint_eq_cell index z' hz'] at hatom
  exact (le_iSup (fun k : ℕ => parabolicDyadicFiltration d k)
    ((d + 2) * n)) _ hatom

private noncomputable def parabolicDyadicTimeLowerUnion (d : ℕ) (q : ℝ) :
    Set (ParabolicDyadicReferenceSpace d) := by
  classical
  exact ⋃ n : ℕ, ⋃ index : ParabolicDyadicIndex d n,
    if ∀ z ∈ parabolicDyadicRestrictedCell index, z.val.1 < q then
      parabolicDyadicRestrictedCell index
    else ∅

private theorem measurableSet_parabolicDyadicTimeLowerUnion (d : ℕ) (q : ℝ) :
    MeasurableSet[⨆ k : ℕ, parabolicDyadicFiltration d k]
      (parabolicDyadicTimeLowerUnion d q) := by
  classical
  unfold parabolicDyadicTimeLowerUnion
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro index
  let M : MeasurableSpace (ParabolicDyadicReferenceSpace d) :=
    ⨆ k : ℕ, parabolicDyadicFiltration d k
  change @MeasurableSet _ M (if ∀ z ∈ parabolicDyadicRestrictedCell index,
    z.val.1 < q then parabolicDyadicRestrictedCell index else ∅)
  exact @MeasurableSet.ite' _ M _ _ _
    (fun _ => measurableSet_parabolicDyadicRestrictedCell_iSup d n index)
    (fun _ => @MeasurableSet.empty _ M)

private theorem parabolicDyadicTimeLowerUnion_eq_preimage_Iio (d : ℕ) (q : ℝ) :
    parabolicDyadicTimeLowerUnion d q =
      {z : ParabolicDyadicReferenceSpace d | z.val.1 < q} := by
  classical
  ext z
  constructor
  · intro hz
    change z.val.1 < q
    obtain ⟨n, hz⟩ := Set.mem_iUnion.mp hz
    obtain ⟨index, hz⟩ := Set.mem_iUnion.mp hz
    by_cases hcell : ∀ y ∈ parabolicDyadicRestrictedCell index, y.val.1 < q
    · rw [if_pos hcell] at hz
      exact hcell z hz
    · rw [if_neg hcell] at hz
      exact False.elim (Set.notMem_empty z hz)
  · intro hz
    have hgap : 0 < q - z.val.1 := sub_pos.mpr hz
    have hwidth_eventually : ∀ᶠ n in atTop, parabolicDyadicTimeWidth n < q - z.val.1 :=
      tendsto_parabolicDyadicTimeWidth_atTop.eventually_lt_const hgap
    obtain ⟨n, hn⟩ := eventually_atTop.mp hwidth_eventually
    have hwidth : parabolicDyadicTimeWidth n < q - z.val.1 := hn n le_rfl
    have hzcover : (z : TimeVelocity d) ∈
        ⋃ index : ParabolicDyadicIndex d n, parabolicDyadicHalfOpenCell index := by
      rw [iUnion_parabolicDyadicHalfOpenCell_eq_reference]
      exact z.property
    obtain ⟨index, hzindex⟩ := Set.mem_iUnion.mp hzcover
    have hzindex' : z ∈ parabolicDyadicRestrictedCell index := by
      change (z : TimeVelocity d) ∈ parabolicDyadicHalfOpenCell index
      exact hzindex
    have hcell : ∀ y ∈ parabolicDyadicRestrictedCell index, y.val.1 < q := by
      intro y hy
      change (y : TimeVelocity d) ∈ parabolicDyadicHalfOpenCell index at hy
      rw [mem_parabolicDyadicHalfOpenCell_iff] at hzindex hy
      have hcell_width := parabolicDyadicTimeCell_width index
      linarith [hzindex.1.1, hy.1.2, hcell_width, hwidth]
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    refine Set.mem_iUnion.mpr ⟨index, ?_⟩
    rw [if_pos hcell]
    exact hzindex'

private theorem measurableSet_time_preimage_Iio_iSup (d : ℕ) (q : ℝ) :
    MeasurableSet[⨆ k : ℕ, parabolicDyadicFiltration d k]
      {z : ParabolicDyadicReferenceSpace d | z.val.1 < q} := by
  rw [← parabolicDyadicTimeLowerUnion_eq_preimage_Iio]
  exact measurableSet_parabolicDyadicTimeLowerUnion d q

private noncomputable def parabolicDyadicVelocityLowerUnion (d : ℕ)
    (coordinate : Fin d) (q : ℝ) : Set (ParabolicDyadicReferenceSpace d) := by
  classical
  exact ⋃ n : ℕ, ⋃ index : ParabolicDyadicIndex d n,
    if ∀ z ∈ parabolicDyadicRestrictedCell index, z.val.2 coordinate < q then
      parabolicDyadicRestrictedCell index
    else ∅

private theorem measurableSet_parabolicDyadicVelocityLowerUnion (d : ℕ)
    (coordinate : Fin d) (q : ℝ) :
    MeasurableSet[⨆ k : ℕ, parabolicDyadicFiltration d k]
      (parabolicDyadicVelocityLowerUnion d coordinate q) := by
  classical
  unfold parabolicDyadicVelocityLowerUnion
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro index
  let M : MeasurableSpace (ParabolicDyadicReferenceSpace d) :=
    ⨆ k : ℕ, parabolicDyadicFiltration d k
  change @MeasurableSet _ M (if ∀ z ∈ parabolicDyadicRestrictedCell index,
    z.val.2 coordinate < q then parabolicDyadicRestrictedCell index else ∅)
  exact @MeasurableSet.ite' _ M _ _ _
    (fun _ => measurableSet_parabolicDyadicRestrictedCell_iSup d n index)
    (fun _ => @MeasurableSet.empty _ M)

private theorem parabolicDyadicVelocityLowerUnion_eq_preimage_Iio (d : ℕ)
    (coordinate : Fin d) (q : ℝ) :
    parabolicDyadicVelocityLowerUnion d coordinate q =
      {z : ParabolicDyadicReferenceSpace d | z.val.2 coordinate < q} := by
  classical
  ext z
  constructor
  · intro hz
    change z.val.2 coordinate < q
    obtain ⟨n, hz⟩ := Set.mem_iUnion.mp hz
    obtain ⟨index, hz⟩ := Set.mem_iUnion.mp hz
    by_cases hcell : ∀ y ∈ parabolicDyadicRestrictedCell index, y.val.2 coordinate < q
    · rw [if_pos hcell] at hz
      exact hcell z hz
    · rw [if_neg hcell] at hz
      exact False.elim (Set.notMem_empty z hz)
  · intro hz
    have hgap : 0 < q - z.val.2 coordinate := sub_pos.mpr hz
    have hwidth_eventually : ∀ᶠ n in atTop,
        parabolicDyadicVelocityWidth n < q - z.val.2 coordinate :=
      tendsto_parabolicDyadicVelocityWidth_atTop.eventually_lt_const hgap
    obtain ⟨n, hn⟩ := eventually_atTop.mp hwidth_eventually
    have hwidth : parabolicDyadicVelocityWidth n < q - z.val.2 coordinate := hn n le_rfl
    have hzcover : (z : TimeVelocity d) ∈
        ⋃ index : ParabolicDyadicIndex d n, parabolicDyadicHalfOpenCell index := by
      rw [iUnion_parabolicDyadicHalfOpenCell_eq_reference]
      exact z.property
    obtain ⟨index, hzindex⟩ := Set.mem_iUnion.mp hzcover
    have hzindex' : z ∈ parabolicDyadicRestrictedCell index := by
      change (z : TimeVelocity d) ∈ parabolicDyadicHalfOpenCell index
      exact hzindex
    have hcell : ∀ y ∈ parabolicDyadicRestrictedCell index,
        y.val.2 coordinate < q := by
      intro y hy
      change (y : TimeVelocity d) ∈ parabolicDyadicHalfOpenCell index at hy
      rw [mem_parabolicDyadicHalfOpenCell_iff,
        mem_parabolicDyadicVelocityCell_iff] at hzindex hy
      have hcell_width := parabolicDyadicVelocityCell_width index coordinate
      linarith [hzindex.2 coordinate |>.1, hy.2 coordinate |>.2, hcell_width, hwidth]
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    refine Set.mem_iUnion.mpr ⟨index, ?_⟩
    rw [if_pos hcell]
    exact hzindex'

private theorem measurableSet_velocity_preimage_Iio_iSup (d : ℕ)
    (coordinate : Fin d) (q : ℝ) :
    MeasurableSet[⨆ k : ℕ, parabolicDyadicFiltration d k]
      {z : ParabolicDyadicReferenceSpace d | z.val.2 coordinate < q} := by
  rw [← parabolicDyadicVelocityLowerUnion_eq_preimage_Iio]
  exact measurableSet_parabolicDyadicVelocityLowerUnion d coordinate q

/-- The scheduled finite parabolic dyadic filtration generates exactly the
ambient subtype measurable space of the half-open reference cell. -/
theorem iSup_parabolicDyadicFiltration_eq_referenceMeasurableSpace (d : ℕ) :
    (⨆ k : ℕ, parabolicDyadicFiltration d k) =
      (inferInstance : MeasurableSpace (ParabolicDyadicReferenceSpace d)) := by
  apply le_antisymm
  · apply iSup_le
    intro k
    exact (parabolicDyadicFiltration d).le k
  · let M : MeasurableSpace (ParabolicDyadicReferenceSpace d) :=
      ⨆ k : ℕ, parabolicDyadicFiltration d k
    have htime : Measurable[M] (fun z : ParabolicDyadicReferenceSpace d => z.val.1) :=
      measurable_of_Iio fun q => by
        change MeasurableSet[⨆ k : ℕ, parabolicDyadicFiltration d k]
          {z : ParabolicDyadicReferenceSpace d | z.val.1 < q}
        exact measurableSet_time_preimage_Iio_iSup d q
    have hvelocity : Measurable[M] (fun z : ParabolicDyadicReferenceSpace d => z.val.2) :=
      measurable_pi_iff.mpr fun coordinate =>
        measurable_of_Iio fun q => by
          change MeasurableSet[⨆ k : ℕ, parabolicDyadicFiltration d k]
            {z : ParabolicDyadicReferenceSpace d | z.val.2 coordinate < q}
          exact measurableSet_velocity_preimage_Iio_iSup d coordinate q
    have hcoe : Measurable[M] (fun z : ParabolicDyadicReferenceSpace d =>
        ((z.val.1, z.val.2) : TimeVelocity d)) := htime.prodMk hvelocity
    change MeasurableSpace.comap Subtype.val
      (inferInstance : MeasurableSpace (TimeVelocity d)) ≤ M
    exact hcoe.comap_le

end

end HypoellipticAleksandrov.Parabolic
