module

public import HypoellipticAleksandrov.Measure.ParabolicDyadicFiltration
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated

/-!
# Finite parabolic dyadic averages

This module records the explicit finite-cell averaging function at a complete
parabolic dyadic checkpoint.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- The ordinary normalized integral of `f` over one addressed dyadic cell. -/
def parabolicDyadicCellAverage (d n : ℕ)
    (f : ParabolicDyadicReferenceSpace d → ℝ)
    (index : ParabolicDyadicIndex d n) : ℝ :=
  ((parabolicDyadicReferenceMeasure d).real
      (parabolicDyadicRestrictedCell index))⁻¹ *
    ∫ x in parabolicDyadicRestrictedCell index,
      f x ∂parabolicDyadicReferenceMeasure d

/-- The finite indicator sum of the addressed-cell averages at generation
`n`. -/
def parabolicDyadicCheckpointAverage (d n : ℕ)
    (f : ParabolicDyadicReferenceSpace d → ℝ) :
    ParabolicDyadicReferenceSpace d → ℝ :=
  fun z => ∑ index : ParabolicDyadicIndex d n,
    (parabolicDyadicRestrictedCell index).indicator
      (fun _ => parabolicDyadicCellAverage d n f index) z

/-- Restricting the reference-subtype measure to an addressed cell recovers
the ambient volume of that half-open cell. -/
theorem parabolicDyadicReferenceMeasure_restrictedCell {d n : ℕ}
    (index : ParabolicDyadicIndex d n) :
    parabolicDyadicReferenceMeasure d (parabolicDyadicRestrictedCell index) =
      volume (parabolicDyadicHalfOpenCell index) := by
  rw [parabolicDyadicReferenceMeasure, comap_subtype_coe_apply
    (measurableSet_parabolicDyadicReferenceCell d)]
  change volume (Subtype.val '' (Subtype.val ⁻¹' parabolicDyadicHalfOpenCell index)) = _
  rw [Subtype.image_preimage_coe, inter_comm,
    inter_eq_left.mpr (parabolicDyadicHalfOpenCell_subset_reference index)]

/-- The real reference-subtype measure of a generation-`n` addressed cell is
the exact parabolic dyadic volume. -/
theorem parabolicDyadicReferenceMeasure_restrictedCell_toReal {d n : ℕ}
    (index : ParabolicDyadicIndex d n) :
    (parabolicDyadicReferenceMeasure d
      (parabolicDyadicRestrictedCell index)).toReal =
      (2 : ℝ) ^ d / (2 : ℝ) ^ ((d + 2) * n) := by
  rw [parabolicDyadicReferenceMeasure_restrictedCell]
  exact volume_parabolicDyadicHalfOpenCell_toReal index

/-- Every finite addressed dyadic cell has strictly positive reference
subtype measure, also in dimension zero. -/
theorem parabolicDyadicReferenceMeasure_restrictedCell_real_pos {d n : ℕ}
    (index : ParabolicDyadicIndex d n) :
    0 < (parabolicDyadicReferenceMeasure d).real
      (parabolicDyadicRestrictedCell index) := by
  rw [Measure.real, parabolicDyadicReferenceMeasure_restrictedCell_toReal]
  exact div_pos (pow_pos (by norm_num) _) (pow_pos (by norm_num) _)

/-- On an addressed generation-`n` cell, the checkpoint average is the
corresponding single-cell average. -/
theorem parabolicDyadicCheckpointAverage_eq_cellAverage {d n : ℕ}
    (f : ParabolicDyadicReferenceSpace d → ℝ)
    (index : ParabolicDyadicIndex d n) (z : ParabolicDyadicReferenceSpace d)
    (hz : z ∈ parabolicDyadicRestrictedCell index) :
    parabolicDyadicCheckpointAverage d n f z =
      parabolicDyadicCellAverage d n f index := by
  classical
  unfold parabolicDyadicCheckpointAverage
  rw [Finset.sum_eq_single index]
  · simp only [Set.indicator_of_mem hz]
  · intro other _ hne
    have hnot : z ∉ parabolicDyadicRestrictedCell other := by
      intro hother
      exact (Set.disjoint_left.mp
        (parabolicDyadicHalfOpenCell_disjoint_of_ne hne) hother hz).elim
    simp only [Set.indicator_of_notMem hnot]
  · simp

/-- The finite checkpoint average is strongly measurable for the checkpoint
filtration. -/
theorem stronglyMeasurable_parabolicDyadicCheckpointAverage (d n : ℕ)
    (f : ParabolicDyadicReferenceSpace d → ℝ) :
    StronglyMeasurable[parabolicDyadicFiltration d ((d + 2) * n)]
      (parabolicDyadicCheckpointAverage d n f) := by
  unfold parabolicDyadicCheckpointAverage
  simp only [← Finset.sum_apply]
  change StronglyMeasurable[parabolicDyadicFiltration d ((d + 2) * n)]
    (∑ index : ParabolicDyadicIndex d n,
      (parabolicDyadicRestrictedCell index).indicator
        (fun _ => parabolicDyadicCellAverage d n f index))
  apply Finset.stronglyMeasurable_sum
  intro index _
  apply stronglyMeasurable_const.indicator
  apply ProbabilityTheory.measurableSet_partitionFiltration_of_mem
    (measurableSet_parabolicDyadicGenerator d)
  rw [memPartition_parabolicDyadicFiltration_checkpoint_eq_range]
  exact ⟨index, rfl⟩

/-- The finite checkpoint average is integrable for the finite reference
measure. -/
theorem integrable_parabolicDyadicCheckpointAverage (d n : ℕ)
    (f : ParabolicDyadicReferenceSpace d → ℝ) :
    Integrable (parabolicDyadicCheckpointAverage d n f)
      (parabolicDyadicReferenceMeasure d) := by
  classical
  letI : IsFiniteMeasure (parabolicDyadicReferenceMeasure d) :=
    ⟨lt_top_iff_ne_top.mpr (parabolicDyadicReferenceMeasure_univ_ne_top d)⟩
  unfold parabolicDyadicCheckpointAverage
  apply integrable_finset_sum Finset.univ
  intro index _
  exact IntegrableOn.integrable_indicator integrableOn_const
    (measurableSet_parabolicDyadicRestrictedCell index)

/-- The set integral of the checkpoint average over an addressed cell is the
set integral of the original function over that cell. -/
theorem setIntegral_parabolicDyadicCheckpointAverage_restrictedCell
    (d n : ℕ) (f : ParabolicDyadicReferenceSpace d → ℝ)
    (index : ParabolicDyadicIndex d n) :
    ∫ x in parabolicDyadicRestrictedCell index,
      parabolicDyadicCheckpointAverage d n f x ∂parabolicDyadicReferenceMeasure d =
      ∫ x in parabolicDyadicRestrictedCell index,
        f x ∂parabolicDyadicReferenceMeasure d := by
  calc
    ∫ x in parabolicDyadicRestrictedCell index,
        parabolicDyadicCheckpointAverage d n f x ∂parabolicDyadicReferenceMeasure d =
        ∫ x in parabolicDyadicRestrictedCell index,
          parabolicDyadicCellAverage d n f index ∂parabolicDyadicReferenceMeasure d :=
      setIntegral_congr_fun (measurableSet_parabolicDyadicRestrictedCell index)
        fun z hz => parabolicDyadicCheckpointAverage_eq_cellAverage f index z hz
    _ = ∫ x in parabolicDyadicRestrictedCell index,
          f x ∂parabolicDyadicReferenceMeasure d := by
      rw [setIntegral_const, smul_eq_mul]
      unfold parabolicDyadicCellAverage
      have hpos := parabolicDyadicReferenceMeasure_restrictedCell_real_pos index
      rw [← mul_assoc, mul_inv_cancel₀ hpos.ne']
      exact one_mul _

/-- The explicit checkpoint average is the conditional expectation onto the
finite sigma-algebra generated by the complete dyadic generator block. -/
theorem parabolicDyadicCheckpointAverage_ae_eq_condExp
    (d n : ℕ) (f : ParabolicDyadicReferenceSpace d → ℝ)
    (hf : Integrable f (parabolicDyadicReferenceMeasure d)) :
    parabolicDyadicCheckpointAverage d n f =ᵐ[parabolicDyadicReferenceMeasure d]
      (parabolicDyadicReferenceMeasure d)[f |
        parabolicDyadicFiltration d ((d + 2) * n)] := by
  classical
  letI : IsFiniteMeasure (parabolicDyadicReferenceMeasure d) :=
    ⟨lt_top_iff_ne_top.mpr (parabolicDyadicReferenceMeasure_univ_ne_top d)⟩
  apply ae_eq_condExp_of_forall_setIntegral_eq
    ((parabolicDyadicFiltration d).le ((d + 2) * n)) hf
  · intro s _ _
    exact (integrable_parabolicDyadicCheckpointAverage d n f).integrableOn
  · intro s hs _
    change MeasurableSet[MeasureTheory.Filtration.seq
      (parabolicDyadicFiltration d) ((d + 2) * n)] s at hs
    change MeasurableSet[MeasurableSpace.generateFrom
      (memPartition (parabolicDyadicGenerator d) ((d + 2) * n))] s at hs
    obtain ⟨S, hS, hs_eq⟩ :=
      (MeasurableSpace.measurableSet_generateFrom_memPartition_iff
        (parabolicDyadicGenerator d) ((d + 2) * n) s).mp hs
    have hS_range : (↑S : Set (Set (ParabolicDyadicReferenceSpace d))) ⊆
        Set.range (parabolicDyadicRestrictedCell :
          ParabolicDyadicIndex d n → Set (ParabolicDyadicReferenceSpace d)) := by
      rw [← memPartition_parabolicDyadicFiltration_checkpoint_eq_range]
      exact hS
    have hmeas : ∀ cell ∈ S, MeasurableSet cell := by
      intro cell hcell
      obtain ⟨index, hindex⟩ := hS_range hcell
      rw [← hindex]
      exact measurableSet_parabolicDyadicRestrictedCell index
    have hdisjoint : (↑S : Set (Set (ParabolicDyadicReferenceSpace d))).Pairwise
        (Function.onFun Disjoint id) := by
      intro cell hcell other hother hne
      exact disjoint_memPartition (parabolicDyadicGenerator d) ((d + 2) * n)
        (hS hcell) (hS hother) hne
    have haverage : ∀ cell ∈ S,
        ∫ x in cell, parabolicDyadicCheckpointAverage d n f x
          ∂parabolicDyadicReferenceMeasure d =
        ∫ x in cell, f x ∂parabolicDyadicReferenceMeasure d := by
      intro cell hcell
      obtain ⟨index, hindex⟩ := hS_range hcell
      rw [← hindex]
      exact setIntegral_parabolicDyadicCheckpointAverage_restrictedCell d n f index
    have hS_union : ⋃₀ (↑S : Set (Set (ParabolicDyadicReferenceSpace d))) =
        ⋃ cell ∈ S, cell := by
      ext z
      simp
    calc
      ∫ x in s, parabolicDyadicCheckpointAverage d n f x
          ∂parabolicDyadicReferenceMeasure d =
          ∫ x in ⋃ cell ∈ S, cell, parabolicDyadicCheckpointAverage d n f x
            ∂parabolicDyadicReferenceMeasure d := by
        rw [hs_eq, hS_union]
      _ = ∑ cell ∈ S, ∫ x in cell, parabolicDyadicCheckpointAverage d n f x
            ∂parabolicDyadicReferenceMeasure d :=
        integral_biUnion_finset S hmeas hdisjoint fun cell hcell =>
          (integrable_parabolicDyadicCheckpointAverage d n f).integrableOn
      _ = ∑ cell ∈ S, ∫ x in cell, f x ∂parabolicDyadicReferenceMeasure d := by
        apply Finset.sum_congr rfl
        intro cell hcell
        exact haverage cell hcell
      _ = ∫ x in ⋃ cell ∈ S, cell, f x ∂parabolicDyadicReferenceMeasure d :=
        (integral_biUnion_finset S hmeas hdisjoint fun cell hcell => hf.integrableOn).symm
      _ = ∫ x in s, f x ∂parabolicDyadicReferenceMeasure d := by
        rw [hs_eq, hS_union]
  · exact (stronglyMeasurable_parabolicDyadicCheckpointAverage d n f).aestronglyMeasurable

end

end HypoellipticAleksandrov.Parabolic
