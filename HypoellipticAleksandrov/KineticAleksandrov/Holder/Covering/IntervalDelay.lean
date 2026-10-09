module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.IntervalDelayFinite
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

/-! # Sharp delayed-interval union inequality

The finite estimate uses bounded open components. The countable estimate follows by
continuity from below over finite subfamilies, with no uniform bound on the intervals.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set MeasureTheory

/-- A bounded forward union controls the preceding union by the sharp delay factor. -/
theorem interval_delay_of_bounded_union {ι : Type*} (a h : ι → ℝ) (I : Set ι)
    {m : ℝ} (hm : 0 < m) (hh : ∀ i ∈ I, 0 < h i)
    (hbelow : BddBelow (⋃ i ∈ I, Ioo (a i) (a i + m*h i)))
    (habove : BddAbove (⋃ i ∈ I, Ioo (a i) (a i + m*h i))) :
    volume (⋃ i ∈ I, Ioo (a i-h i) (a i)) ≤
      ENNReal.ofReal ((m+1)/m) * volume (⋃ i ∈ I, Ioo (a i) (a i+m*h i)) := by
  let U := ⋃ i ∈ I, Ioo (a i) (a i+m*h i)
  obtain ⟨C, hcount, hdisj, hcomp, hcover, hcontains⟩ :=
    bounded_open_interval_components (isOpen_biUnion fun _ _ => isOpen_Ioo) hbelow habove
  let ext : Set ℝ → Set ℝ := fun s => Ioo (sInf s-(sSup s-sInf s)/m) (sSup s)
  have hback : (⋃ i ∈ I, Ioo (a i-h i) (a i)) ⊆ ⋃ s ∈ C, ext s := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    have hai : a i < a i+m*h i := by nlinarith only [hm, hh i hi]
    obtain ⟨s, hs, hIs⟩ := hcontains (a i) (a i+m*h i) hai
      (subset_iUnion₂_of_subset i hi Subset.rfl)
    have hI := backwardInterval_subset_component_extension (hh i hi) hm
      (hIs.trans (subset_of_eq (hcomp s hs).2))
    exact mem_iUnion₂.mpr ⟨s, hs, hI hxi⟩
  have hvol : ∀ s ∈ C, volume (ext s) = ENNReal.ofReal ((m+1)/m) * volume s := by
    intro s hs
    change volume (Ioo (sInf s-(sSup s-sInf s)/m) (sSup s)) = _
    rw [volume_component_extension hm, ← (hcomp s hs).2]
  have hmeas : ∀ s ∈ C, MeasurableSet s := by
    intro s hs
    rw [(hcomp s hs).2]
    exact measurableSet_Ioo
  calc
    volume (⋃ i ∈ I, Ioo (a i-h i) (a i)) ≤ volume (⋃ s ∈ C, ext s) :=
      measure_mono hback
    _ ≤ ∑' s : C, volume (ext s) := measure_biUnion_le volume hcount ext
    _ = ∑' s : C, ENNReal.ofReal ((m+1)/m) * volume (s : Set ℝ) :=
      tsum_congr fun s => hvol s s.2
    _ = ENNReal.ofReal ((m+1)/m) * ∑' s : C, volume (s : Set ℝ) :=
      ENNReal.tsum_mul_left
    _ = ENNReal.ofReal ((m+1)/m) * volume U := by
      have hsum := measure_biUnion (μ := volume) hcount hdisj hmeas
      simp only [id_eq] at hsum
      rw [hcover] at hsum
      rw [← hsum]

/-- The sharp delayed-union inequality for a finite interval family. -/
theorem interval_delay_finset {ι : Type*} (a h : ι → ℝ) (s : Finset ι)
    {m : ℝ} (hm : 0 < m) (hh : ∀ i ∈ s, 0 < h i) :
    volume (⋃ i ∈ s, Ioo (a i-h i) (a i)) ≤
      ENNReal.ofReal ((m+1)/m) * volume (⋃ i ∈ s, Ioo (a i) (a i+m*h i)) := by
  apply interval_delay_of_bounded_union a h (s : Set ι) hm hh
  · obtain ⟨l, hl⟩ := (s.finite_toSet.image a).bddBelow
    refine ⟨l, ?_⟩
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    exact (hl (mem_image_of_mem a hi)).trans hxi.1.le
  · obtain ⟨b, hb⟩ := (s.finite_toSet.image (fun i => a i+m*h i)).bddAbove
    refine ⟨b, ?_⟩
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    exact hxi.2.le.trans (hb (mem_image_of_mem (fun i => a i+m*h i) hi))

/-- Countable delayed interval families satisfy the same sharp factor. -/
theorem interval_delay_countable {ι : Type*} [Countable ι] (a h : ι → ℝ)
    {m : ℝ} (hm : 0 < m) (hh : ∀ i, 0 < h i) :
    volume (⋃ i, Ioo (a i-h i) (a i)) ≤
      ENNReal.ofReal ((m+1)/m) * volume (⋃ i, Ioo (a i) (a i+m*h i)) := by
  classical
  let B : Finset ι → Set ℝ := fun s => ⋃ i ∈ s, Ioo (a i-h i) (a i)
  have hB : Monotone B := by
    intro s t hst x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨i, hst hi, hxi⟩
  have heq : (⋃ s, B s) = ⋃ i, Ioo (a i-h i) (a i) := by
    ext x
    simp only [B, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨s, i, _, hx⟩
      exact ⟨i, hx⟩
    · rintro ⟨i, hx⟩
      exact ⟨{i}, i, Finset.mem_singleton_self i, hx⟩
  rw [← heq, hB.measure_iUnion]
  apply iSup_le
  intro s
  calc
    volume (B s) ≤ ENNReal.ofReal ((m+1)/m) *
        volume (⋃ i ∈ s, Ioo (a i) (a i+m*h i)) :=
      interval_delay_finset a h s hm (fun i _ => hh i)
    _ ≤ ENNReal.ofReal ((m+1)/m) * volume (⋃ i, Ioo (a i) (a i+m*h i)) := by
      apply mul_le_mul_right
      apply measure_mono
      intro x hx
      obtain ⟨i, _, hxi⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion.mpr ⟨i, hxi⟩

/-- Countably many interval endpoints do not change the measure of an interval union. -/
theorem volume_iUnion_Ioc_eq_Ioo {ι : Type*} [Countable ι] (a b : ι → ℝ) :
    volume (⋃ i, Ioc (a i) (b i)) = volume (⋃ i, Ioo (a i) (b i)) := by
  have hnull : volume (range b) = 0 := (countable_range b).measure_zero volume
  apply le_antisymm
  · have hsub : (⋃ i, Ioc (a i) (b i)) ⊆ (⋃ i, Ioo (a i) (b i)) ∪ range b := by
      intro x hx
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      rcases lt_or_eq_of_le hxi.2 with hlt | heq
      · exact Or.inl (mem_iUnion.mpr ⟨i, hxi.1, hlt⟩)
      · exact Or.inr ⟨i, heq.symm⟩
    calc
      volume (⋃ i, Ioc (a i) (b i)) ≤
          volume ((⋃ i, Ioo (a i) (b i)) ∪ range b) := measure_mono hsub
      _ ≤ volume (⋃ i, Ioo (a i) (b i)) + volume (range b) := measure_union_le _ _
      _ = volume (⋃ i, Ioo (a i) (b i)) := by rw [hnull, add_zero]
  · apply measure_mono
    exact iUnion_mono fun _ => Ioo_subset_Ioc_self

/-- The sharp delay factor also holds for the source's half-closed intervals. -/
theorem interval_delay_countable_Ioc {ι : Type*} [Countable ι] (a h : ι → ℝ)
    {m : ℝ} (hm : 0 < m) (hh : ∀ i, 0 < h i) :
    volume (⋃ i, Ioc (a i-h i) (a i)) ≤
      ENNReal.ofReal ((m+1)/m) * volume (⋃ i, Ioc (a i) (a i+m*h i)) := by
  rw [volume_iUnion_Ioc_eq_Ioo, volume_iUnion_Ioc_eq_Ioo]
  exact interval_delay_countable a h hm hh

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
