module

public import HypoellipticAleksandrov.KineticAleksandrov.Geometry
public import HypoellipticAleksandrov.Geometry.KineticPointMeasure
import Mathlib.MeasureTheory.Measure.Prod

/-! # Null time faces of kinetic cylinders and stacks

The proof uses the existing product Lebesgue measure in the literal coordinate order.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set MeasureTheory

/-- A complete kinetic time slice has zero Lebesgue measure. -/
theorem volume_time_face {d : ℕ} (t : ℝ) :
    volume {P : KineticPoint d | P.time = t} = 0 := by
  have hset : {P : KineticPoint d | P.time = t} =
      (KineticPoint.equivProd d) ⁻¹'
        ({t} ×ˢ (univ : Set (PDE.Vec d × PDE.Vec d))) := by
    ext P
    simp only [mem_ofPred_eq, mem_preimage, mem_prod, mem_singleton_iff, mem_univ,
      and_true]
    rfl
  rw [hset, (KineticPoint.measurePreserving_equivProd d).measure_preimage
    ((measurableSet_singleton t).prod MeasurableSet.univ).nullMeasurableSet]
  change (volume : Measure ℝ).prod volume ({t} ×ˢ univ) = 0
  rw [Measure.prod_prod]
  simp only [measure_singleton, zero_mul]

/-- Every subset of a kinetic time slice is null, without a measurability premise. -/
theorem volume_eq_zero_of_subset_time_face {d : ℕ} {s : Set (KineticPoint d)}
    {t : ℝ} (hs : s ⊆ {P | P.time = t}) : volume s = 0 :=
  measure_mono_null hs (volume_time_face t)

/-- Adding any part of a single time face leaves the measure unchanged. -/
theorem volume_union_time_face {d : ℕ} (s : Set (KineticPoint d))
    {f : Set (KineticPoint d)} {t : ℝ} (hf : f ⊆ {P | P.time = t}) :
    volume (s ∪ f) = volume s := by
  apply le_antisymm
  · calc
      volume (s ∪ f) ≤ volume s + volume f := measure_union_le s f
      _ = volume s := by rw [volume_eq_zero_of_subset_time_face hf, add_zero]
  · exact measure_mono subset_union_left

/-- Closing only the top time face of a backward cylinder does not change its volume. -/
theorem volume_backwardCylinder_with_top {d : ℕ} (P : KineticPoint d) (r : ℝ) :
    volume (backwardCylinder P r ∪
      {Z | Z.time = P.time ∧ Z.velocity ∈ PDE.euclideanBall P.velocity r ∧
        relativePosition P Z ∈ PDE.euclideanBall (0 : PDE.Vec d) (r ^ 3)}) =
      volume (backwardCylinder P r) := by
  apply volume_union_time_face
  intro Z hZ
  exact hZ.1

/-- Removing the terminal time face from a forward stack preserves its measure. -/
theorem volume_forwardStack_open_top {d : ℕ} (P : KineticPoint d) (r : ℝ) (m : ℕ) :
    volume (forwardStack P r m ∩ {Z | Z.time < P.time + (m : ℝ) * r ^ 2}) =
      volume (forwardStack P r m) := by
  let S := forwardStack P r m ∩ {Z | Z.time < P.time + (m : ℝ) * r ^ 2}
  let f : Set (KineticPoint d) := {Z | Z.time = P.time + (m : ℝ) * r ^ 2}
  have hsub : forwardStack P r m ⊆ S ∪ f := by
    intro Z hZ
    by_cases ht : Z.time < P.time + (m : ℝ) * r ^ 2
    · exact Or.inl ⟨hZ, ht⟩
    · exact Or.inr (le_antisymm (by linarith only [hZ.2.1]) (le_of_not_gt ht))
  apply le_antisymm (measure_mono inter_subset_left)
  calc
    volume (forwardStack P r m) ≤ volume (S ∪ f) := measure_mono hsub
    _ = volume S := volume_union_time_face S Subset.rfl

/-- Countably many time faces are still null. -/
theorem volume_iUnion_time_faces {d : ℕ} {ι : Type*} [Countable ι] (t : ι → ℝ) :
    volume (⋃ i, {P : KineticPoint d | P.time = t i}) = 0 := by
  exact measure_iUnion_null fun i => volume_time_face (t i)

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
