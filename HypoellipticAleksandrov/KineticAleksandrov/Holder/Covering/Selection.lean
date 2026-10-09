module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.Inflation
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Countable disjoint selection of kinetic cylinders

The selection theorem is abstract; the enlargement conclusion is discharged by the
Euclidean kinetic engulfing lemma rather than by a product-metric ball comparison.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set

/-- A bounded-radius family admits a countable disjoint selection covering its union
by eightfold centered kinetic inflations. -/
theorem exists_disjoint_cylinder_selection {d : ℕ} {ι : Type*}
    (P : ι → KineticPoint d) (r : ι → ℝ) (t : Set ι) (R : ℝ)
    (hr : ∀ i ∈ t, 0 < r i) (hR : ∀ i ∈ t, r i ≤ R) :
    ∃ u ⊆ t, u.Countable ∧
      u.PairwiseDisjoint (fun i => backwardCylinder (P i) (r i)) ∧
      (⋃ i ∈ t, backwardCylinder (P i) (r i)) ⊆
        ⋃ i ∈ u, inflatedCylinder (P i) (r i) 8 := by
  let : SecondCountableTopology (KineticPoint d) :=
    (KineticPoint.homeomorphProd d).secondCountableTopology
  obtain ⟨u, hut, hdisj, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement
      (fun i => backwardCylinder (P i) (r i)) t r 2 (by norm_num)
      (fun i hi => (hr i hi).le) R hR (fun i hi => cylinder_nonempty (P i) (hr i hi))
  have hcount : u.Countable := hdisj.countable_of_nonempty_interior fun i hi => by
    rw [(isOpen_cylinder (P i) (r i)).interior_eq]
    exact cylinder_nonempty (P i) (hr i (hut hi))
  refine ⟨u, hut, hcount, hdisj, ?_⟩
  intro X hX
  obtain ⟨i, hi, hXi⟩ := mem_iUnion₂.mp hX
  obtain ⟨j, hj, hij, hrj⟩ := hcover i hi
  exact mem_iUnion₂.mpr ⟨j, hj,
    cylinder_subset_inflation_of_inter (hr i hi) (hr j (hut hj)) hrj hij hXi⟩

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
