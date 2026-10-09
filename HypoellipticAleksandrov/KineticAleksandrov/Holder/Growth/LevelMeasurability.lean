module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.ReferenceGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometryMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic

/-! # Measurability of source levels using continuity only on the admissibility domain -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

open Set MeasureTheory

/-- Relative superlevels are measurable without assuming global measurability of u. -/
theorem measurableSet_superlevel_inter {d : ℕ} {O E : Set (KineticPoint d)}
    (hO : IsOpen O) (hE : MeasurableSet E) (hEO : E ⊆ O)
    {u : KineticPoint d → ℝ} (hu : ContinuousOn u O) (ell : ℝ) :
    MeasurableSet ({P | ell ≤ u P} ∩ E) := by
  classical
  let f := O.piecewise u (fun _ => 0)
  have hf : Measurable f := hu.measurable_piecewise continuous_const.continuousOn
    hO.measurableSet
  have heq : {P | ell ≤ u P} ∩ E = {P | ell ≤ f P} ∩ E := by
    ext P
    by_cases hp : P ∈ E
    · have hpo := hEO hp
      simp only [mem_inter_iff, mem_ofPred_eq, hp, and_true, f,
        piecewise_eq_of_mem O u (fun _ => 0) hpo]
    · simp only [mem_inter_iff, hp, and_false]
  rw [heq]
  exact (measurableSet_le measurable_const hf).inter hE

/-- All source level intersections are bounded by their comparison region. -/
theorem superlevel_inter_isBounded {d : ℕ} {E : Set (KineticPoint d)}
    (hE : Bornology.IsBounded E) (u : KineticPoint d → ℝ) (ell : ℝ) :
    Bornology.IsBounded ({P | ell ≤ u P} ∩ E) :=
  hE.subset inter_subset_right

/-- Exact source volume scaling also holds after conversion to real volume. -/
theorem volume_affine_image_toReal {d : ℕ} (P0 : KineticPoint d) {R : ℝ}
    (hR : 0 < R) (E : Set (KineticPoint d)) :
    (volume (kineticAffine P0 R '' E)).toReal = R ^ (4 * d + 2) * (volume E).toReal := by
  rw [volume_kineticAffine_image P0 hR, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_pos hR _).le]

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
