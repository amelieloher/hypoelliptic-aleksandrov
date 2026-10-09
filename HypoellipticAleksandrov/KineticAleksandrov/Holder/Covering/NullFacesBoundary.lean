module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.NullFacesSphere
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.Inflation
import Mathlib.Tactic

/-! # Null boundaries of positive-radius kinetic cylinders -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set MeasureTheory

/-- The closure of a kinetic cylinder satisfies all four weak coordinate inequalities. -/
theorem closure_cylinder_bounds {d : ℕ} (P : KineticPoint d) (r : ℝ) :
    closure (backwardCylinder P r) ⊆ {X | P.time-r^2 ≤ X.time ∧ X.time ≤ P.time ∧
      PDE.vecNormSq (X.velocity-P.velocity) ≤ r^2 ∧
      PDE.vecNormSq (relativePosition P X) ≤ (r^3)^2} := by
  have hx : Continuous (relativePosition P) :=
    (continuous_position.sub continuous_const).sub
      ((continuous_time.sub continuous_const).smul continuous_const)
  apply closure_minimal
  · intro X hX
    have hp : PDE.vecNormSq (relativePosition P X) < (r^3)^2 := by
      simpa only [PDE.euclideanBall, PDE.euclideanSqDist, mem_ofPred_eq, sub_zero]
        using hX.2.2.2
    exact ⟨hX.1.le, hX.2.1.le, hX.2.2.1.le, hp.le⟩
  · exact (isClosed_le continuous_const continuous_time).inter
      ((isClosed_le continuous_time continuous_const).inter
        ((isClosed_le (PDE.continuous_vecNormSq.comp
          (continuous_velocity.sub continuous_const)) continuous_const).inter
          (isClosed_le (PDE.continuous_vecNormSq.comp hx) continuous_const)))

/-- Positive-radius kinetic cylinders have null topological frontier. -/
theorem volume_frontier_cylinder {d : ℕ} (P : KineticPoint d) {r : ℝ} (hr : 0 < r) :
    volume (frontier (backwardCylinder P r)) = 0 := by
  let f₁ := {X : KineticPoint d | X.time = P.time-r^2}
  let f₂ := {X : KineticPoint d | X.time = P.time}
  let f₃ := {X : KineticPoint d | X.velocity ∈ PDE.euclideanSphere P.velocity r}
  let f₄ := {X : KineticPoint d | relativePosition P X ∈ PDE.euclideanSphere 0 (r^3)}
  have hsub : frontier (backwardCylinder P r) ⊆ f₁ ∪ f₂ ∪ f₃ ∪ f₄ := by
    intro X hX
    have hb := closure_cylinder_bounds P r (frontier_subset_closure hX)
    by_contra hn
    have h₁ : X.time ≠ P.time-r^2 := fun h => hn (Or.inl (Or.inl (Or.inl h)))
    have h₂ : X.time ≠ P.time := fun h => hn (Or.inl (Or.inl (Or.inr h)))
    have h₃ : PDE.vecNormSq (X.velocity-P.velocity) ≠ r^2 :=
      fun h => hn (Or.inl (Or.inr h))
    have h₄ : PDE.vecNormSq (relativePosition P X) ≠ (r^3)^2 := by
      intro h
      apply hn
      apply Or.inr
      simpa only [f₄, mem_ofPred_eq, PDE.euclideanSphere, PDE.euclideanSqDist, sub_zero]
        using h
    have hm : X ∈ backwardCylinder P r :=
      ⟨lt_of_le_of_ne hb.1 h₁.symm, lt_of_le_of_ne hb.2.1 h₂,
        lt_of_le_of_ne hb.2.2.1 h₃, by
          simpa only [PDE.euclideanBall, PDE.euclideanSqDist, mem_ofPred_eq, sub_zero]
            using lt_of_le_of_ne hb.2.2.2 h₄⟩
    have hi : X ∈ interior (backwardCylinder P r) := by
      rw [(isOpen_cylinder P r).interior_eq]
      exact hm
    exact hX.2 hi
  apply measure_mono_null hsub
  apply measure_union_null
  · apply measure_union_null
    · exact measure_union_null (volume_time_face _) (volume_time_face _)
    · exact volume_velocity_sphere_face P.velocity hr
  · exact volume_position_sphere_face P (pow_pos hr 3)

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
