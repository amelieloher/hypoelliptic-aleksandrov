module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitWholeUniform

/-! # Bounded inner cylinders and neighbourhoods for whole-space exhaustion -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov Set Filter
open scoped Topology

/-- A strict bounded whole-space cylinder, using the explicit Euclidean radial cutoff. -/
def wholeSpaceInnerCylinder {n : ℕ} (α τ S : ℝ) : Set (KineticPoint n) :=
  {p | α < p.time ∧ p.time < τ ∧ radialSq p < S ^ 2}

/-- Strict bounded whole-space cylinders are open. -/
theorem isOpen_wholeSpaceInnerCylinder {n : ℕ} (α τ S : ℝ) :
    IsOpen (wholeSpaceInnerCylinder (n := n) α τ S) :=
  (isOpen_lt continuous_const continuous_time).inter
    ((isOpen_lt continuous_time continuous_const).inter
      (isOpen_lt continuous_radialSq continuous_const))

/-- The strict whole-space cylinder lies in its compact closed counterpart. -/
theorem wholeSpaceInnerCylinder_subset_closed {n : ℕ} (α τ S : ℝ) :
    wholeSpaceInnerCylinder (n := n) α τ S ⊆
      movingClosedSlab univ (fun _ => 0) α τ ∩ {p | radialSq p ≤ S ^ 2} := by
  intro p hp
  have hm : p.position ∈ movingDomain univ (fun _ : ℝ => (0 : PDE.Vec n)) p.time :=
    mem_movingDomain_iff.mpr (mem_univ _)
  exact ⟨⟨hp.1.le, hp.2.1.le, subset_closure hm⟩, hp.2.2.le⟩

/-- Compact radial cylinders are relative neighbourhoods of all points of a whole-space
closed slab, including its time faces. -/
theorem exists_wholeSpace_closedCylinder_mem_nhdsWithin {n : ℕ} {α τ : ℝ}
    {p : KineticPoint n}
    (_hp : p ∈ movingClosedSlab univ (fun _ => 0) α τ) :
    ∃ S : ℝ, 0 < S ∧ radialSq p < S ^ 2 ∧
      (movingClosedSlab univ (fun _ : ℝ => (0 : PDE.Vec n)) α τ ∩
        {p | radialSq p ≤ S ^ 2}) ∈
        𝓝[movingClosedSlab univ (fun _ : ℝ => (0 : PDE.Vec n)) α τ] p := by
  let S := radialSq p + 1
  have hrad0 : 0 ≤ radialSq p :=
    add_nonneg (PDE.vecNormSq_nonneg _) (PDE.vecNormSq_nonneg _)
  have hS : 0 < S := by dsimp [S]; linarith
  have hrad : radialSq p < S ^ 2 := by dsimp [S]; nlinarith
  refine ⟨S, hS, hrad, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    (continuous_radialSq.continuousAt.eventually (gt_mem_nhds hrad)).filter_mono
      nhdsWithin_le_nhds] with q hq hrq
  exact ⟨hq, hrq.le⟩

end HypoellipticAleksandrov.KineticAleksandrov
