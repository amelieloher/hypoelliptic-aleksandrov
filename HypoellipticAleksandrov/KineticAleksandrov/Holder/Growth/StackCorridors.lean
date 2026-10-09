module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.StackCorridorsInclusions
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.StackCorridorsRegion

/-! # Source stack corridors for the common growth-lemma witnesses

The comparison region depends only on dimension and stack height. The path is Hermite
on the travel interval and tangent before its initial time, as in the companion paper.
-/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
open Set

/-- Exact source cap and comparison-region corridors for every stack endpoint. -/
theorem exists_stack_corridors {d : ℕ} (P0 P : KineticPoint d) {r : ℝ} (hr : 0 < r)
    (m : ℕ) (hP : P ∈ forwardStack P0 r m) :
    ∃ x v : ℝ → PDE.Vec d,
      IsSkeleton x v ((384*((m : ℝ)+2)+32)/r)
        (-(r^2/32)) (P.time-stackStartTime P0 r) ∧
      x 0 = stackStartPosition P0 r ∧ v 0 = P0.velocity ∧
      x (P.time-stackStartTime P0 r) = P.position ∧
      v (P.time-stackStartTime P0 r) = P.velocity ∧
      r^2/8 ≤ P.time-stackStartTime P0 r ∧
      P.time-stackStartTime P0 r ≤ ((m : ℝ)+1)*r^2 ∧
      corridor (stackStartTime P0 r) (-(r^2/32)) 0 (r^3/(2*8^3)) (r/16) x v ⊆
        kineticAffine P0 r '' cap d ∧
      corridor (stackStartTime P0 r) (-(r^2/32)) (P.time-stackStartTime P0 r)
        (r^3/(2*8^3)) (r/16) x v ⊆ kineticAffine P0 r '' stackComparisonRegion d m := by
  obtain ⟨hlo, hhi, -, -⟩ := stack_endpoint_data P0 P hr m hP
  obtain ⟨x, v, hsk, hx0, hv0, hxT, hvT, hleft, hb⟩ := exists_stack_path P0 P hr m hP
  exact ⟨x, v, hsk, hx0, hv0, hxT, hvT, hlo, hhi,
    initial_corridor_subset_cap P0 hr x v hleft,
    full_corridor_subset_comparison P0 P hr m hhi x v hb⟩

/-- The same fixed comparison region encloses both reference closures. -/
theorem stackComparisonRegion_geometry (d m : ℕ) :
    IsOpen (stackComparisonRegion d m) ∧ Bornology.IsBounded (stackComparisonRegion d m) ∧
      closure (backwardCylinder (⟨0,0,0⟩ : KineticPoint d) 1) ⊆ stackComparisonRegion d m ∧
      closure (forwardStack (⟨0,0,0⟩ : KineticPoint d) 1 m) ⊆
        stackComparisonRegion d m :=
  ⟨isOpen_stackComparisonRegion d m, isBounded_stackComparisonRegion d m,
    closure_unitCylinder_subset_comparison d m, closure_unitStack_subset_comparison d m⟩

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
