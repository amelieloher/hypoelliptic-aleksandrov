module

public import HypoellipticAleksandrov.Parabolic.WeakDerivatives
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.Compactness.Lindelof

/-!
# Gluing ambient C² representatives

Local ambient C² representatives belonging to one restricted-volume almost
everywhere class glue to a globally defined C² function on their carrier.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open Set MeasureTheory
open scoped Topology

noncomputable section

/-- Ambient `C²` local representatives in one restricted-volume AE class glue
to a `C²` function on the covered carrier, with their complete local germs and the
global AE class preserved. -/
theorem exists_contDiffOn_two_gluing
    {d : ℕ} {Q : Set (TimeVelocity d)}
    {w₀ : TimeVelocity d → ℝ}
    (V : Q → Set (TimeVelocity d))
    (v : Q → TimeVelocity d → ℝ)
    (hVopen : ∀ z, IsOpen (V z))
    (hzV : ∀ z, (z : TimeVelocity d) ∈ V z)
    (hVQ : ∀ z, V z ⊆ Q)
    (hvC2 : ∀ z, ContDiff ℝ 2 (v z))
    (hvAE : ∀ z,
      v z =ᵐ[timeVelocityVolumeOn (V z)] w₀) :
    ∃ w : TimeVelocity d → ℝ,
      ContDiffOn ℝ 2 w Q ∧
      w =ᵐ[timeVelocityVolumeOn Q] w₀ ∧
      ∀ z, Set.EqOn w (v z) (V z) := by
  classical
  have hcompat (x y : Q) : Set.EqOn (v x) (v y) (V x ∩ V y) := by
    have hx : v x =ᵐ[timeVelocityVolumeOn (V x ∩ V y)] w₀ :=
      (hvAE x).filter_mono
        (ae_mono (Measure.restrict_mono_set volume inter_subset_left))
    have hy : v y =ᵐ[timeVelocityVolumeOn (V x ∩ V y)] w₀ :=
      (hvAE y).filter_mono
        (ae_mono (Measure.restrict_mono_set volume inter_subset_right))
    have hxy : v x =ᵐ[timeVelocityVolumeOn (V x ∩ V y)] v y := hx.trans hy.symm
    exact Measure.eqOn_open_of_ae_eq hxy ((hVopen x).inter (hVopen y))
      (hvC2 x).continuous.continuousOn (hvC2 y).continuous.continuousOn
  let w : TimeVelocity d → ℝ := fun y => if hy : y ∈ Q then v ⟨y, hy⟩ y else 0
  have hwv (x : Q) : Set.EqOn w (v x) (V x) := by
    intro y hy
    have hyQ : y ∈ Q := hVQ x hy
    rw [show w y = v ⟨y, hyQ⟩ y by simp [w, hyQ]]
    exact hcompat ⟨y, hyQ⟩ x ⟨hzV ⟨y, hyQ⟩, hy⟩
  have hwC2 : ContDiffOn ℝ 2 w Q := by
    apply contDiffOn_of_locally_contDiffOn
    intro x hx
    refine ⟨V ⟨x, hx⟩, hVopen ⟨x, hx⟩, hzV ⟨x, hx⟩, ?_⟩
    exact (hvC2 ⟨x, hx⟩).contDiffOn.congr_mono
      (fun y hy => hwv ⟨x, hx⟩ hy.2) inter_subset_right
  obtain ⟨t, htcount, hQcover⟩ :=
    (HereditarilyLindelofSpace.isLindelof Q).elim_nhds_subcover'
      (fun x hx => V ⟨x, hx⟩)
      (fun x hx => (hVopen ⟨x, hx⟩).mem_nhds (hzV ⟨x, hx⟩))
  have hunionQ : (⋃ x ∈ t, V x) = Q := by
    apply Set.Subset.antisymm
    · exact iUnion₂_subset fun x _ => hVQ x
    · exact hQcover
  have hwAEunion : w =ᵐ[timeVelocityVolumeOn (⋃ x ∈ t, V x)] w₀ := by
    rw [timeVelocityVolumeOn, MeasureTheory.ae_eq_restrict_biUnion_iff V htcount]
    intro x hx
    have hwvx : w =ᵐ[timeVelocityVolumeOn (V x)] v x := by
      filter_upwards [ae_restrict_mem (hVopen x).measurableSet] with y hy
      exact hwv x hy
    exact hwvx.trans (hvAE x)
  refine ⟨w, hwC2, ?_, hwv⟩
  simpa [hunionQ] using hwAEunion

end

end HypoellipticAleksandrov.Parabolic
