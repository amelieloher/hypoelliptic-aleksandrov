module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometryTopology
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Setting
import Mathlib.Tactic

/-! # Compactness and the exact closed union of kinetic Holder neighbourhoods -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set

/-- A positive affine map takes the closed unit cylinder onto the physical cylinder closure. -/
theorem kineticAffine_image_closedUnitCylinder {d : ℕ} (P : KineticPoint d) {r : ℝ}
    (hr : 0 < r) :
    kineticAffine P r '' closure (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1) =
      closure (backwardCylinder P r) := by
  have hc := (kineticAffineHomeomorph P r hr.ne').image_closure
    (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1)
  change kineticAffine P r '' closure _ = closure (kineticAffine P r '' _) at hc
  rw [kineticAffine_image_unitCylinder P hr] at hc
  exact hc

/-- The affine cylinder map is jointly continuous in its center and reference point. -/
theorem continuous_kineticAffine_pair (d : ℕ) (r : ℝ) :
    Continuous (fun z : KineticPoint d × KineticPoint d => kineticAffine z.1 r z.2) := by
  have ht1 := (continuous_time (d := d)).comp
    (continuous_fst (X := KineticPoint d) (Y := KineticPoint d))
  have ht2 := (continuous_time (d := d)).comp
    (continuous_snd (X := KineticPoint d) (Y := KineticPoint d))
  have hx1 := (continuous_position (d := d)).comp
    (continuous_fst (X := KineticPoint d) (Y := KineticPoint d))
  have hx2 := (continuous_position (d := d)).comp
    (continuous_snd (X := KineticPoint d) (Y := KineticPoint d))
  have hv1 := (continuous_velocity (d := d)).comp
    (continuous_fst (X := KineticPoint d) (Y := KineticPoint d))
  have hv2 := (continuous_velocity (d := d)).comp
    (continuous_snd (X := KineticPoint d) (Y := KineticPoint d))
  exact KineticPoint.continuous_mk
    (ht1.add (ht2.const_mul (r ^ 2)))
    ((hx1.add (hx2.const_smul (r ^ 3))).add ((ht2.const_mul (r ^ 2)).smul hv1))
    (hv1.add (hv2.const_smul r))

/-- Compact centers and one compact model cylinder give the exact compact neighbourhood closure. -/
theorem holder_neighbourhood_compact {d : ℕ}
    (K : Set (KineticPoint d)) (hK : IsCompact K) (R0 : ℝ) (hR0 : 0 < R0) :
    closure (holderNeighbourhood R0 K) =
        ⋃ P ∈ K, closure (backwardCylinder P (2 * R0)) ∧
      IsCompact (closure (holderNeighbourhood R0 K)) := by
  let r := 2 * R0
  have hr : 0 < r := by dsimp only [r]; positivity
  let B := closure (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1)
  let U := ⋃ P ∈ K, closure (backwardCylinder P r)
  have himage : (fun z : KineticPoint d × KineticPoint d => kineticAffine z.1 r z.2) ''
      (K ×ˢ B) = U := by
    ext Z
    simp only [mem_image, mem_prod, mem_iUnion, U]
    constructor
    · rintro ⟨⟨P, Q⟩, ⟨hP, hQ⟩, rfl⟩
      exact ⟨P, hP, kineticAffine_image_closedUnitCylinder P hr ▸ ⟨Q, hQ, rfl⟩⟩
    · rintro ⟨P, hP, hZ⟩
      rw [← kineticAffine_image_closedUnitCylinder P hr] at hZ
      obtain ⟨Q, hQ, heq⟩ := hZ
      exact ⟨(P, Q), ⟨hP, hQ⟩, heq⟩
  have hUc : IsCompact U := by
    rw [← himage]
    exact (hK.prod (isCompact_closure_backwardCylinder _ 1 zero_lt_one)).image
      (continuous_kineticAffine_pair d r)
  have hNsub : holderNeighbourhood R0 K ⊆ U := by
    intro Z hZ
    simp only [holderNeighbourhood, mem_iUnion] at hZ
    obtain ⟨P, hP, hZ⟩ := hZ
    exact mem_iUnion.mpr ⟨P, mem_iUnion.mpr ⟨hP, subset_closure hZ⟩⟩
  have hclosed : closure (holderNeighbourhood R0 K) = U := by
    apply Subset.antisymm (closure_minimal hNsub hUc.isClosed)
    intro Z hZ
    simp only [U, mem_iUnion] at hZ
    obtain ⟨P, hP, hZ⟩ := hZ
    have hs : backwardCylinder P r ⊆ holderNeighbourhood R0 K := by
      intro Y hY
      exact mem_iUnion.mpr ⟨P, mem_iUnion.mpr ⟨hP, hY⟩⟩
    exact closure_mono hs hZ
  exact ⟨hclosed, hclosed ▸ hUc⟩

end HypoellipticAleksandrov.KineticAleksandrov.Holder
