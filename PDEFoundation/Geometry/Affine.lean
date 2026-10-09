module

public import PDEFoundation.Ambient.Basic
public import Mathlib.Data.Set.Basic

/-!
# Affine set operations on native vectors

Pure set-theoretic translation identities. Measure-preserving and integral
transport statements belong in the later measure layer.
-/

@[expose] public section

namespace PDE

/-- Translate a set of native vectors by `z`. -/
def translateSet {d : ℕ} (z : Vec d) (U : Set (Vec d)) : Set (Vec d) :=
  {x | ∃ y ∈ U, x = y + z}

theorem mem_translateSet_iff_sub_mem {d : ℕ}
    {z x : Vec d} {U : Set (Vec d)} :
    x ∈ translateSet z U ↔ x - z ∈ U := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [sub_eq_add_neg, add_assoc]
  · intro hx
    refine ⟨x - z, hx, ?_⟩
    ext i
    simp [sub_eq_add_neg, add_assoc]

theorem preimage_subRight_eq_translateSet {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) :
    (fun x : Vec d => x - z) ⁻¹' U = translateSet z U := by
  ext x
  simp [mem_translateSet_iff_sub_mem]

theorem preimage_addNeg_eq_translateSet {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) :
    (fun x : Vec d => x + -z) ⁻¹' U = translateSet z U := by
  ext x
  simp [mem_translateSet_iff_sub_mem, sub_eq_add_neg]

theorem preimage_addRight_translateSet_eq {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) :
    (fun x : Vec d => x + z) ⁻¹' translateSet z U = U := by
  ext x
  simp [mem_translateSet_iff_sub_mem, sub_eq_add_neg, add_assoc]

theorem image_addRight_eq_translateSet {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) :
    (fun x : Vec d => x + z) '' U = translateSet z U := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem translateSet_inter {d : ℕ}
    (z : Vec d) (U V : Set (Vec d)) :
    translateSet z (U ∩ V) = translateSet z U ∩ translateSet z V := by
  ext y
  simp [mem_translateSet_iff_sub_mem]

@[simp]
theorem translateSet_zero {d : ℕ} (U : Set (Vec d)) :
    translateSet (0 : Vec d) U = U := by
  ext x
  simp [translateSet]

theorem translateSet_translateSet {d : ℕ}
    (z w : Vec d) (U : Set (Vec d)) :
    translateSet w (translateSet z U) = translateSet (z + w) U := by
  ext x
  constructor
  · rintro ⟨y, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, by simp [add_assoc]⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u + z, ⟨u, hu, rfl⟩, by simp [add_assoc]⟩

end PDE
