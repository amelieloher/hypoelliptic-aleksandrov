module

public import HypoellipticAleksandrov.Parabolic.ScalarClassical
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Order.Compact

/-! # Auxiliary compact product collars

These carriers are used only for local energy and regularity estimates. The prescribed
Euclidean ball and its boundary remain the replacement domain.
-/

@[expose] public section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Set

/-- A finite time interval and compact spatial closure give compact product closure. -/
theorem isCompact_closure_local_product {d : ℕ} (a T : ℝ)
    {O : Set (PDE.Vec d)} (hOc : IsCompact (closure O)) :
    IsCompact (closure (Ioo a T ×ˢ O)) := by
  rw [closure_prod_eq]
  exact (isCompact_Icc.of_isClosed_subset isClosed_closure
    (closure_minimal Ioo_subset_Icc_self isClosed_Icc)).prod hOc

/-- Strict temporal margins and spatial compact containment give product compact containment. -/
theorem closure_local_product_subset {d : ℕ} {a b c e : ℝ}
    (hac : a < c) (heb : e < b) {O Ω : Set (PDE.Vec d)} (hOΩ : closure O ⊆ Ω) :
    closure (Ioo c e ×ˢ O) ⊆ Ioo a b ×ˢ Ω := by
  rw [closure_prod_eq]
  intro z hz
  have ht : z.1 ∈ Icc c e :=
    closure_minimal Ioo_subset_Icc_self isClosed_Icc hz.1
  exact ⟨⟨hac.trans_le ht.1, ht.2.trans_lt heb⟩, hOΩ hz.2⟩

/-- Every point of an open spatial carrier has three nested compactly contained collars. -/
theorem exists_three_nested_local_spatial_collars {d : ℕ}
    (Ω : Set (PDE.Vec d)) (hΩ : IsOpen Ω) (x : PDE.Vec d) (hx : x ∈ Ω) :
    ∃ O₀ O₁ O₂ : Set (PDE.Vec d),
      IsOpen O₀ ∧ IsCompact (closure O₀) ∧ closure O₀ ⊆ Ω ∧
      IsOpen O₁ ∧ IsCompact (closure O₁) ∧ closure O₁ ⊆ O₀ ∧
      IsOpen O₂ ∧ IsCompact (closure O₂) ∧ closure O₂ ⊆ O₁ ∧ x ∈ O₂ := by
  obtain ⟨O₀, hO₀, hxO₀, hO₀Ω, hO₀c⟩ :=
    exists_open_between_and_isCompact_closure (isCompact_singleton (x := x)) hΩ
      (singleton_subset_iff.mpr hx)
  obtain ⟨O₁, hO₁, hxO₁, hO₁O₀, hO₁c⟩ :=
    exists_open_between_and_isCompact_closure (isCompact_singleton (x := x)) hO₀ hxO₀
  obtain ⟨O₂, hO₂, hxO₂, hO₂O₁, hO₂c⟩ :=
    exists_open_between_and_isCompact_closure (isCompact_singleton (x := x)) hO₁ hxO₁
  exact ⟨O₀, O₁, O₂, hO₀, hO₀c, hO₀Ω, hO₁, hO₁c, hO₁O₀,
    hO₂, hO₂c, hO₂O₁, hxO₂ (mem_singleton x)⟩

end HypoellipticAleksandrov.Parabolic.LocalHolder
