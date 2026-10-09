module

public import HypoellipticAleksandrov.Parabolic.NestedQuantitativeSmoothCutoffExistence
public import HypoellipticAleksandrov.Parabolic.ParabolicW12TimeReflection

/-!
# Original-time interior geometry

This file constructs the nested spatial cutoffs and strict reverse-time slabs
used to invoke the interior Caccioppoli theorem on an original-time cylinder.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- Compact containment of an original-time cylinder supplies the nested
spatial cutoffs and strict reverse-time slabs required by the interior
Caccioppoli theorem. -/
theorem exists_originalTimeInteriorCaccioppoliGeometry
    {d : ℕ} {Ω O : Set (PDE.Vec d)}
    (r₀ s₀ s₁ r₁ : ℝ)
    (hr₀s₀ : r₀ < s₀) (hs₀s₁ : s₀ < s₁) (hs₁r₁ : s₁ < r₁)
    (hΩ : IsOpen Ω)
    (hOcompact : IsCompact (closure O))
    (hOΩ : closure O ⊆ Ω) :
    ∃ (Kη : ℝ)
      (η : PDE.QuantitativeSmoothCutoff (closure O) Ω Kη)
      (Kχ : ℝ)
      (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
      (τ₀ τ₁ τ₂ τ₃ : ℝ),
      tsupport χ.toFun ⊆ Ω ∧
      τ₀ = (r₁ - s₁) / 2 ∧
      τ₁ = r₁ - s₁ ∧
      τ₂ = r₁ - s₀ ∧
      τ₃ = ((r₁ - s₀) + (r₁ - r₀)) / 2 ∧
      0 < τ₀ ∧ τ₀ < τ₁ ∧ τ₁ < τ₂ ∧
      τ₂ < τ₃ ∧ τ₃ < r₁ - r₀ := by
  obtain ⟨Kη, ⟨η, Kχ, χ⟩⟩ :=
    exists_nestedQuantitativeSmoothCutoffs_tsupport_subset hOcompact hΩ hOΩ
  refine ⟨Kη, η, Kχ, χ, (r₁ - s₁) / 2, r₁ - s₁, r₁ - s₀,
    ((r₁ - s₀) + (r₁ - r₀)) / 2, χ.tsupport_subset, rfl, rfl, rfl, rfl, ?_⟩
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Reflection at `r₁` carries the selected reverse-time interior cylinder
back to the literal original-time cylinder. -/
theorem reverseTimeMap_preimage_originalTimeInteriorCylinder
    {d : ℕ} (r₁ s₀ s₁ : ℝ) (O : Set (PDE.Vec d)) :
    reverseTimeMap r₁ ⁻¹'
        (Set.Ioo (r₁ - s₁) (r₁ - s₀) ×ˢ O) =
      Set.Ioo s₀ s₁ ×ˢ O := by
  ext z
  rcases z with ⟨r, y⟩
  simp only [Set.mem_preimage, reverseTimeMap_apply, Set.mem_prod, Set.mem_Ioo]
  constructor
  · rintro ⟨⟨hl, hu⟩, hy⟩
    exact ⟨⟨by linarith, by linarith⟩, hy⟩
  · rintro ⟨⟨hl, hu⟩, hy⟩
    exact ⟨⟨by linarith, by linarith⟩, hy⟩

end HypoellipticAleksandrov.Parabolic.Dirichlet
