module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialCoordinateShiftCarrierGeometry
public import HypoellipticAleksandrov.Parabolic.QuantitativeSmoothCutoffExistence

/-!
# Intermediate spatial cutoff and signed collar

This module packages the compact-open separation, quantitative spatial cutoff,
and uniform signed coordinate-shift collar used for interior spatial
difference quotients.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

/-- Between a compactly contained spatial set and its open ambient set, one can
choose an intermediate open set, a quantitative plateau cutoff, and a positive
signed coordinate-shift radius whose full carrier remains in the ambient set. -/
theorem exists_intermediateSpatialCutoff_signedCollar
    {d : ℕ} (O₀ O₁ : Set (PDE.Vec d))
    (hO₀ : IsOpen O₀)
    (hO₁compact : IsCompact (closure O₁))
    (hO₁O₀ : closure O₁ ⊆ O₀) :
    ∃ (O₂ : Set (PDE.Vec d)) (Keta : ℝ)
      (_η : PDE.QuantitativeSmoothCutoff (closure O₁) O₂ Keta)
      (δ : ℝ),
      IsOpen O₂ ∧
      IsCompact (closure O₂) ∧
      closure O₁ ⊆ O₂ ∧
      closure O₂ ⊆ O₀ ∧
      0 ≤ Keta ∧
      0 < δ ∧
      HypoellipticAleksandrov.Parabolic.Dirichlet.spatialCoordinateShiftCarrier
        (closure O₂) δ ⊆ O₀ := by
  obtain ⟨O₂, hO₂open, hO₁O₂, hO₂O₀, hO₂compact⟩ :=
    exists_open_between_and_isCompact_closure hO₁compact hO₀ hO₁O₀
  obtain ⟨Keta, ⟨η⟩⟩ :=
    exists_quantitativeSmoothCutoff_tsupport_subset
      hO₁compact hO₂open hO₁O₂
  have hKeta : 0 ≤ Keta :=
    (PDE.vecEuclideanNorm_nonneg (PDE.classicalGradient η.toFun 0)).trans
      (η.gradient_bound 0)
  obtain ⟨δ, hδ, hcarrier⟩ :=
    Dirichlet.IsCompact.exists_spatialCoordinateShiftCarrier_subset_open
      hO₂compact hO₀ hO₂O₀
  exact ⟨O₂, Keta, η, δ, hO₂open, hO₂compact, hO₁O₂, hO₂O₀,
    hKeta, hδ, hcarrier⟩

end HypoellipticAleksandrov.Parabolic
