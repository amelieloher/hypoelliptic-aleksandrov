module

public import HypoellipticAleksandrov.Parabolic.QuantitativeSmoothCutoffExistence

/-!
# Nested quantitative smooth cutoffs

This module iterates quantitative smooth-cutoff existence to obtain a second
cutoff whose plateau contains the first cutoff's topological support.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

/-- A compact subset of an open velocity set admits two nested quantitative
smooth cutoffs: the second equals one on the first cutoff's topological
support, and both supports lie in the original open set. -/
theorem exists_nestedQuantitativeSmoothCutoffs_tsupport_subset
    {d : ℕ} {E Ω : Set (PDE.Vec d)}
    (hE : IsCompact E) (hΩ : IsOpen Ω) (hEΩ : E ⊆ Ω) :
    ∃ Kη : ℝ, Nonempty
      (Σ η : PDE.QuantitativeSmoothCutoff E Ω Kη,
        Σ Kχ : ℝ,
          PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ) := by
  obtain ⟨Kη, ⟨η⟩⟩ :=
    exists_quantitativeSmoothCutoff_tsupport_subset hE hΩ hEΩ
  obtain ⟨Kχ, ⟨χ⟩⟩ :=
    exists_quantitativeSmoothCutoff_tsupport_subset
      η.hasCompactSupport hΩ η.tsupport_subset
  exact ⟨Kη, ⟨η, Kχ, χ⟩⟩

end HypoellipticAleksandrov.Parabolic
