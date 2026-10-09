module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertTraces

/-!
# Algebra of canonical reverse-time Hilbert representatives

This module records algebraic identities for the canonical continuous
spatial-`L²` representatives of reverse-time Gelfand curves.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The canonical Hilbert representative of a difference is the difference
of the canonical representatives whenever the corresponding weak derivative
data are available. -/
theorem reverseTimeHilbertRepresentative_sub_eq
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hdu : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (v : ReverseTimeL2V hΩ T) (k : ReverseTimeL2VStar hΩ T)
    (hdv : HasGelfandWeakTimeDerivative hΩ T hT v k)
    (hdiff : HasGelfandWeakTimeDerivative hΩ T hT (u - v) (g - k)) :
    reverseTimeHilbertRepresentative hΩ T hT (u - v) (g - k) hdiff =
      reverseTimeHilbertRepresentative hΩ T hT u g hdu -
        reverseTimeHilbertRepresentative hΩ T hT v k hdv := by
  obtain ⟨hU, _⟩ := reverseTimeHilbertRepresentative_spec hΩ T hT u g hdu
  obtain ⟨hV, _⟩ := reverseTimeHilbertRepresentative_spec hΩ T hT v k hdv
  obtain ⟨hW, _⟩ := reverseTimeHilbertRepresentative_spec hΩ T hT (u - v) (g - k) hdiff
  apply ReverseTimeHilbertRepresentativeAgrees.unique hW hT
  filter_upwards [hU, hV, Lp.coeFn_sub u v] with τ hUτ hVτ huv
  intro hτ
  let hτcc : τ ∈ Set.Icc 0 T := ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩
  change
    (reverseTimeHilbertRepresentative hΩ T hT u g hdu -
      reverseTimeHilbertRepresentative hΩ T hT v k hdv) ⟨τ, hτcc⟩ =
      valueCLM hΩ ((u - v) τ)
  change reverseTimeHilbertRepresentative hΩ T hT u g hdu ⟨τ, hτcc⟩ -
      reverseTimeHilbertRepresentative hΩ T hT v k hdv ⟨τ, hτcc⟩ =
        valueCLM hΩ ((u - v) τ)
  rw [hUτ hτ, hVτ hτ, huv]
  exact (valueCLM hΩ).map_sub _ _

end HypoellipticAleksandrov.Parabolic.Dirichlet
