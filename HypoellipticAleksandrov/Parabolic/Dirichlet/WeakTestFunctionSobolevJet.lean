module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolev

/-!
# Sobolev jets of bundled spatial test functions

This module records the almost-everywhere representative identities for the
canonical inclusion of bundled smooth compactly supported test functions into
the Hilbert realization of spatial `H¹₀`.
-/

@[expose] public section

open Filter
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The value cofunction of a bundled smooth compactly supported test
function agrees almost everywhere with its literal function after canonical
inclusion into the Hilbert `H¹₀` graph. -/
theorem ae_valueCLM_smoothCompactlySupportedH1HilbertGraph
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (ψ : PDE.WeakTestFunction Ω) :
    (fun y => valueCLM hΩ
      (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ) y)
      =ᵐ[PDE.volumeOn Ω] ψ := by
  change (fun y =>
    ((PDE.smoothCompactlySupportedW1pGraph
      (p := (2 : ℝ≥0∞)) hΩ ψ).1).1 y) =ᵐ[PDE.volumeOn Ω] ψ
  simpa only [PDE.smoothCompactlySupportedW1pGraph,
    PDE.W1pFunction.ofContDiff] using
    PDE.W1pFunction.coeFn_toW1pGraph_fst
      (PDE.W1pFunction.ofContDiff hΩ
        (ψ.contDiff.of_le (by simp)) ψ.hasCompactSupport (2 : ℝ≥0∞))

/-- Each gradient-coordinate cofunction of a bundled smooth compactly
supported test function agrees almost everywhere with its literal derivative
after canonical inclusion into the Hilbert `H¹₀` graph. -/
theorem ae_gradientCoordCLM_smoothCompactlySupportedH1HilbertGraph
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (ψ : PDE.WeakTestFunction Ω) (j : Fin d) :
    (fun y => gradientCLM hΩ
      (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ) y j)
      =ᵐ[PDE.volumeOn Ω] fun y => ψ.partialDeriv j y := by
  change (fun y =>
    ((PDE.smoothCompactlySupportedW1pGraph
      (p := (2 : ℝ≥0∞)) hΩ ψ).1).2 y j) =ᵐ[PDE.volumeOn Ω]
      fun y => ψ.partialDeriv j y
  simpa only [PDE.smoothCompactlySupportedW1pGraph,
    PDE.W1pFunction.ofContDiff, PDE.WeakTestFunction.partialDeriv] using
    PDE.W1pFunction.coeFn_toW1pGraph_snd_apply
      (PDE.W1pFunction.ofContDiff hΩ
        (ψ.contDiff.of_le (by simp)) ψ.hasCompactSupport (2 : ℝ≥0∞)) j

end HypoellipticAleksandrov.Parabolic.Dirichlet
