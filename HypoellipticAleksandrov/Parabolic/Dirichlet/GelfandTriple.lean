module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolevExtensionality
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialL2Density
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# The spatial Gelfand triple

This module realizes the dual side of the spatial Gelfand triple
`H¹₀(Ω) → L²(Ω) → (H¹₀(Ω))^*`.  It uses the continuous, injective spatial
value map and its dense-range theorem, together with the real Hilbert-space pairing.

No coercivity, time-dependent, Bochner, or PDE assertion is made here.
-/

@[expose] public section

open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω : Set (PDE.Vec d)}

/-- The `H⁻¹` carrier dual to the spatial Hilbert realization of `H¹₀(Ω)`. -/
abbrev H10HilbertGraphDual (hΩ : IsOpen Ω) : Type _ :=
  StrongDual ℝ (H10HilbertGraph hΩ)

/-- The canonical continuous pivot embedding from spatial `L²` into the dual
of the spatial Hilbert realization of `H¹₀`. -/
noncomputable def scalarLpToH10HilbertGraphDual
    (hΩ : IsOpen Ω) :
    PDE.ScalarLp Ω (2 : ℝ≥0∞) →L[ℝ] H10HilbertGraphDual hΩ :=
  ContinuousLinearMap.toSesqForm (valueCLM hΩ)

@[simp]
theorem scalarLpToH10HilbertGraphDual_apply
    (hΩ : IsOpen Ω) (h : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (v : H10HilbertGraph hΩ) :
    scalarLpToH10HilbertGraphDual hΩ h v = inner ℝ (valueCLM hΩ v) h := by
  change inner ℝ h (valueCLM hΩ v) = inner ℝ (valueCLM hΩ v) h
  exact real_inner_comm _ _

/-- The pivot embedding is bounded by the operator norm of the spatial value map. -/
theorem norm_scalarLpToH10HilbertGraphDual_apply_le
    (hΩ : IsOpen Ω) (h : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ‖scalarLpToH10HilbertGraphDual hΩ h‖ ≤ ‖valueCLM hΩ‖ * ‖h‖ := by
  exact ContinuousLinearMap.toSesqForm_apply_norm_le

/-- Dense range of the spatial value map makes the pivot embedding injective. -/
theorem scalarLpToH10HilbertGraphDual_injective
    (hΩ : IsOpen Ω) :
    Function.Injective (scalarLpToH10HilbertGraphDual hΩ) := by
  intro h k hhk
  have h_dense : Dense
      ((LinearMap.range (valueCLM hΩ).toLinearMap :
        Submodule ℝ (PDE.ScalarLp Ω (2 : ℝ≥0∞))) :
        Set (PDE.ScalarLp Ω (2 : ℝ≥0∞))) := by
    simpa only [LinearMap.coe_range, ContinuousLinearMap.coe_coe, DenseRange] using
      valueCLM_denseRange hΩ
  apply h_dense.eq_of_inner_right (𝕜 := ℝ)
  intro x hx
  obtain ⟨v, rfl⟩ := hx
  have h_eval :
      scalarLpToH10HilbertGraphDual hΩ h v =
        scalarLpToH10HilbertGraphDual hΩ k v :=
    congrArg (fun ℓ : H10HilbertGraphDual hΩ => ℓ v) hhk
  simpa only [scalarLpToH10HilbertGraphDual_apply, ContinuousLinearMap.coe_coe] using h_eval

end HypoellipticAleksandrov.Parabolic.Dirichlet
