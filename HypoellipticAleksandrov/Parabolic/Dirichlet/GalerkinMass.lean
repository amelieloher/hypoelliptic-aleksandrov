module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.GalerkinDense
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Finite Galerkin mass spaces and initial data

This module provides the finite-dimensional `L²` mass space associated with
the actual-test Galerkin spaces, its Gram matrix, and the lifted orthogonal
projection of an initial `L²` datum.  It makes no time-dependent, derivative,
or PDE assertion.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open scoped ENNReal RealInnerProductSpace

variable {d : ℕ} {Ω : Set (PDE.Vec d)}

/-- The `L²` image of the finite actual-test Galerkin space. -/
noncomputable def galerkinValueSpace
    (hΩ : IsOpen Ω) (N : ℕ) :
    Submodule ℝ (PDE.ScalarLp Ω (2 : ℝ≥0∞)) :=
  (galerkinSpace hΩ N).map (valueCLM hΩ).toLinearMap

/-- The finite Galerkin value space is finite dimensional. -/
noncomputable instance galerkinValueSpace_finiteDimensional
    (hΩ : IsOpen Ω) (N : ℕ) :
    FiniteDimensional ℝ (galerkinValueSpace hΩ N) := by
  unfold galerkinValueSpace
  infer_instance

/-- The finite Galerkin value space is complete. -/
noncomputable instance galerkinValueSpace_completeSpace
    (hΩ : IsOpen Ω) (N : ℕ) :
    CompleteSpace (galerkinValueSpace hΩ N) :=
  FiniteDimensional.complete ℝ (galerkinValueSpace hΩ N)

/-- The `L²` mass Gram matrix of the finite actual-test Galerkin basis. -/
noncomputable def galerkinMassGram
    (hΩ : IsOpen Ω) (N : ℕ) :
    Matrix
      (Fin (Module.finrank ℝ (galerkinSpace hΩ N)))
      (Fin (Module.finrank ℝ (galerkinSpace hΩ N))) ℝ :=
  Matrix.gram ℝ (fun i =>
    valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ))

/-- The finite `L²` mass Gram matrix is positive definite. -/
theorem galerkinMassGram_posDef
    (hΩ : IsOpen Ω) (N : ℕ) :
    (galerkinMassGram hΩ N).PosDef := by
  let E := galerkinSpace hΩ N
  let L : E →ₗ[ℝ] PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
    (valueCLM hΩ).toLinearMap.comp E.subtype
  have hL : Function.Injective L := by
    intro u v huv
    apply Subtype.ext
    exact valueCLM_injective hΩ huv
  have hli : LinearIndependent ℝ (L ∘ galerkinSpaceBasis hΩ N) :=
    (galerkinSpaceBasis hΩ N).linearIndependent.map' L
      (LinearMap.ker_eq_bot_of_injective hL)
  simpa only [galerkinMassGram, L, E, Function.comp_def, LinearMap.comp_apply, LinearMap.coe_comp,
    ContinuousLinearMap.coe_coe, Submodule.coe_subtype] using
    Matrix.posDef_gram_of_linearIndependent hli

/-- The finite `L²` mass Gram matrix is invertible, including at `N = 0`. -/
theorem isUnit_galerkinMassGram
    (hΩ : IsOpen Ω) (N : ℕ) :
    IsUnit (galerkinMassGram hΩ N) :=
  (galerkinMassGram_posDef hΩ N).isUnit

/-- A chosen preimage of the finite Galerkin value-space projection. -/
noncomputable def galerkinInitialProjectionPreimage
    (hΩ : IsOpen Ω) (N : ℕ)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    H10HilbertGraph hΩ :=
  Classical.choose <| Submodule.mem_map.mp
    (Submodule.starProjection_apply_mem (galerkinValueSpace hΩ N) initial)

/-- The chosen projection preimage lies in the finite Galerkin space. -/
theorem galerkinInitialProjectionPreimage_mem
    (hΩ : IsOpen Ω) (N : ℕ)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    galerkinInitialProjectionPreimage hΩ N initial ∈ galerkinSpace hΩ N := by
  exact (Classical.choose_spec <| Submodule.mem_map.mp
    (Submodule.starProjection_apply_mem (galerkinValueSpace hΩ N) initial)).1

private theorem value_galerkinInitialProjectionPreimage
    (hΩ : IsOpen Ω) (N : ℕ)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    valueCLM hΩ (galerkinInitialProjectionPreimage hΩ N initial) =
      (galerkinValueSpace hΩ N).starProjection initial := by
  exact (Classical.choose_spec <| Submodule.mem_map.mp
    (Submodule.starProjection_apply_mem (galerkinValueSpace hΩ N) initial)).2

/-- The lift to the finite Galerkin space of the `L²` orthogonal projection
of an initial datum. -/
noncomputable def galerkinInitialProjection
    (hΩ : IsOpen Ω) (N : ℕ)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    galerkinSpace hΩ N :=
  ⟨galerkinInitialProjectionPreimage hΩ N initial,
    galerkinInitialProjectionPreimage_mem hΩ N initial⟩

/-- Applying the spatial value map to the lifted initial datum recovers its
`L²` orthogonal projection onto the finite Galerkin value space. -/
theorem value_galerkinInitialProjection
    (hΩ : IsOpen Ω) (N : ℕ)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    valueCLM hΩ (galerkinInitialProjection hΩ N initial :
      H10HilbertGraph hΩ) =
    (galerkinValueSpace hΩ N).starProjection initial :=
  value_galerkinInitialProjectionPreimage hΩ N initial

/-- The finite Galerkin `L²` initial projection is contractive. -/
theorem norm_value_galerkinInitialProjection_le
    (hΩ : IsOpen Ω) (N : ℕ)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ‖valueCLM hΩ (galerkinInitialProjection hΩ N initial :
      H10HilbertGraph hΩ)‖ ≤ ‖initial‖ := by
  rw [value_galerkinInitialProjection]
  exact (galerkinValueSpace hΩ N).norm_starProjection_apply_le initial

end HypoellipticAleksandrov.Parabolic.Dirichlet
