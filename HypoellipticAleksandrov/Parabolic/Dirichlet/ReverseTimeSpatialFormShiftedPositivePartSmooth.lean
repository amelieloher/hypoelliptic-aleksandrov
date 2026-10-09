module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormBounds
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormShiftedPositivePart

/-!
# Smooth-data shifted positive-part spatial-form inequality

This file derives the scalar-product integrability required by the literal
fixed-slice theorem from closed-cylinder smoothness and boundedness of the
spatial domain.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- Smoothness of the scalar coefficient on a bounded closed cylinder supplies
the fixed-slice shifted positive-part spatial-form inequality. -/
theorem reverseTimeSpatialForm_apply_shiftedPositivePart_ge_of_smoothOnNeighborhood
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcNonpos : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0)
    (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
    (u : H10HilbertGraph hΩ) (k : ℝ≥0) :
    reverseTimeSpatialForm hΩ r₁ τ a b c u (h10ShiftedPositivePart hΩ u k) ≥
      reverseTimeSpatialForm hΩ r₁ τ a b c
        (h10ShiftedPositivePart hΩ u k) (h10ShiftedPositivePart hΩ u k) := by
  let q := fun y : PDE.Vec d => reverseTimeScalarCoefficient r₁ c τ y
  let U := valueCLM hΩ u
  let W := valueCLM hΩ (h10ShiftedPositivePart hΩ u k)
  obtain ⟨C, hC, hCbound⟩ :=
    exists_reverseTimeScalarCoefficient_bound_of_smoothOnNeighborhood
      r₀ r₁ hΩbounded c hcSmooth
  have hqMeas : AEStronglyMeasurable q (PDE.volumeOn Ω) := by
    exact (continuousOn_reverseTimeScalarCoefficient_slice_of_smoothOnNeighborhood
      r₀ r₁ τ c hcSmooth hτ).aestronglyMeasurable hΩ.measurableSet
  have hqBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖q y‖ ≤ C := by
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with y hy
    simpa only [q, Real.norm_eq_abs] using hCbound τ hτ y hy
  have hScalarSquare : Integrable (fun y => q y * W y * W y) (PDE.volumeOn Ω) := by
    refine (L2.integrable_inner (𝕜 := ℝ)
      (scalarL2Multiplier q hqMeas C hC hqBound W) W).congr ?_
    filter_upwards [scalarL2Multiplier_apply_ae q hqMeas C hC hqBound W] with y hy
    rw [hy]
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  have hScalarCross : Integrable (fun y => q y * U y * W y) (PDE.volumeOn Ω) := by
    refine (L2.integrable_inner (𝕜 := ℝ)
      (scalarL2Multiplier q hqMeas C hC hqBound U) W).congr ?_
    filter_upwards [scalarL2Multiplier_apply_ae q hqMeas C hC hqBound U] with y hy
    rw [hy]
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  have hScalarNonpos : ∀ᵐ y ∂PDE.volumeOn Ω, q y ≤ 0 := by
    have htime : r₀ ≤ r₁ - τ ∧ r₁ - τ ≤ r₁ := by
      constructor <;> linarith [h₀₁, hτ.1, hτ.2]
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with y hy
    simpa only [q, reverseTimeScalarCoefficient_apply] using
      hcNonpos (r₁ - τ, y) ⟨htime, subset_closure hy⟩
  exact reverseTimeSpatialForm_apply_shiftedPositivePart_ge hΩ r₁ τ a b c u k
    hScalarNonpos (by simpa only [q, W] using hScalarSquare)
    (by simpa only [q, U, W] using hScalarCross)

end HypoellipticAleksandrov.Parabolic.Dirichlet
