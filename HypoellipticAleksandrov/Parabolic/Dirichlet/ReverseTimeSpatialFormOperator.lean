module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormOperatorContinuity
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeBochner
public import Mathlib.Topology.Order.ProjIcc

/-!
# Clamped reverse-time spatial form operator

This compatibility module supplies the continuous all-real-time clamped
representative of the local reverse-time spatial form operator.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal RealInnerProductSpace Matrix.Norms.Elementwise MatrixOrder

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

section

variable {d : ℕ} {Ω : Set (PDE.Vec d)}
variable (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
variable (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
variable (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
  (scalarParabolicClosedCylinder r₀ r₁ Ω))
variable (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
  (scalarParabolicClosedCylinder r₀ r₁ Ω))
variable (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
  (scalarParabolicClosedCylinder r₀ r₁ Ω))
/-- The clamped all-time representative of the local reverse-time operator. -/
noncomputable def reverseTimeSpatialFormOperatorClamp :
    ℝ → H10HilbertGraph hΩ →L[ℝ] H10HilbertGraphDual hΩ := fun τ =>
  reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth
    (Set.projIcc 0 (r₁ - r₀) (sub_nonneg.mpr h₀₁.le) τ)

/-- The clamped representative is continuous in operator norm. -/
theorem continuous_reverseTimeSpatialFormOperatorClamp :
    Continuous (reverseTimeSpatialFormOperatorClamp r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth) := by
  change Continuous ((reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth) ∘ Set.projIcc 0 (r₁ - r₀) (sub_nonneg.mpr h₀₁.le))
  exact (continuous_reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth).comp continuous_projIcc

/-- On the literal reverse-time time measure, the clamped representative has
the exact form evaluation. -/
theorem ae_reverseTimeSpatialFormOperatorClamp_apply :
    ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀), ∀ u v : H10HilbertGraph hΩ,
      reverseTimeSpatialFormOperatorClamp r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth τ u v = reverseTimeSpatialForm hΩ r₁ τ a b c u v := by
  rw [reverseTimeVolume, reverseTimeOpenInterval]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
  intro u v
  have hproj : Set.projIcc 0 (r₁ - r₀) (sub_nonneg.mpr h₀₁.le) τ =
      ⟨τ, ⟨hτ.1.le, hτ.2.le⟩⟩ :=
    Set.projIcc_of_mem (sub_nonneg.mpr h₀₁.le) ⟨hτ.1.le, hτ.2.le⟩
  unfold reverseTimeSpatialFormOperatorClamp
  rw [hproj]
  exact reverseTimeSpatialFormOperator_apply r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth ⟨τ, ⟨hτ.1.le, hτ.2.le⟩⟩ u v

end


end HypoellipticAleksandrov.Parabolic.Dirichlet
