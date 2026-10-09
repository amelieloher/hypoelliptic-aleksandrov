module

public import HypoellipticAleksandrov.Coefficients.Ellipticity
public import HypoellipticAleksandrov.Parabolic.C2ToScalarC12
public import HypoellipticAleksandrov.Parabolic.SpatialCoordinateDerivatives

/-! # Coefficient derivative bounds on compact collars

Smoothness and compactness give one bound for every coefficient derivative, with no
choice depending on the replacement solution.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Set
open scoped Matrix.Norms.Elementwise

/-- All first spatial coefficient derivatives have a common bound on a compact carrier. -/
theorem exists_compact_coefficient_spatial_derivative_bound {d : ℕ}
    (A : CoefficientField d) (hA : IsSmoothCoefficient A)
    (K : Set (TimeVelocity d)) (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ K, ∀ i j k,
      |spatialPartial k (fun y => A z.1 y i j) z.2| ≤ M := by
  let D (z : TimeVelocity d) (k i j : Fin d) :=
    spatialPartial k (fun y => A z.1 y i j) z.2
  have hD : Continuous D := by
    apply continuous_pi
    intro k
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    have hcoeff : ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => A z.1 z.2 i j) :=
      (contDiff_apply ℝ ℝ j).comp ((contDiff_apply ℝ (Fin d → ℝ) i).comp hA)
    have hc12 := isScalarC12On_of_contDiff_two (hcoeff.of_le (by simp)) univ
    exact (continuous_apply k).comp
      (continuousOn_univ.mp hc12.continuousOn_scalarSpatialGradient)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hD.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro z hz i j k
  calc
    _ = ‖D z k i j‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖D z k i‖ := norm_le_pi_norm _ j
    _ ≤ ‖D z k‖ := norm_le_pi_norm _ i
    _ ≤ ‖D z‖ := norm_le_pi_norm _ k
    _ ≤ C := hC z hz
    _ ≤ max C 0 := le_max_left _ _

end HypoellipticAleksandrov.Parabolic.LocalHolder
