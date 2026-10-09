module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxLimitRegularity
public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxClassicalEquation

/-! # Classical homogeneous limits of controlled approximation families

The common derivative subsequence simultaneously supplies classical regularity and
preserves the homogeneous equation. No regularity theorem is used.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set
open scoped Topology

/-- Controlled higher families and strong root convergence give the actual classical equation. -/
theorem scalarC12_homogeneous_of_strongL2_limit {d : ℕ}
    (U : Set (TimeVelocity d)) (hU : IsOpen U)
    (A : CoefficientField d) (hA : IsSmoothCoefficient A)
    (M : ℝ) (hAb : ∀ z ∈ U, ∀ i j, |A z.1 z.2 i j| ≤ M)
    (u : ℕ → TimeVelocity d → ℝ)
    (D : ∀ n, ParabolicWeakDerivativeFamily d (2 * (d + 4)) U (u n))
    (hu : ∀ n, ParabolicMemLpOn U 2 (u n))
    (v : TimeVelocity d → ℝ) (hv : ParabolicMemLpOn U 2 v)
    (hvcont : ContinuousOn v U)
    (hstrong : Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 (hv.toLp v)))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n, (D n).squaredL2Norm ≤ C ^ 2)
    (hzero : ∀ n, homogeneousWeakFamilyResidual (by omega : 2 ≤ 2 * (d + 4)) A (D n)
      =ᵐ[timeVelocityVolumeOn U] 0) :
    IsScalarC12On v U ∧ ∀ z ∈ U, scalarTimeDerivative v z +
      matrixContraction (coefficientAt A z) (scalarSpatialHessian v z) = 0 := by
  obtain ⟨E, σ, hσ, htest⟩ := exists_weakDerivativeFamily_testing_limit_of_tendsto_toLp
    U u D hu v hv hstrong C hC hb
  have hv12 := scalarC12On_of_continuousOn_higher_weak_family hU hvcont E
  have hEq := homogeneousWeakFamilyResidual_ae_eq_zero_of_testing_limit
    U hU (by omega : 2 ≤ 2 * (d + 4)) A hA M hAb
    (fun n => u (σ n)) (fun n => D (σ n)) v E (fun n => hzero (σ n)) htest
  exact ⟨hv12, classical_homogeneous_equation_of_weak_family hU
    (by omega : 2 ≤ 2 * (d + 4)) v hv12 A hA E hEq⟩

end HypoellipticAleksandrov.Parabolic.LocalHolder
