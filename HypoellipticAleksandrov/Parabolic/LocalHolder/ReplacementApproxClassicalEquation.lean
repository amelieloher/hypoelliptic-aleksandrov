module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxClassicalJet
public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxWeakEquationLimit
public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyShift
public import HypoellipticAleksandrov.Parabolic.ParabolicW12WeakDerivativeFamilyEquation

/-! # Identifying the weak limit equation with the actual classical equation

Local weak derivative uniqueness identifies every selected derivative with the literal
classical jet. Continuous residuals then vanish pointwise on open collars.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set
open scoped BigOperators Matrix.Norms.Elementwise

/-- A classical root satisfying the actual coherent weak-family equation solves it pointwise. -/
theorem classical_homogeneous_equation_of_weak_family {d L : ℕ}
    {U : Set (TimeVelocity d)} (hU : IsOpen U) (hL : 2 ≤ L)
    (u : TimeVelocity d → ℝ) (hu : IsScalarC12On u U)
    (A : CoefficientField d) (hA : IsSmoothCoefficient A)
    (E : ParabolicWeakDerivativeFamily d L U u)
    (hEq : homogeneousWeakFamilyResidual hL A E =ᵐ[timeVelocityVolumeOn U] 0) :
    ∀ z ∈ U, scalarTimeDerivative u z +
      matrixContraction (coefficientAt A z) (scalarSpatialHessian u z) = 0 := by
  classical
  intro z hz
  obtain ⟨V, hV, hzV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := z)) hU (singleton_subset_iff.mpr hz)
  have hsub : V ⊆ U := subset_closure.trans hVU
  let J := classicalLocalW12Jet u hu hV hVc hVU
  let D := (E.restrict hsub).truncate hL
  let F := J.toWeakDerivativeFamily hV
  have hall : ∀ᵐ y ∂timeVelocityVolumeOn V,
      ∀ beta, D.representative beta y = F.representative beta y := by
    apply ae_all_iff.mpr
    intro beta
    exact D.representative_ae_eq_of_root_ae hV F
      (Eventually.of_forall (fun _ => rfl)) beta
  have hEqV := hEq.filter_mono (ae_mono (Measure.restrict_mono_set volume hsub))
  have hFzero : homogeneousWeakFamilyResidual (le_refl 2) A F
      =ᵐ[timeVelocityVolumeOn V] 0 := by
    filter_upwards [hall, hEqV] with y hy hEy
    have hDy : homogeneousWeakFamilyResidual (le_refl 2) A D y = 0 := hEy
    simp only [homogeneousWeakFamilyResidual] at hDy ⊢
    simp_rw [hy] at hDy
    exact hDy
  let R (y : TimeVelocity d) := J.timeDeriv y +
    ∑ i, ∑ j, A y.1 y.2 i j * J.velocityHessian y j i
  have hRJ : (fun y => J.timeDeriv y +
      (∑ i, ∑ j, A y.1 y.2 i j * J.velocityHessian y j i) +
      (∑ j, (0 : PDE.Vec d) j * J.velocityGrad y j) + 0 * J.toFun y)
      =ᵐ[timeVelocityVolumeOn V] R :=
    Eventually.of_forall (fun _ => by simp [R])
  have hFR := J.toWeakDerivativeFamily_originalTimeEquation hV A
    (fun _ _ => 0) (fun _ _ => 0) (fun t y => R (t, y)) hRJ
  have hRzero : R =ᵐ[timeVelocityVolumeOn V] 0 := by
    have hFR' : homogeneousWeakFamilyResidual (le_refl 2) A F
        =ᵐ[timeVelocityVolumeOn V] R := by
      filter_upwards [hFR] with y hy
      simpa only [homogeneousWeakFamilyResidual, F, ParabolicDerivativeIndex.castLE,
        Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, Prod.mk.eta] using hy
    exact hFR'.symm.trans hFzero
  let Q (y : TimeVelocity d) := scalarTimeDerivative u y +
    matrixContraction (coefficientAt A y) (scalarSpatialHessian u y)
  have hQR : EqOn Q R V := by
    intro y hy
    have hs := scalarSpatialHessian_isSymm_of_c12 hu (hsub hy)
    have hentry (i j : Fin d) : scalarSpatialHessian u y j i =
        scalarSpatialHessian u y i j := congrArg (fun M : PDE.Mat d => M i j) hs
    simp only [Q, R, J, classicalLocalW12Jet, matrixContraction, coefficientAt, hentry]
  have hQzero : Q =ᵐ[timeVelocityVolumeOn V] 0 := by
    filter_upwards [hRzero, ae_restrict_mem hV.measurableSet] with y hy hyV
    exact (hQR hyV).trans hy
  have hQc : ContinuousOn Q V := by
    apply (hu.continuousOn_scalarTimeDerivative.mono hsub).add
    apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    have ha : Continuous (fun y : TimeVelocity d => A y.1 y.2 i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp hA.continuous)
    exact ha.continuousOn.mul (((continuous_apply j).comp_continuousOn
      ((continuous_apply i).comp_continuousOn
        hu.continuousOn_scalarSpatialHessian)).mono hsub)
  exact Measure.eqOn_open_of_ae_eq hQzero hV hQc continuousOn_const
    (hzV (mem_singleton z))

end HypoellipticAleksandrov.Parabolic.LocalHolder
