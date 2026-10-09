module

public import HypoellipticAleksandrov.Parabolic.HarnackUnitCylinder.TimeWeakDerivative
public import HypoellipticAleksandrov.Parabolic.HarnackUnitCylinder.SpatialWeakDerivatives
public import HypoellipticAleksandrov.Parabolic.HarnackUnitCylinder.CompactLp
public import HypoellipticAleksandrov.Parabolic.WeakEquation

/-! # Classical anisotropic solutions supply local weak parabolic jets -/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open Set MeasureTheory
open scoped ENNReal

/-- Every finite compact collar of a C¹,² solution supplies its exact scalar weak jet. -/
theorem IsScalarC12On.isWeakParabolicEquationLoc
    {d : ℕ} {U : Set (TimeVelocity d)} {B : CoefficientField d}
    {u : TimeVelocity d → ℝ} (hU : IsOpen U)
    (hu : IsScalarC12On u U)
    (heq : ∀ z ∈ U, scalarTimeDerivative u z =
      matrixContraction (coefficientAt B z) (scalarSpatialHessian u z))
    (p : ℝ≥0∞) : IsWeakParabolicEquationLoc B U p u := by
  intro V hV hcompact hVU
  have hsub : V ⊆ U := subset_closure.trans hVU
  have hlocal : IsScalarC12On u V := by
    rcases hu with ⟨hv, ht, hs, hdt, hdg, hdh⟩
    exact ⟨hv.mono hsub, fun z hz => ht z (hsub hz), fun z hz => hs z (hsub hz),
      hdt.mono hsub, hdg.mono hsub, hdh.mono hsub⟩
  let w : ParabolicW12Function d V p :=
    { toFun := u
      timeDeriv := scalarTimeDerivative u
      velocityGrad := scalarSpatialGradient u
      velocityHessian := scalarSpatialHessian u
      memLp := memLp_on_of_continuousOn_compact_closure
        hu.continuousOn hV hcompact hVU p
      timeDeriv_memLp := memLp_on_of_continuousOn_compact_closure
        hu.continuousOn_scalarTimeDerivative hV hcompact hVU p
      velocityGrad_memLp := fun i => memLp_on_of_continuousOn_compact_closure
        ((continuous_apply i).comp_continuousOn hu.continuousOn_scalarSpatialGradient)
        hV hcompact hVU p
      velocityHessian_memLp := fun i j => memLp_on_of_continuousOn_compact_closure
        ((continuous_apply j).comp_continuousOn
          ((continuous_apply i).comp_continuousOn hu.continuousOn_scalarSpatialHessian))
        hV hcompact hVU p
      hasWeakTimeDeriv := IsScalarC12On.hasWeakTimeDerivOn hV hlocal
      hasWeakVelocityPartialDeriv := IsScalarC12On.hasWeakVelocityPartialDerivOn hV hlocal
      hasWeakVelocitySecondPartialDeriv :=
        IsScalarC12On.hasWeakVelocitySecondPartialDerivOn hV hlocal }
  refine ⟨w, Filter.EventuallyEq.rfl, ?_⟩
  change ∀ᵐ z ∂timeVelocityVolumeOn V,
    scalarTimeDerivative u z -
      matrixContraction (coefficientAt B z) (scalarSpatialHessian u z) = 0
  exact ae_restrict_of_forall_mem hV.measurableSet (fun z hz =>
    sub_eq_zero.mpr (heq z (hsub hz)))

end HypoellipticAleksandrov.Parabolic
