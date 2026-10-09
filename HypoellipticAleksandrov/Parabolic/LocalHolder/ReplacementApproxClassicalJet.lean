module

public import HypoellipticAleksandrov.Parabolic.HarnackUnitCylinder.ClassicalWeakEquation
public import HypoellipticAleksandrov.Parabolic.ParabolicW12WeakDerivativeFamily

/-! # Literal local weak jets of classical replacement functions

Compact containment supplies integrability without assuming bounds on derivatives. The
stored weak derivatives are exactly the classical scalar derivatives.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter Set MeasureTheory
open scoped BigOperators

/-- Restricting a supplied classical jet preserves its actual derivative functions. -/
theorem scalarC12On_mono {d : ℕ} {U V : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ} (hu : IsScalarC12On u U) (hVU : V ⊆ U) :
    IsScalarC12On u V := by
  rcases hu with ⟨hv, ht, hs, hdt, hdg, hdh⟩
  exact ⟨hv.mono hVU, fun z hz => ht z (hVU hz), fun z hz => hs z (hVU hz),
    hdt.mono hVU, hdg.mono hVU, hdh.mono hVU⟩

/-- A compact collar carries the literal classical weak `W¹,²₂` jet. -/
def classicalLocalW12Jet {d : ℕ} {U V : Set (TimeVelocity d)}
    (u : TimeVelocity d → ℝ) (hu : IsScalarC12On u U)
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVU : closure V ⊆ U) :
    ParabolicW12Function d V 2 :=
  { toFun := u
    timeDeriv := scalarTimeDerivative u
    velocityGrad := scalarSpatialGradient u
    velocityHessian := scalarSpatialHessian u
    memLp := memLp_on_of_continuousOn_compact_closure hu.continuousOn hV hVc hVU 2
    timeDeriv_memLp := memLp_on_of_continuousOn_compact_closure
      hu.continuousOn_scalarTimeDerivative hV hVc hVU 2
    velocityGrad_memLp := fun i => memLp_on_of_continuousOn_compact_closure
      ((continuous_apply i).comp_continuousOn hu.continuousOn_scalarSpatialGradient)
      hV hVc hVU 2
    velocityHessian_memLp := fun i j => memLp_on_of_continuousOn_compact_closure
      ((continuous_apply j).comp_continuousOn
        ((continuous_apply i).comp_continuousOn hu.continuousOn_scalarSpatialHessian))
      hV hVc hVU 2
    hasWeakTimeDeriv := IsScalarC12On.hasWeakTimeDerivOn hV
      (scalarC12On_mono hu (subset_closure.trans hVU))
    hasWeakVelocityPartialDeriv := IsScalarC12On.hasWeakVelocityPartialDerivOn hV
      (scalarC12On_mono hu (subset_closure.trans hVU))
    hasWeakVelocitySecondPartialDeriv := IsScalarC12On.hasWeakVelocitySecondPartialDerivOn hV
      (scalarC12On_mono hu (subset_closure.trans hVU)) }

/-- The literal local classical jet retains the homogeneous equation in weak-jet order. -/
theorem classicalLocalW12Jet_homogeneous_equation {d : ℕ}
    {U V : Set (TimeVelocity d)} (u : TimeVelocity d → ℝ)
    (hu : IsScalarC12On u U) (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hVU : closure V ⊆ U) (A : CoefficientField d)
    (heq : ∀ z ∈ U, scalarTimeDerivative u z +
      matrixContraction (coefficientAt A z) (scalarSpatialHessian u z) = 0) :
    ∀ᵐ z ∂timeVelocityVolumeOn V,
      (classicalLocalW12Jet u hu hV hVc hVU).timeDeriv z +
        ∑ i, ∑ j, A z.1 z.2 i j *
          (classicalLocalW12Jet u hu hV hVc hVU).velocityHessian z j i = 0 := by
  apply ae_restrict_of_forall_mem hV.measurableSet
  intro z hz
  have hzU := hVU (subset_closure hz)
  have hs := scalarSpatialHessian_isSymm_of_c12 hu hzU
  have hentry (i j : Fin d) : scalarSpatialHessian u z j i =
      scalarSpatialHessian u z i j := congrArg (fun M : PDE.Mat d => M i j) hs
  simpa only [classicalLocalW12Jet, matrixContraction, coefficientAt, hentry]
    using heq z hzU

end HypoellipticAleksandrov.Parabolic.LocalHolder
