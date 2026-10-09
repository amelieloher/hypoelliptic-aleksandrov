module

public import HypoellipticAleksandrov.Parabolic.WeakEquationMollificationResidualDecay
public import HypoellipticAleksandrov.Parabolic.WeakSolutionMollifierConvergence

/-!
# Aligned residual-bearing weak-solution mollifications

This module selects one concrete localized parabolic jet and proves the
simultaneous compact approximation, residual, coefficient, and positivity
properties of that same jet's literal right mollifications.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace LocalizedParabolicJet

/-- The concrete localized jet selected for a weak solution has an eventual
pointwise mollified residual equation on its compact carrier. -/
theorem eventually_residual_equation_on
    {d : Nat} {A Aext : CoefficientField d}
    {U K : Set (TimeVelocity d)} {u : TimeVelocity d → Real}
    (J : LocalizedParabolicJet d U K u)
    (hExtAE : coefficientAt Aext =ᵐ[timeVelocityVolumeOn U] coefficientAt A)
    (hWeak : IsWeakParabolicEquationLoc A U (parabolicExponent d) u) :
    ∀ᶠ n in atTop, ∀ z ∈ K,
      parabolicOperator (parabolicMollifyCoefficient Aext n)
          (parabolicMollifiedValue J.g n) z =
        weakEquationMollificationResidual Aext J.g n z := by
  have hp : (1 : ENNReal) ≤ parabolicExponent d := by
    simp [parabolicExponent]
  have hWeq : IsWeakParabolicEquationOn A J.w :=
    hWeak.equationOn J.W_open J.W_closure_compact J.closure_W_subset_U hp J.w J.w_ae_eq_u
  have hWeq' : J.w.timeDeriv =ᵐ[timeVelocityVolumeOn J.W]
      fun z => matrixContraction (coefficientAt A z) (J.w.velocityHessian z) := by
    filter_upwards [hWeq] with z hz
    exact sub_eq_zero.mp (by simpa only [weakParabolicOperator, Pi.zero_apply] using hz)
  obtain ⟨O, hO, hclosureVO, hOW, _hvalue, htime, _hgrad, hhessian⟩ :=
    J.exists_open_plateau
  have hOU : O ⊆ U :=
    hOW.trans (subset_closure.trans J.closure_W_subset_U)
  have hWeqO : J.w.timeDeriv =ᵐ[timeVelocityVolumeOn O]
      fun z => matrixContraction (coefficientAt A z) (J.w.velocityHessian z) :=
    hWeq'.filter_mono <| ae_mono <| Measure.restrict_mono_set volume hOW
  have hExtAEO : coefficientAt Aext =ᵐ[timeVelocityVolumeOn O] coefficientAt A :=
    hExtAE.filter_mono <| ae_mono <| Measure.restrict_mono_set volume hOU
  have hEqO : J.g.timeDeriv =ᵐ[timeVelocityVolumeOn O]
      fun z => matrixContraction (coefficientAt Aext z) (J.g.velocityHessian z) := by
    apply (ae_restrict_iff' hO.measurableSet).mpr
    have hWeqO' := (ae_restrict_iff' hO.measurableSet).mp hWeqO
    have hExtAEO' := (ae_restrict_iff' hO.measurableSet).mp hExtAEO
    filter_upwards [hWeqO', hExtAEO'] with z hweq hAext hzO
    calc
      J.g.timeDeriv z = J.w.timeDeriv z := htime hzO
      _ = matrixContraction (coefficientAt A z) (J.w.velocityHessian z) := hweq hzO
      _ = matrixContraction (coefficientAt Aext z) (J.g.velocityHessian z) := by
        rw [hAext hzO, hhessian hzO]
  have hEquation := eventually_residual_equation_of_ae_on J.V_closure_compact hO hclosureVO
    J.g hp hEqO
  filter_upwards [hEquation] with n hn
  intro z hz
  exact hn z (subset_closure (J.K_subset_V hz))

end LocalizedParabolicJet

/-- A nonnegative local weak solution admits one selected localized jet whose
literal mollifications converge uniformly to the supplied representative,
have decaying residuals, and eventually satisfy all stated smooth classical
approximation properties on the same compact carrier. -/
theorem exists_localizedJet_eventually_nonnegative_residual_mollifications_tendsto
    (d : Nat) (hd : 1 ≤ d) (lam Lam : Real)
    (A Aext : CoefficientField d)
    (U K : Set (TimeVelocity d))
    (u q : TimeVelocity d → Real)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hExtAE : coefficientAt Aext =ᵐ[timeVelocityVolumeOn U] coefficientAt A)
    (hExtBorel : IsBorelCoefficient Aext)
    (hExtLower : HasLowerEllipticity lam Aext)
    (hExtUpper : HasUpperEllipticity Lam Aext)
    (hWeak : IsWeakParabolicEquationLoc A U (parabolicExponent d) u)
    (huNonneg : ∀ᵐ z ∂timeVelocityVolumeOn U, 0 ≤ u z)
    (hq : ContinuousOn q U)
    (hqu : q =ᵐ[timeVelocityVolumeOn U] u) :
    ∃ J : LocalizedParabolicJet d U K u,
      TendstoUniformlyOn
        (fun n z => parabolicMollifiedValue J.g n z) q atTop K ∧
      Tendsto (fun n => eLpNorm
        (weakEquationMollificationResidual Aext J.g n)
        (parabolicExponent d) (volume.restrict K)) atTop (nhds 0) ∧
      ∀ᶠ n in atTop,
        IsSmoothCoefficient (parabolicMollifyCoefficient Aext n) ∧
        IsSymmetricCoefficient (parabolicMollifyCoefficient Aext n) ∧
        HasLowerEllipticity lam (parabolicMollifyCoefficient Aext n) ∧
        HasUpperEllipticity Lam (parabolicMollifyCoefficient Aext n) ∧
        ContDiff Real (↑(⊤ : ℕ∞)) (parabolicMollifiedValue J.g n) ∧
        (∀ z ∈ K, 0 ≤ parabolicMollifiedValue J.g n z) ∧
        (∀ z ∈ K,
          parabolicOperator (parabolicMollifyCoefficient Aext n)
              (parabolicMollifiedValue J.g n) z =
            weakEquationMollificationResidual Aext J.g n z) := by
  obtain ⟨J, hUniform⟩ :=
    ParabolicW12Loc.exists_localizedJet_mollifications_tendstoUniformlyOn d hd hU hK hKU
      hWeak.parabolicW12Loc hq hqu
  have hp : (1 : ENNReal) ≤ parabolicExponent d := by
    simp [parabolicExponent]
  have hResidual := tendsto_eLpNorm_weakEquationMollificationResidual_on_compact d lam Lam
    Aext J.g K hK hExtBorel hExtLower hExtUpper
  have hSymm : IsSymmetricCoefficient Aext :=
    isSymmetricCoefficient_of_hasLowerEllipticity hExtLower
  have hCoefficient : ∀ᶠ n in atTop,
      IsSmoothCoefficient (parabolicMollifyCoefficient Aext n) ∧
      IsSymmetricCoefficient (parabolicMollifyCoefficient Aext n) ∧
      HasLowerEllipticity lam (parabolicMollifyCoefficient Aext n) ∧
      HasUpperEllipticity Lam (parabolicMollifyCoefficient Aext n) :=
    Filter.Eventually.of_forall fun n =>
      ⟨isSmoothCoefficient_parabolicMollifyCoefficient d lam Lam Aext hExtBorel hExtLower
          hExtUpper n,
        isSymmetricCoefficient_parabolicMollifyCoefficient d lam Lam Aext hSymm n,
        hasLowerEllipticity_parabolicMollifyCoefficient d lam Lam Aext hExtBorel hSymm
          hExtLower hExtUpper n,
        hasUpperEllipticity_parabolicMollifyCoefficient d lam Lam Aext hExtBorel hSymm
          hExtLower hExtUpper n⟩
  obtain ⟨O, hO, hclosureVO, hOW, hvalue, _htime, _hgrad, _hhessian⟩ :=
    J.exists_open_plateau
  have hKO : K ⊆ O :=
    J.K_subset_V.trans (subset_closure.trans hclosureVO)
  have hOU : O ⊆ U :=
    hOW.trans (subset_closure.trans J.closure_W_subset_U)
  have hValueO : J.g.toFun =ᵐ[timeVelocityVolumeOn O] J.w.toFun := by
    filter_upwards [ae_restrict_mem hO.measurableSet] with z hzO
    exact hvalue hzO
  have hWValueO : J.w.toFun =ᵐ[timeVelocityVolumeOn O] u :=
    J.w_ae_eq_u.filter_mono <| ae_mono <| Measure.restrict_mono_set volume hOW
  have huNonnegO : ∀ᵐ z ∂timeVelocityVolumeOn O, 0 ≤ u z :=
    huNonneg.filter_mono <| ae_mono <| Measure.restrict_mono_set volume hOU
  have hNonnegO : ∀ᵐ z ∂timeVelocityVolumeOn O, 0 ≤ J.g.toFun z := by
    filter_upwards [hValueO.trans hWValueO, huNonnegO] with z hgu hnonneg
    rw [hgu]
    exact hnonneg
  have hNonnegative :=
    eventually_nonnegative_parabolicMollifiedValue_of_ae_nonnegative_on hK hO hKO J.g hNonnegO
  have hEquation := J.eventually_residual_equation_on hExtAE hWeak
  refine ⟨J, ?_, hResidual, ?_⟩
  · simpa only [parabolicMollifiedValue] using hUniform
  · filter_upwards [hCoefficient, hNonnegative, hEquation] with n hcoefficient hnonnegative
      hequation
    exact ⟨hcoefficient.1, hcoefficient.2.1, hcoefficient.2.2.1, hcoefficient.2.2.2,
      contDiff_parabolicMollifiedValue J.g hp n, hnonnegative, hequation⟩

end HypoellipticAleksandrov.Parabolic
