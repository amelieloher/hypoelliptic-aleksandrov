module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.VariationalEnergy
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGelfandPairing
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSourcePairing
public import HypoellipticAleksandrov.Parabolic.Dirichlet.OriginalTimeTests

/-!
# Original-time separated distribution identity

This module reflects the reverse-time variational residual to its
original-time separated-test distribution identity.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The original-time pullback of the already-negative reverse-time source. -/
noncomputable def originalTimeEnergySourcePairing
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω)
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (r : ℝ) (v : H10HilbertGraph hΩ) : ℝ :=
  reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth (r₁ - r) v

private noncomputable def reverseTimeTestOfOriginal
    (r₀ r₁ : ℝ) (phi : OriginalTimeScalarTest r₀ r₁) :
    ReverseTimeScalarTest (r₁ - r₀) := by
  let e : ℝ ≃ₜ ℝ := (Homeomorph.neg ℝ).trans (Homeomorph.addLeft r₁)
  refine
    { toFun := fun tau => phi (r₁ - tau)
      contDiff' := ?_
      hasCompactSupport' := ?_
      tsupport_subset' := ?_ }
  · simpa only [Function.comp_def, sub_eq_add_neg, id_eq] using
      phi.contDiff.comp (contDiff_const.sub contDiff_id)
  · change HasCompactSupport ((phi : ℝ → ℝ) ∘ e)
    simpa only [e, Function.comp_apply, sub_eq_add_neg] using
      phi.hasCompactSupport.comp_homeomorph e
  · change tsupport ((phi : ℝ → ℝ) ∘ e) ⊆ Set.Ioo 0 (r₁ - r₀)
    rw [tsupport, Function.support_comp_eq_preimage, ← e.preimage_closure]
    change (fun tau : ℝ => r₁ - tau) ⁻¹' tsupport (phi : ℝ → ℝ) ⊆
      Set.Ioo 0 (r₁ - r₀)
    refine (preimage_mono phi.tsupport_subset).trans ?_
    change (fun tau : ℝ => r₁ - tau) ⁻¹' Set.Ioo r₀ r₁ ⊆ Set.Ioo 0 (r₁ - r₀)
    rw [preimage_const_sub_Ioo]
    simp only [sub_self]
    exact Subset.rfl

private theorem deriv_reverseTimeTestOfOriginal
    (r₀ r₁ : ℝ) (phi : OriginalTimeScalarTest r₀ r₁) (tau : ℝ) :
    (reverseTimeTestOfOriginal r₀ r₁ phi).deriv tau = -phi.deriv (r₁ - tau) := by
  rw [ReverseTimeScalarTest.deriv_apply, OriginalTimeScalarTest.deriv_apply]
  exact (HasDerivAt.comp_const_sub r₁ tau
    ((phi.contDiff.differentiable (by simp)).differentiableAt.hasDerivAt)).deriv

private theorem integrable_reverseTimeNegativeSourceRaw_mul_test
    {d : ℕ} {Ω : Set (PDE.Vec d)} (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (eta : ReverseTimeScalarTest (r₁ - r₀)) (v : H10HilbertGraph hΩ) :
    Integrable
      (fun tau => reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v * eta tau)
      (reverseTimeVolume (r₁ - r₀)) := by
  let S := reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth
  let z := reverseTimeSeparatedVTest hΩ eta v
  have hPair : Integrable (fun tau => S tau (z tau)) (reverseTimeVolume (r₁ - r₀)) :=
    integrable_reverseTimeDualPairing hΩ (r₁ - r₀) z S
  refine hPair.congr ?_
  filter_upwards
    [(memLp_reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth).coeFn_toLp,
      ae_reverseTimeSeparatedVTest hΩ eta v] with tau hS hz
  dsimp only [S, z]
  calc
    reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau
        (reverseTimeSeparatedVTest hΩ eta v tau) =
        reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau (eta tau • v) :=
      congrArg (reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau) hz
    _ = eta tau * reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v := by
      rw [ContinuousLinearMap.map_smul]
      rfl
    _ = eta tau * reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v :=
      congrArg (fun q => eta tau * q v) hS
    _ = reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v * eta tau :=
      mul_comm _ _

private theorem integral_sub_add_eq_zero_of_pairing
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (mass form source dual : α → ℝ)
    (hmass : Integrable mass μ) (hform : Integrable form μ)
    (hsource : Integrable source μ)
    (hmassEq : (∫ x, mass x ∂μ) = -(∫ x, dual x ∂μ))
    (hformEq : (∫ x, form x ∂μ) = (∫ x, source x ∂μ) - ∫ x, dual x ∂μ) :
    (∫ x, mass x - form x + source x ∂μ) = 0 := by
  change (∫ x, (mass - form) x + source x ∂μ) = 0
  rw [integral_add (hmass.sub hform) hsource]
  change (∫ x, mass x - form x ∂μ) + ∫ x, source x ∂μ = 0
  rw [integral_sub hmass hform, hmassEq, hformEq]
  ring

private theorem reverseTime_separated_residual_of_variationalEnergy
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u g)
    (hu : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F hFSmooth initial u g hdu)
    (eta : ReverseTimeScalarTest (r₁ - r₀))
    (v : H10HilbertGraph hΩ) :
    Integrable (fun tau =>
      inner ℝ (valueCLM hΩ v) (valueCLM hΩ (u tau)) * eta.deriv tau -
        reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v * eta tau +
        reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v * eta tau)
      (reverseTimeVolume (r₁ - r₀)) ∧
    (∫ tau,
      inner ℝ (valueCLM hΩ v) (valueCLM hΩ (u tau)) * eta.deriv tau -
        reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v * eta tau +
        reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v * eta tau
      ∂reverseTimeVolume (r₁ - r₀)) = 0 := by
  obtain ⟨hmassLift, hg, hmassLiftEq⟩ := hdu v eta
  have hmass : Integrable (fun tau =>
      inner ℝ (valueCLM hΩ v) (valueCLM hΩ (u tau)) * eta.deriv tau)
      (reverseTimeVolume (r₁ - r₀)) := by
    refine hmassLift.congr ?_
    filter_upwards [coeFn_reverseTimeValueCLM hΩ (r₁ - r₀) u] with tau huValue
    rw [huValue]
  have hmassEq : (∫ tau,
      inner ℝ (valueCLM hΩ v) (valueCLM hΩ (u tau)) * eta.deriv tau
      ∂reverseTimeVolume (r₁ - r₀)) =
      -(∫ tau, (g tau) v * eta tau ∂reverseTimeVolume (r₁ - r₀)) := by
    calc
      _ = ∫ tau,
          inner ℝ (valueCLM hΩ v) (reverseTimeValueCLM hΩ (r₁ - r₀) u tau) * eta.deriv tau
          ∂reverseTimeVolume (r₁ - r₀) := by
        apply integral_congr_ae
        filter_upwards [coeFn_reverseTimeValueCLM hΩ (r₁ - r₀) u] with tau huValue
        rw [huValue]
      _ = _ := hmassLiftEq
  have hsource := integrable_reverseTimeNegativeSourceRaw_mul_test r₀ r₁ h₀₁ hΩ hΩbounded F
    hFSmooth eta v
  have hformEq : ∀ᵐ tau ∂reverseTimeVolume (r₁ - r₀),
      reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v * eta tau =
        reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v * eta tau -
          (g tau) v * eta tau := by
    filter_upwards [hu.2, ae_restrict_mem measurableSet_Ioo] with tau hEquation htau
    have hRaw : reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau =
        reverseTimeSourceFunctional hΩ
          (reverseTimeSourceSlice r₁ tau F
            (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood r₀ r₁ hΩ hΩbounded F hFSmooth
              tau ⟨le_of_lt htau.1, le_of_lt htau.2⟩)) :=
      reverseTimeNegativeSourceRaw_eq_sourceFunctional_of_mem_Icc r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth
        tau ⟨le_of_lt htau.1, le_of_lt htau.2⟩
    have hPoint := hEquation htau v
    rw [← hRaw] at hPoint
    calc
      reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v * eta tau =
          ((g tau) v + reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v - (g tau) v) * eta tau := by
            ring
      _ = (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v -
          (g tau) v) * eta tau := by
            rw [hPoint]
      _ = _ := sub_mul _ _ _
  have hform : Integrable (fun tau =>
      reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v * eta tau)
      (reverseTimeVolume (r₁ - r₀)) :=
    (hsource.sub hg).congr (by
      filter_upwards [hformEq] with tau htau
      exact htau.symm)
  have hformEqIntegral : (∫ tau,
      reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v * eta tau
      ∂reverseTimeVolume (r₁ - r₀)) =
      (∫ tau, reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v * eta tau
        ∂reverseTimeVolume (r₁ - r₀)) -
        ∫ tau, (g tau) v * eta tau ∂reverseTimeVolume (r₁ - r₀) := by
    calc
      _ = ∫ tau, reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v * eta tau -
          (g tau) v * eta tau ∂reverseTimeVolume (r₁ - r₀) := integral_congr_ae hformEq
      _ = _ := integral_sub hsource hg
  constructor
  · exact (hmass.sub hform).add hsource
  · exact integral_sub_add_eq_zero_of_pairing (reverseTimeVolume (r₁ - r₀)) _ _ _ _
      hmass hform hsource hmassEq hformEqIntegral

private theorem originalTimeReflection_measurePreserving (r₀ r₁ : ℝ) :
    MeasurePreserving (fun r : ℝ => r₁ - r)
      (reverseTimeVolume (r₁ - r₀)) (volume.restrict (Set.Ioo r₀ r₁)) := by
  have hreflection : MeasurePreserving (fun r : ℝ => r₁ - r) (volume : Measure ℝ) volume := by
    simpa only [Function.comp_def, sub_eq_add_neg, id_eq] using
      (measurePreserving_add_left (volume : Measure ℝ) r₁).comp
        (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hpreimage : (fun r : ℝ => r₁ - r) ⁻¹' Set.Ioo r₀ r₁ = Set.Ioo 0 (r₁ - r₀) := by
    rw [preimage_const_sub_Ioo]
    simp only [sub_self]
  rw [reverseTimeVolume, reverseTimeOpenInterval, ← hpreimage]
  exact hreflection.restrict_preimage isOpen_Ioo.measurableSet

private theorem originalTimeReflection_measurePreserving_symm (r₀ r₁ : ℝ) :
    MeasurePreserving (fun r : ℝ => r₁ - r)
      (volume.restrict (Set.Ioo r₀ r₁)) (reverseTimeVolume (r₁ - r₀)) := by
  have hreflection : MeasurePreserving (fun r : ℝ => r₁ - r) (volume : Measure ℝ) volume := by
    simpa only [Function.comp_def, sub_eq_add_neg, id_eq] using
      (measurePreserving_add_left (volume : Measure ℝ) r₁).comp
        (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hpreimage : (fun r : ℝ => r₁ - r) ⁻¹' Set.Ioo 0 (r₁ - r₀) = Set.Ioo r₀ r₁ := by
    rw [preimage_const_sub_Ioo]
    congr 1 <;> ring
  rw [reverseTimeVolume, reverseTimeOpenInterval, ← hpreimage]
  exact hreflection.restrict_preimage isOpen_Ioo.measurableSet

/-- A supplied reverse-time variational energy solution satisfies the original-time
separated-test distribution identity. -/
theorem originalTime_separated_distribution_of_reverseTimeVariationalEnergy
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) u g)
    (hu : IsReverseTimeVariationalEnergySolution
      r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth initial u g hdu)
    (phi : OriginalTimeScalarTest r₀ r₁)
    (v : H10HilbertGraph hΩ) :
    Integrable
      (fun r =>
        inner ℝ (valueCLM hΩ v) (valueCLM hΩ (u (r₁ - r))) *
            phi.deriv r +
          reverseTimeSpatialForm hΩ r₁ (r₁ - r) a b c
              (u (r₁ - r)) v * phi r -
          originalTimeEnergySourcePairing
              r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth r v * phi r)
      (volume.restrict (Set.Ioo r₀ r₁)) ∧
    (∫ r,
        inner ℝ (valueCLM hΩ v) (valueCLM hΩ (u (r₁ - r))) *
            phi.deriv r +
          reverseTimeSpatialForm hΩ r₁ (r₁ - r) a b c
              (u (r₁ - r)) v * phi r -
          originalTimeEnergySourcePairing
              r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth r v * phi r
      ∂volume.restrict (Set.Ioo r₀ r₁)) = 0 := by
  let eta := reverseTimeTestOfOriginal r₀ r₁ phi
  let residual : ℝ → ℝ := fun tau =>
    inner ℝ (valueCLM hΩ v) (valueCLM hΩ (u tau)) * eta.deriv tau -
      reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v * eta tau +
      reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v * eta tau
  obtain ⟨hresidual, hresidualIntegral⟩ :=
    reverseTime_separated_residual_of_variationalEnergy r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth
      initial u g hdu hu eta v
  have hreflection := originalTimeReflection_measurePreserving_symm r₀ r₁
  have hpoint (r : ℝ) :
      inner ℝ (valueCLM hΩ v) (valueCLM hΩ (u (r₁ - r))) * phi.deriv r +
          reverseTimeSpatialForm hΩ r₁ (r₁ - r) a b c (u (r₁ - r)) v * phi r -
          originalTimeEnergySourcePairing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth r v * phi r =
        -(residual (r₁ - r)) := by
    change
      inner ℝ (valueCLM hΩ v) (valueCLM hΩ (u (r₁ - r))) * phi.deriv r +
          reverseTimeSpatialForm hΩ r₁ (r₁ - r) a b c (u (r₁ - r)) v * phi r -
          reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth (r₁ - r) v * phi r =
        -(inner ℝ (valueCLM hΩ v) (valueCLM hΩ (u (r₁ - r))) *
            (reverseTimeTestOfOriginal r₀ r₁ phi).deriv (r₁ - r) -
          reverseTimeSpatialForm hΩ r₁ (r₁ - r) a b c (u (r₁ - r)) v *
            reverseTimeTestOfOriginal r₀ r₁ phi (r₁ - r) +
          reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth (r₁ - r) v *
            reverseTimeTestOfOriginal r₀ r₁ phi (r₁ - r))
    have hvalue : reverseTimeTestOfOriginal r₀ r₁ phi (r₁ - r) = phi r := by
      change phi (r₁ - (r₁ - r)) = phi r
      rw [sub_sub_cancel]
    rw [deriv_reverseTimeTestOfOriginal, hvalue]
    ring
  have horiginal : Integrable
      (fun r =>
        inner ℝ (valueCLM hΩ v) (valueCLM hΩ (u (r₁ - r))) * phi.deriv r +
          reverseTimeSpatialForm hΩ r₁ (r₁ - r) a b c (u (r₁ - r)) v * phi r -
          originalTimeEnergySourcePairing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth r v * phi r)
      (volume.restrict (Set.Ioo r₀ r₁)) := by
    refine (hreflection.integrable_comp_of_integrable hresidual.neg).congr ?_
    filter_upwards [] with r
    simpa only [Function.comp_def, Pi.neg_apply] using (hpoint r).symm
  constructor
  · exact horiginal
  · calc
      _ = ∫ r, -(residual (r₁ - r)) ∂volume.restrict (Set.Ioo r₀ r₁) := by
        apply integral_congr_ae
        filter_upwards [] with r
        exact hpoint r
      _ = ∫ tau, -residual tau ∂reverseTimeVolume (r₁ - r₀) := by
        exact hreflection.integral_comp ((Homeomorph.neg ℝ).trans
          (Homeomorph.addLeft r₁)).measurableEmbedding (fun tau => -residual tau)
      _ = -(∫ tau, residual tau ∂reverseTimeVolume (r₁ - r₀)) := integral_neg residual
      _ = 0 := by rw [hresidualIntegral, neg_zero]

end HypoellipticAleksandrov.Parabolic.Dirichlet
