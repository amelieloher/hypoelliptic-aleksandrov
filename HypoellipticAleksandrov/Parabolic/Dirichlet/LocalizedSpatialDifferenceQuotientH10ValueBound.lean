module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientSmoothValueBound

/-!
# Uniform value bound for localized spatial quotients

This module transfers the sharp smooth localized value estimate to every
element of the zero-boundary spatial Sobolev graph.
-/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The value of the localized spatial quotient is uniformly controlled by
the weak spatial gradient of its input. -/
theorem norm_valueCLM_localizedSpatialDifferenceQuotientH10CLM_apply_le_gradient
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω)
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω)
    (u : H10HilbertGraph hΩ) :
    ‖valueCLM hΩ
        (localizedSpatialDifferenceQuotientH10CLM
          hΩ η k h hηΩ hηshift u)‖ ≤
      ‖gradientCLM hΩ u‖ := by
  refine (denseRange_smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ).induction_on u ?_ ?_
  · exact isClosed_le
      (((valueCLM hΩ).comp
        (localizedSpatialDifferenceQuotientH10CLM
          hΩ η k h hηΩ hηshift)).continuous.norm)
      ((gradientCLM hΩ).continuous.norm)
  · intro φ
    rw [localizedSpatialDifferenceQuotientH10CLM_apply_smooth
      hΩ η k h φ hηΩ hηshift,
      valueCLM_localizedSpatialDifferenceQuotientSmoothCoreLinearMap_apply
        hΩ η k h φ hηΩ hηshift]
    have hinput :
        smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ =
          smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ := by
      apply Subtype.ext
      rfl
    rw [hinput]
    exact norm_localizedSpatialDifferenceQuotientL2_apply_smooth_le_gradient
      hΩ η k h φ

end HypoellipticAleksandrov.Parabolic.Dirichlet
