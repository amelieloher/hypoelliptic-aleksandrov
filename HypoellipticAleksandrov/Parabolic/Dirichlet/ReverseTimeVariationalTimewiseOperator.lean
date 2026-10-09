module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.VariationalEnergy
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeFormResidual
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeDualPairing

/-!
# Timewise bounded operators for reverse-time variational solutions

This module identifies the declared variational derivative with its canonical
Bochner residual and evaluates that identity against a bounded spatial operator.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal RealInnerProductSpace Matrix.Norms.Elementwise MatrixOrder

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The declared reverse-time variational derivative is the canonical Bochner
source-minus-form residual. -/
theorem IsReverseTimeVariationalEnergySolution.g_eq_reverseTimeFormResidual
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) u g)
    (hu : IsReverseTimeVariationalEnergySolution
      r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth initial u g hdu) :
    g = reverseTimeFormResidual r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth F hFSmooth u := by
  apply Lp.ext
  filter_upwards [hu.2, ae_restrict_mem measurableSet_Ioo,
    ae_reverseTimeFormResidual_apply r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth F hFSmooth u] with τ hsolution hτ hresidual
  ext v
  have hsol := hsolution hτ v
  have hres := hresidual hτ v
  linarith

private theorem ae_sub_apply_timewiseCLM
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ)
    (source action : ReverseTimeL2VStar hΩ T)
    (u : ReverseTimeL2V hΩ T)
    (Q : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ) :
    ∀ᵐ τ ∂reverseTimeVolume T,
      ((source - action) τ) (Q (u τ)) =
        (source τ) (Q (u τ)) - (action τ) (Q (u τ)) := by
  filter_upwards [Lp.coeFn_sub source action] with τ hsub
  calc
    ((source - action) τ) (Q (u τ)) = (source τ - action τ) (Q (u τ)) :=
      congrArg (fun ell => ell (Q (u τ))) hsub
    _ = (source τ) (Q (u τ)) - (action τ) (Q (u τ)) := rfl

/-- The declared derivative evaluated on a timewise bounded spatial image is
the totalized negative-source evaluation minus the totalized form action. -/
theorem ae_reverseTimeVariationalEnergySolution_apply_timewiseCLM
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) u g)
    (hu : IsReverseTimeVariationalEnergySolution
      r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth initial u g hdu)
    (Q : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ) :
    ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀),
      (g τ) (Q (u τ)) =
        (reverseTimeNegativeSource
          r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ) (Q (u τ)) -
        (reverseTimeSpatialFormBochnerAction
          r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth u τ) (Q (u τ)) := by
  rw [IsReverseTimeVariationalEnergySolution.g_eq_reverseTimeFormResidual
    r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth F hFSmooth initial
    u g hdu hu]
  simpa only [reverseTimeFormResidual] using
    (ae_sub_apply_timewiseCLM hΩ (r₁ - r₀)
      (reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth)
      (reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth u) u Q)

/-- Pairing a dual Bochner curve with a bounded timewise spatial image is
integrable on the reverse-time volume. -/
theorem integrable_reverseTimeDualPairing_timewiseCLM
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ)
    (Q : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) :
    MeasureTheory.Integrable (fun τ => (g τ) (Q (u τ)))
      (reverseTimeVolume T) := by
  let Qu := Q.compLpL (2 : ℝ≥0∞) (reverseTimeVolume T) u
  have hQu : Qu =ᵐ[reverseTimeVolume T] fun τ => Q (u τ) :=
    ContinuousLinearMap.coeFn_compLpL Q u
  refine (integrable_reverseTimeDualPairing hΩ T Qu g).congr ?_
  filter_upwards [hQu] with τ hQ
  rw [hQ]

/-- Integrating the timewise bounded-operator pairing of a reverse-time
variational solution gives its totalized source-minus-form identity. -/
theorem integral_reverseTimeVariationalEnergySolution_pair_timewiseCLM_eq
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) u g)
    (hu : IsReverseTimeVariationalEnergySolution
      r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth initial u g hdu)
    (Q : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ) :
    (∫ τ, (g τ) (Q (u τ)) ∂reverseTimeVolume (r₁ - r₀)) =
      (∫ τ,
        (reverseTimeNegativeSource
          r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ) (Q (u τ))
        ∂reverseTimeVolume (r₁ - r₀)) -
      (∫ τ,
        (reverseTimeSpatialFormBochnerAction
          r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth u τ) (Q (u τ))
        ∂reverseTimeVolume (r₁ - r₀)) := by
  have hpair := integrable_reverseTimeDualPairing_timewiseCLM hΩ (r₁ - r₀) Q u g
  have hsource := integrable_reverseTimeDualPairing_timewiseCLM hΩ (r₁ - r₀) Q u
    (reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth)
  have haction := integrable_reverseTimeDualPairing_timewiseCLM hΩ (r₁ - r₀) Q u
    (reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth u)
  calc
    (∫ τ, (g τ) (Q (u τ)) ∂reverseTimeVolume (r₁ - r₀)) =
        ∫ τ,
          (reverseTimeNegativeSource
            r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ) (Q (u τ)) -
          (reverseTimeSpatialFormBochnerAction
            r₀ r₁ h₀₁ hΩ hΩbounded a b c
            haSmooth hbSmooth hcSmooth u τ) (Q (u τ))
          ∂reverseTimeVolume (r₁ - r₀) := by
      exact integral_congr_ae
        (ae_reverseTimeVariationalEnergySolution_apply_timewiseCLM
          r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth F hFSmooth
          initial u g hdu hu Q)
    _ = _ := integral_sub hsource haction

end HypoellipticAleksandrov.Parabolic.Dirichlet
