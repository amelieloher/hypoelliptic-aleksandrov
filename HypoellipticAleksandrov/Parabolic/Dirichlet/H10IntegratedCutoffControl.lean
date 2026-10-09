module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10IntegratedHalfAbsorption
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10CutoffGradientBound

/-!
# Sign-free integrated cutoff-gradient control

This module replaces the signed companion-field term in integrated H10 half
absorption with its sign-free aggregate cutoff-gradient control.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.Elementwise

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

namespace IsReverseTimeVariationalEnergySolution

/-- The reducible exact output proposition of integrated H10 half coercivity
with sign-free cutoff-gradient control.  This names a conclusion and is not an
assumption package. -/
abbrev integratedH10HalfCoerciveCutoffControlOutput
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (_haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (_hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (_hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (_hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ) : Prop :=
    ∃ δ : ℝ, 0 < δ ∧
      ∀ lam : ℝ, 0 < lam →
        ∃ C_lam : ℝ, 0 ≤ C_lam ∧
          ∀ (Lam : ℝ)
            (hLower : ∀ z : TimeVelocity d,
              z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
                lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
            (hUpper : ∀ z : TimeVelocity d,
              z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
                a z.1 z.2 ≤ Lam • (1 : PDE.Mat d)),
            ∀ (k : Fin d) (h : ℝ), |h| ≤ δ →
              ∃ hχshift : Set.MapsTo
                (fun y : PDE.Vec d => y + h • PDE.basisVec k)
                (tsupport χ.toFun) Ω,
              ∀ (hζnonneg :
                  ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀), 0 ≤ ζ τ)
                (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
                (u : ReverseTimeL2V hΩ (r₁ - r₀))
                (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
                (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
                  (sub_pos.mpr h₀₁) u g)
                (hu : IsReverseTimeVariationalEnergySolution
                  r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth initial u g hdu),
                let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
                  intro y hy
                  apply subset_tsupport
                  change χ y ≠ 0
                  rw [χ.eq_one_on_inner y hy]
                  exact one_ne_zero
                let hηshift : Set.MapsTo
                    (fun y : PDE.Vec d => y + h • PDE.basisVec k)
                    (tsupport η.toFun) Ω :=
                  hχshift.mono_left hηχ
                let A : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
                  localizedSpatialDifferenceQuotientH10CLM
                    hΩ η k h η.tsupport_subset hηshift
                let Gv : ℝ → PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
                  fun τ => gradientCLM hΩ (A (u τ))
                (-(1 / 2 : ℝ) *
                    (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * ζ.deriv τ
                      ∂reverseTimeVolume (r₁ - r₀)) +
                  (∫ τ, ζ τ *
                    ((lam / 2) * ‖Gv τ‖ ^ 2 -
                      max Lam 0 * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2)
                    ∂reverseTimeVolume (r₁ - r₀)) ≤
                  (∫ τ, ζ τ * (C_lam * (1 + ‖u τ‖ ^ 2))
                    ∂reverseTimeVolume (r₁ - r₀)))

private theorem integrable_norm_sq_timewise_apply
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : H10HilbertGraph hΩ →L[ℝ] E) (u : ReverseTimeL2V hΩ T) :
    Integrable (fun τ => ‖L (u τ)‖ ^ 2) (reverseTimeVolume T) := by
  let Lu := L.compLpL (2 : ℝ≥0∞) (reverseTimeVolume T) u
  have hLu : Lu =ᵐ[reverseTimeVolume T] fun τ => L (u τ) :=
    ContinuousLinearMap.coeFn_compLpL L u
  refine (show Integrable (fun τ => ‖Lu τ‖ ^ 2) (reverseTimeVolume T) by
    simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) Lu Lu).congr ?_
  filter_upwards [hLu] with τ hτ
  rw [hτ]

private theorem integrable_weighted
    {T : ℝ} (ζ : ReverseTimeScalarTest T) (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1)
    {f : ℝ → ℝ} (hf : Integrable f (reverseTimeVolume T)) :
    Integrable (fun τ => ζ τ * f τ) (reverseTimeVolume T) := by
  exact hf.bdd_mul ζ.contDiff.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall hζunit)

/-- The aggregate cutoff-gradient bound gives a sign-free companion control
in the integrated half-coercive inequality. -/
theorem
    exists_smallStep_integral_h10Commutator_add_halfCoerciveTerm_le_nonprincipalYoung_cutoffControl
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ) :
    integratedH10HalfCoerciveCutoffControlOutput
      r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth
      F hFSmooth ζ hζunit η χ := by
  obtain ⟨δ, hδ, hparent⟩ :=
    exists_smallStep_integral_h10Commutator_add_halfCoerciveTerm_le_nonprincipalYoung
      r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth F hFSmooth ζ hζunit η χ
  refine ⟨δ, hδ, ?_⟩
  intro lam hlam
  obtain ⟨C_lam, hC_lam, hparent⟩ := hparent lam hlam
  refine ⟨C_lam, hC_lam, ?_⟩
  intro Lam hLower hUpper k h hh
  obtain ⟨hχshift, hparent⟩ := hparent Lam hLower hUpper k h hh
  refine ⟨hχshift, ?_⟩
  intro hζnonneg initial u g hdu hu
  let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
    intro y hy
    apply subset_tsupport
    change χ y ≠ 0
    rw [χ.eq_one_on_inner y hy]
    exact one_ne_zero
  let hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω := hχshift.mono_left hηχ
  let A : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
    localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
  let Gv : ℝ → PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
    fun τ => gradientCLM hΩ (A (u τ))
  let Wv : ℝ → PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
    fun τ => cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h (u τ)
  have hparent' := hparent hζnonneg initial u g hdu hu
  have hGsq : Integrable (fun τ => ‖Gv τ‖ ^ 2) (reverseTimeVolume (r₁ - r₀)) := by
    exact integrable_norm_sq_timewise_apply hΩ (r₁ - r₀) ((gradientCLM hΩ).comp A) u
  have hWsq : Integrable (fun τ => ‖Wv τ‖ ^ 2) (reverseTimeVolume (r₁ - r₀)) := by
    exact integrable_norm_sq_timewise_apply hΩ (r₁ - r₀)
      (cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h) u
  have hUsq : Integrable (fun τ => ‖gradientCLM hΩ (u τ)‖ ^ 2)
      (reverseTimeVolume (r₁ - r₀)) := by
    exact integrable_norm_sq_timewise_apply hΩ (r₁ - r₀) (gradientCLM hΩ) u
  have hhalf : Integrable (fun τ => ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2))
      (reverseTimeVolume (r₁ - r₀)) :=
    integrable_weighted ζ hζunit (hGsq.const_mul (lam / 2))
  have hW : Integrable (fun τ => ζ τ * (Lam * ‖Wv τ‖ ^ 2))
      (reverseTimeVolume (r₁ - r₀)) :=
    integrable_weighted ζ hζunit (hWsq.const_mul Lam)
  have hcutoff : Integrable (fun τ => ζ τ *
      (max Lam 0 * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2))
      (reverseTimeVolume (r₁ - r₀)) :=
    integrable_weighted ζ hζunit (hUsq.const_mul (max Lam 0 * Kη ^ 2))
  have hparentBulk : Integrable (fun τ => ζ τ *
      ((lam / 2) * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2))
      (reverseTimeVolume (r₁ - r₀)) := by
    simpa only [Pi.sub_def, mul_sub] using hhalf.sub hW
  have htargetBulk : Integrable (fun τ => ζ τ *
      ((lam / 2) * ‖Gv τ‖ ^ 2 -
        max Lam 0 * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2))
      (reverseTimeVolume (r₁ - r₀)) := by
    simpa only [Pi.sub_def, mul_sub] using hhalf.sub hcutoff
  have hpoint : ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀),
      ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2 -
        max Lam 0 * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2) ≤
      ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2) := by
    filter_upwards [hζnonneg] with τ hζτ
    have hcontrol : Lam * ‖Wv τ‖ ^ 2 ≤
        max Lam 0 * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2 := by
      calc
        Lam * ‖Wv τ‖ ^ 2 ≤ max Lam 0 * ‖Wv τ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
        _ ≤ max Lam 0 * (Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left
            (norm_sq_cutoffGradientSpatialDifferenceQuotientH10CLM_apply_le_gradient
              hΩ η χ k h hχshift (u τ))
            (le_max_right _ _)
        _ = max Lam 0 * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2 := by ring
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left hcontrol _) hζτ
  have hbulk :
      (∫ τ, ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2 -
        max Lam 0 * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2)
        ∂reverseTimeVolume (r₁ - r₀)) ≤
      ∫ τ, ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
        ∂reverseTimeVolume (r₁ - r₀) :=
    integral_mono_ae htargetBulk hparentBulk hpoint
  change
    -(1 / 2 : ℝ) *
        (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * ζ.deriv τ
          ∂reverseTimeVolume (r₁ - r₀)) +
      (∫ τ, ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2 -
        max Lam 0 * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2)
        ∂reverseTimeVolume (r₁ - r₀)) ≤
      ∫ τ, ζ τ * (C_lam * (1 + ‖u τ‖ ^ 2)) ∂reverseTimeVolume (r₁ - r₀)
  change
    -(1 / 2 : ℝ) *
        (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * ζ.deriv τ
          ∂reverseTimeVolume (r₁ - r₀)) +
      (∫ τ, ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
        ∂reverseTimeVolume (r₁ - r₀)) ≤
      ∫ τ, ζ τ * (C_lam * (1 + ‖u τ‖ ^ 2)) ∂reverseTimeVolume (r₁ - r₀) at hparent'
  linarith

/-- The integrated cutoff-control inequality has a Young constant uniform
over all coefficient data satisfying the supplied literal majorants. -/
theorem exists_uniform_integral_h10Commutator_add_halfCoerciveTerm_le_cutoffControl_of_majorants
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (ζ : ReverseTimeScalarTest (r₁ - r₀)) (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1)
    (δ : ℝ)
    (hcarrier : spatialCoordinateShiftCarrier (tsupport χ.toFun) δ ⊆ Ω)
    (lam : ℝ) (hlam : 0 < lam) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C_lam : ℝ, 0 ≤ C_lam ∧
      ∀ (Lam : ℝ) (hlamLam : lam ≤ Lam)
        (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
        (c F : ℝ → PDE.Vec d → ℝ),
        ∀ (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
            (scalarParabolicClosedCylinder r₀ r₁ Ω))
          (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
            (scalarParabolicClosedCylinder r₀ r₁ Ω))
          (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
            (scalarParabolicClosedCylinder r₀ r₁ Ω))
          (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
            (scalarParabolicClosedCylinder r₀ r₁ Ω))
          (hLower : ∀ z : TimeVelocity d,
            z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
              lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
          (hUpper : ∀ z : TimeVelocity d,
            z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
              a z.1 z.2 ≤ Lam • (1 : PDE.Mat d))
          (hA : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
            spatialMatrixFDerivFrobeniusNorm
              (fun w : TimeVelocity d => reverseTimeCoefficient r₁ a w.1 w.2) z ≤ M)
          (hB : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
            PDE.vecEuclideanNorm (reverseTimeDivergenceDrift r₁ a b z.1 z.2) ≤ M)
          (hBD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
            spatialVectorFDerivFrobeniusNorm
              (fun w : TimeVelocity d => reverseTimeDivergenceDrift r₁ a b w.1 w.2) z ≤ M)
          (hq : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
            |-(reverseTimeScalarCoefficient r₁ c z.1 z.2)| ≤ M)
          (hqD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
            spatialScalarFDerivEuclideanNorm
              (fun w : TimeVelocity d => -(reverseTimeScalarCoefficient r₁ c w.1 w.2)) z ≤ M)
          (hfD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
            spatialScalarFDerivEuclideanNorm
              (fun w : TimeVelocity d => -(reverseTimeScalarCoefficient r₁ F w.1 w.2)) z ≤ M),
        ∀ (k : Fin d) (h : ℝ) (hh : |h| ≤ δ)
          (hζnonneg : ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀), 0 ≤ ζ τ)
          (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
          (u : ReverseTimeL2V hΩ (r₁ - r₀))
          (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
          (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u g)
          (hu : IsReverseTimeVariationalEnergySolution
            r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth initial u g hdu),
          let hχshift : Set.MapsTo
              (fun y : PDE.Vec d => y + h • PDE.basisVec k)
              (tsupport χ.toFun) Ω :=
            mapsTo_add_smul_basisVec_of_spatialCoordinateShiftCarrier_subset
              hcarrier k hh
          let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
            intro y hy
            apply subset_tsupport
            change χ y ≠ 0
            rw [χ.eq_one_on_inner y hy]
            exact one_ne_zero
          let hηshift : Set.MapsTo
              (fun y : PDE.Vec d => y + h • PDE.basisVec k)
              (tsupport η.toFun) Ω :=
            hχshift.mono_left hηχ
          let A : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
            localizedSpatialDifferenceQuotientH10CLM
              hΩ η k h η.tsupport_subset hηshift
          let Gv : ℝ → PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
            fun τ => gradientCLM hΩ (A (u τ))
          (-(1 / 2 : ℝ) *
              (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * ζ.deriv τ
                ∂reverseTimeVolume (r₁ - r₀)) +
            (∫ τ, ζ τ *
                ((lam / 2) * ‖Gv τ‖ ^ 2 -
                  Lam * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2)
                ∂reverseTimeVolume (r₁ - r₀)) ≤
            (∫ τ, ζ τ * (C_lam * (1 + ‖u τ‖ ^ 2))
              ∂reverseTimeVolume (r₁ - r₀))) := by
  obtain ⟨C_lam, hC_lam, hparent⟩ :=
    exists_uniform_integral_h10Commutator_add_halfCoerciveTerm_le_nonprincipalYoung_of_majorants
      r₀ r₁ h₀₁ hΩ hΩbounded η χ ζ hζunit δ hcarrier lam hlam M hM
  refine ⟨C_lam, hC_lam, ?_⟩
  intro Lam hlamLam a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hUpper
    hA hB hBD hq hqD hfD k h hh hζnonneg initial u g hdu hu
  have hLam : 0 ≤ Lam := (le_of_lt hlam).trans hlamLam
  let hχshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω :=
    mapsTo_add_smul_basisVec_of_spatialCoordinateShiftCarrier_subset hcarrier k hh
  let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
    intro y hy
    apply subset_tsupport
    change χ y ≠ 0
    rw [χ.eq_one_on_inner y hy]
    exact one_ne_zero
  let hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω := hχshift.mono_left hηχ
  let A : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
    localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
  let Gv : ℝ → PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
    fun τ => gradientCLM hΩ (A (u τ))
  let Wv : ℝ → PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
    fun τ => cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h (u τ)
  have hparent' := hparent Lam a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hUpper
    hA hB hBD hq hqD hfD k h hh hζnonneg initial u g hdu hu
  have hGsq : Integrable (fun τ => ‖Gv τ‖ ^ 2) (reverseTimeVolume (r₁ - r₀)) := by
    exact integrable_norm_sq_timewise_apply hΩ (r₁ - r₀) ((gradientCLM hΩ).comp A) u
  have hWsq : Integrable (fun τ => ‖Wv τ‖ ^ 2) (reverseTimeVolume (r₁ - r₀)) := by
    exact integrable_norm_sq_timewise_apply hΩ (r₁ - r₀)
      (cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h) u
  have hUsq : Integrable (fun τ => ‖gradientCLM hΩ (u τ)‖ ^ 2)
      (reverseTimeVolume (r₁ - r₀)) := by
    exact integrable_norm_sq_timewise_apply hΩ (r₁ - r₀) (gradientCLM hΩ) u
  have hhalf : Integrable (fun τ => ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2))
      (reverseTimeVolume (r₁ - r₀)) :=
    integrable_weighted ζ hζunit (hGsq.const_mul (lam / 2))
  have hW : Integrable (fun τ => ζ τ * (Lam * ‖Wv τ‖ ^ 2))
      (reverseTimeVolume (r₁ - r₀)) :=
    integrable_weighted ζ hζunit (hWsq.const_mul Lam)
  have hcutoff : Integrable (fun τ => ζ τ *
      (Lam * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2))
      (reverseTimeVolume (r₁ - r₀)) :=
    integrable_weighted ζ hζunit (hUsq.const_mul (Lam * Kη ^ 2))
  have hparentBulk : Integrable (fun τ => ζ τ *
      ((lam / 2) * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2))
      (reverseTimeVolume (r₁ - r₀)) := by
    simpa only [Pi.sub_def, mul_sub] using hhalf.sub hW
  have htargetBulk : Integrable (fun τ => ζ τ *
      ((lam / 2) * ‖Gv τ‖ ^ 2 -
        Lam * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2))
      (reverseTimeVolume (r₁ - r₀)) := by
    simpa only [Pi.sub_def, mul_sub] using hhalf.sub hcutoff
  have hpoint : ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀),
      ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2 -
        Lam * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2) ≤
      ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2) := by
    filter_upwards [hζnonneg] with τ hζτ
    have hcontrol : Lam * ‖Wv τ‖ ^ 2 ≤
        Lam * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2 := by
      calc
        Lam * ‖Wv τ‖ ^ 2 ≤ Lam * (Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left
            (norm_sq_cutoffGradientSpatialDifferenceQuotientH10CLM_apply_le_gradient
              hΩ η χ k h hχshift (u τ)) hLam
        _ = Lam * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2 := by ring
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left hcontrol _) hζτ
  have hbulk :
      (∫ τ, ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2 -
        Lam * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2)
        ∂reverseTimeVolume (r₁ - r₀)) ≤
      ∫ τ, ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
        ∂reverseTimeVolume (r₁ - r₀) :=
    integral_mono_ae htargetBulk hparentBulk hpoint
  change
    -(1 / 2 : ℝ) *
        (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * ζ.deriv τ
          ∂reverseTimeVolume (r₁ - r₀)) +
      (∫ τ, ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2 -
        Lam * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2)
        ∂reverseTimeVolume (r₁ - r₀)) ≤
      ∫ τ, ζ τ * (C_lam * (1 + ‖u τ‖ ^ 2)) ∂reverseTimeVolume (r₁ - r₀)
  change
    -(1 / 2 : ℝ) *
        (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * ζ.deriv τ
          ∂reverseTimeVolume (r₁ - r₀)) +
      (∫ τ, ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
        ∂reverseTimeVolume (r₁ - r₀)) ≤
      ∫ τ, ζ τ * (C_lam * (1 + ‖u τ‖ ^ 2)) ∂reverseTimeVolume (r₁ - r₀) at hparent'
  calc
    -(1 / 2 : ℝ) *
        (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * ζ.deriv τ
          ∂reverseTimeVolume (r₁ - r₀)) +
        (∫ τ, ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2 -
          Lam * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2)
          ∂reverseTimeVolume (r₁ - r₀)) ≤
        -(1 / 2 : ℝ) *
          (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * ζ.deriv τ
            ∂reverseTimeVolume (r₁ - r₀)) +
          (∫ τ, ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
            ∂reverseTimeVolume (r₁ - r₀)) :=
      add_le_add_right hbulk _
    _ ≤ ∫ τ, ζ τ * (C_lam * (1 + ‖u τ‖ ^ 2))
        ∂reverseTimeVolume (r₁ - r₀) := hparent'

/-- The integrated cutoff-control H10 inequality has a Young constant uniform
in the reverse-time scalar test and all data satisfying the supplied literal
majorants. -/
theorem
  exists_uniform_timeTest_integral_h10Commutator_add_halfCoercive_le_cutoffControl_of_majorants
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (delta : ℝ)
    (hcarrier : spatialCoordinateShiftCarrier (tsupport χ.toFun) delta ⊆ Ω)
    (lam : ℝ) (hlam : 0 < lam) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C_lam : ℝ, 0 ≤ C_lam ∧
      ∀ (ζ : ReverseTimeScalarTest (r₁ - r₀))
        (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1),
      ∀ (Lam : ℝ) (hlamLam : lam ≤ Lam)
        (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
        (c F : ℝ → PDE.Vec d → ℝ),
        ∀ (haSmooth : IsSmoothOnNeighborhood
              (fun z : TimeVelocity d => a z.1 z.2)
              (scalarParabolicClosedCylinder r₀ r₁ Ω))
          (hbSmooth : IsSmoothOnNeighborhood
              (fun z : TimeVelocity d => b z.1 z.2)
              (scalarParabolicClosedCylinder r₀ r₁ Ω))
          (hcSmooth : IsSmoothOnNeighborhood
              (fun z : TimeVelocity d => c z.1 z.2)
              (scalarParabolicClosedCylinder r₀ r₁ Ω))
          (hFSmooth : IsSmoothOnNeighborhood
              (fun z : TimeVelocity d => F z.1 z.2)
              (scalarParabolicClosedCylinder r₀ r₁ Ω))
          (hLower : ∀ z : TimeVelocity d,
            z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
              lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
          (hUpper : ∀ z : TimeVelocity d,
            z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
              a z.1 z.2 ≤ Lam • (1 : PDE.Mat d))
          (hA : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) delta,
            spatialMatrixFDerivFrobeniusNorm
              (fun w : TimeVelocity d =>
                reverseTimeCoefficient r₁ a w.1 w.2) z ≤ M)
          (hB : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) delta,
            PDE.vecEuclideanNorm
              (reverseTimeDivergenceDrift r₁ a b z.1 z.2) ≤ M)
          (hBD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) delta,
            spatialVectorFDerivFrobeniusNorm
              (fun w : TimeVelocity d =>
                reverseTimeDivergenceDrift r₁ a b w.1 w.2) z ≤ M)
          (hq : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) delta,
            |-(reverseTimeScalarCoefficient r₁ c z.1 z.2)| ≤ M)
          (hqD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) delta,
            spatialScalarFDerivEuclideanNorm
              (fun w : TimeVelocity d =>
                -(reverseTimeScalarCoefficient r₁ c w.1 w.2)) z ≤ M)
          (hfD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) delta,
            spatialScalarFDerivEuclideanNorm
              (fun w : TimeVelocity d =>
                -(reverseTimeScalarCoefficient r₁ F w.1 w.2)) z ≤ M),
        ∀ (k : Fin d) (h : ℝ) (hh : |h| ≤ delta)
          (hζnonneg : ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀), 0 ≤ ζ τ)
          (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
          (u : ReverseTimeL2V hΩ (r₁ - r₀))
          (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
          (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
            (sub_pos.mpr h₀₁) u g)
          (hu : IsReverseTimeVariationalEnergySolution
            r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth initial u g hdu),
          let hχshift : Set.MapsTo
              (fun y : PDE.Vec d => y + h • PDE.basisVec k)
              (tsupport χ.toFun) Ω :=
            mapsTo_add_smul_basisVec_of_spatialCoordinateShiftCarrier_subset
              hcarrier k hh
          let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
            intro y hy
            apply subset_tsupport
            change χ y ≠ 0
            rw [χ.eq_one_on_inner y hy]
            exact one_ne_zero
          let hηshift : Set.MapsTo
              (fun y : PDE.Vec d => y + h • PDE.basisVec k)
              (tsupport η.toFun) Ω :=
            hχshift.mono_left hηχ
          let A : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
            localizedSpatialDifferenceQuotientH10CLM
              hΩ η k h η.tsupport_subset hηshift
          let Gv : ℝ → PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
            fun τ => gradientCLM hΩ (A (u τ))
          (-(1 / 2 : ℝ) *
              (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * ζ.deriv τ
                ∂reverseTimeVolume (r₁ - r₀)) +
            (∫ τ, ζ τ *
                ((lam / 2) * ‖Gv τ‖ ^ 2 -
                  Lam * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2)
                ∂reverseTimeVolume (r₁ - r₀)) ≤
            (∫ τ, ζ τ * (C_lam * (1 + ‖u τ‖ ^ 2))
              ∂reverseTimeVolume (r₁ - r₀))) := by
  obtain ⟨C_lam, hC_lam, hparent⟩ :=
  exists_uniform_timeTest_integral_h10Commutator_add_halfCoercive_le_nonprincipalYoung_of_majorants
    r₀ r₁ h₀₁ hΩ hΩbounded η χ delta hcarrier lam hlam M hM
  refine ⟨C_lam, hC_lam, ?_⟩
  intro zeta hzetaunit Lam hlamLam a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hUpper
    hA hB hBD hq hqD hfD k h hh hζnonneg initial u g hdu hu
  have hLam : 0 ≤ Lam := (le_of_lt hlam).trans hlamLam
  let hχshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω :=
    mapsTo_add_smul_basisVec_of_spatialCoordinateShiftCarrier_subset hcarrier k hh
  let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
    intro y hy
    apply subset_tsupport
    change χ y ≠ 0
    rw [χ.eq_one_on_inner y hy]
    exact one_ne_zero
  let hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω := hχshift.mono_left hηχ
  let A : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
    localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
  let Gv : ℝ → PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
    fun τ => gradientCLM hΩ (A (u τ))
  let Wv : ℝ → PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
    fun τ => cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h (u τ)
  have hparent' := hparent zeta hzetaunit Lam a b c F haSmooth hbSmooth hcSmooth hFSmooth
    hLower hUpper hA hB hBD hq hqD hfD k h hh hζnonneg initial u g hdu hu
  have hGsq : Integrable (fun τ => ‖Gv τ‖ ^ 2) (reverseTimeVolume (r₁ - r₀)) := by
    exact integrable_norm_sq_timewise_apply hΩ (r₁ - r₀) ((gradientCLM hΩ).comp A) u
  have hWsq : Integrable (fun τ => ‖Wv τ‖ ^ 2) (reverseTimeVolume (r₁ - r₀)) := by
    exact integrable_norm_sq_timewise_apply hΩ (r₁ - r₀)
      (cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h) u
  have hUsq : Integrable (fun τ => ‖gradientCLM hΩ (u τ)‖ ^ 2)
      (reverseTimeVolume (r₁ - r₀)) := by
    exact integrable_norm_sq_timewise_apply hΩ (r₁ - r₀) (gradientCLM hΩ) u
  have hhalf : Integrable (fun τ => zeta τ * ((lam / 2) * ‖Gv τ‖ ^ 2))
      (reverseTimeVolume (r₁ - r₀)) :=
    integrable_weighted zeta hzetaunit (hGsq.const_mul (lam / 2))
  have hW : Integrable (fun τ => zeta τ * (Lam * ‖Wv τ‖ ^ 2))
      (reverseTimeVolume (r₁ - r₀)) :=
    integrable_weighted zeta hzetaunit (hWsq.const_mul Lam)
  have hcutoff : Integrable (fun τ => zeta τ *
      (Lam * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2))
      (reverseTimeVolume (r₁ - r₀)) :=
    integrable_weighted zeta hzetaunit (hUsq.const_mul (Lam * Kη ^ 2))
  have hparentBulk : Integrable (fun τ => zeta τ *
      ((lam / 2) * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2))
      (reverseTimeVolume (r₁ - r₀)) := by
    simpa only [Pi.sub_def, mul_sub] using hhalf.sub hW
  have htargetBulk : Integrable (fun τ => zeta τ *
      ((lam / 2) * ‖Gv τ‖ ^ 2 -
        Lam * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2))
      (reverseTimeVolume (r₁ - r₀)) := by
    simpa only [Pi.sub_def, mul_sub] using hhalf.sub hcutoff
  have hpoint : ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀),
      zeta τ * ((lam / 2) * ‖Gv τ‖ ^ 2 -
        Lam * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2) ≤
      zeta τ * ((lam / 2) * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2) := by
    filter_upwards [hζnonneg] with τ hζτ
    have hcontrol : Lam * ‖Wv τ‖ ^ 2 ≤
        Lam * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2 := by
      calc
        Lam * ‖Wv τ‖ ^ 2 ≤ Lam * (Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left
            (norm_sq_cutoffGradientSpatialDifferenceQuotientH10CLM_apply_le_gradient
              hΩ η χ k h hχshift (u τ)) hLam
        _ = Lam * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2 := by ring
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left hcontrol _) hζτ
  have hbulk :
      (∫ τ, zeta τ * ((lam / 2) * ‖Gv τ‖ ^ 2 -
        Lam * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2)
        ∂reverseTimeVolume (r₁ - r₀)) ≤
      ∫ τ, zeta τ * ((lam / 2) * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
        ∂reverseTimeVolume (r₁ - r₀) :=
    integral_mono_ae htargetBulk hparentBulk hpoint
  change
    -(1 / 2 : ℝ) *
        (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * zeta.deriv τ
          ∂reverseTimeVolume (r₁ - r₀)) +
      (∫ τ, zeta τ * ((lam / 2) * ‖Gv τ‖ ^ 2 -
        Lam * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2)
        ∂reverseTimeVolume (r₁ - r₀)) ≤
      ∫ τ, zeta τ * (C_lam * (1 + ‖u τ‖ ^ 2)) ∂reverseTimeVolume (r₁ - r₀)
  change
    -(1 / 2 : ℝ) *
        (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * zeta.deriv τ
          ∂reverseTimeVolume (r₁ - r₀)) +
      (∫ τ, zeta τ * ((lam / 2) * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
        ∂reverseTimeVolume (r₁ - r₀)) ≤
      ∫ τ, zeta τ * (C_lam * (1 + ‖u τ‖ ^ 2)) ∂reverseTimeVolume (r₁ - r₀) at hparent'
  calc
    -(1 / 2 : ℝ) *
        (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * zeta.deriv τ
          ∂reverseTimeVolume (r₁ - r₀)) +
        (∫ τ, zeta τ * ((lam / 2) * ‖Gv τ‖ ^ 2 -
          Lam * Kη ^ 2 * ‖gradientCLM hΩ (u τ)‖ ^ 2)
          ∂reverseTimeVolume (r₁ - r₀)) ≤
        -(1 / 2 : ℝ) *
          (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * zeta.deriv τ
            ∂reverseTimeVolume (r₁ - r₀)) +
          (∫ τ, zeta τ * ((lam / 2) * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
            ∂reverseTimeVolume (r₁ - r₀)) :=
      add_le_add_right hbulk _
    _ ≤ ∫ τ, zeta τ * (C_lam * (1 + ‖u τ‖ ^ 2))
        ∂reverseTimeVolume (r₁ - r₀) := hparent'

end IsReverseTimeVariationalEnergySolution

end HypoellipticAleksandrov.Parabolic.Dirichlet
