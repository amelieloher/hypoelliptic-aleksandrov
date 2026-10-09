module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10IntegratedCoerciveConsequence

/-!
# Integrated localized H10 half absorption

This module derives the positive-lower-bound half-absorption corollary from
the integrated H10 coercive consequence.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.Elementwise

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

namespace IsReverseTimeVariationalEnergySolution

/-- The reducible exact output proposition of integrated positive-lower-bound
H10 half absorption.  This names a conclusion and is not an assumption package. -/
abbrev integratedH10HalfCoerciveConsequenceOutput
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
                let Wv : ℝ → PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
                  fun τ =>
                    cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h (u τ)
                (-(1 / 2 : ℝ) *
                    (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * ζ.deriv τ
                      ∂reverseTimeVolume (r₁ - r₀)) +
                  (∫ τ, ζ τ *
                    ((lam / 2) * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
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

/-- A positive lower ellipticity bound absorbs half of the integrated H10
coercive term into the nonprincipal Young remainder. -/
theorem exists_smallStep_integral_h10Commutator_add_halfCoerciveTerm_le_nonprincipalYoung
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
    integratedH10HalfCoerciveConsequenceOutput
      r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth
      F hFSmooth ζ hζunit η χ := by
  obtain ⟨δ, hδ, hparent⟩ :=
    exists_smallStep_integral_h10Commutator_add_coerciveTerm_le_nonprincipalYoung
      r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth F hFSmooth ζ hζunit η χ
  refine ⟨δ, hδ, ?_⟩
  intro lam hlam
  obtain ⟨C_lam, hC_lam, hparent⟩ := hparent (lam / 2) (half_pos hlam)
  refine ⟨C_lam, hC_lam, ?_⟩
  intro Lam hLower hUpper k h hh
  obtain ⟨hχshift, hparent⟩ := hparent lam Lam hLower hUpper k h hh
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
  have hUsq : Integrable (fun τ => ‖u τ‖ ^ 2) (reverseTimeVolume (r₁ - r₀)) := by
    simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) u u
  have hhalf : Integrable (fun τ => ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2))
      (reverseTimeVolume (r₁ - r₀)) :=
    integrable_weighted ζ hζunit (hGsq.const_mul (lam / 2))
  have hW : Integrable (fun τ => ζ τ * (Lam * ‖Wv τ‖ ^ 2))
      (reverseTimeVolume (r₁ - r₀)) :=
    integrable_weighted ζ hζunit (hWsq.const_mul Lam)
  letI : IsFiniteMeasure (reverseTimeVolume (r₁ - r₀)) := by
    change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) (r₁ - r₀)))
    infer_instance
  have hOne : Integrable (fun _ : ℝ => (1 : ℝ)) (reverseTimeVolume (r₁ - r₀)) :=
    integrable_const _
  have hC : Integrable (fun τ => ζ τ * (C_lam * (1 + ‖u τ‖ ^ 2)))
      (reverseTimeVolume (r₁ - r₀)) :=
    integrable_weighted ζ hζunit ((hOne.add hUsq).const_mul C_lam)
  have htarget : Integrable (fun τ => ζ τ *
      ((lam / 2) * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2))
      (reverseTimeVolume (r₁ - r₀)) := by
    simpa only [Pi.sub_def, mul_sub] using hhalf.sub hW
  have hbulk_split :
      (∫ τ, ζ τ * (lam * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
        ∂reverseTimeVolume (r₁ - r₀)) =
      (∫ τ, ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
        ∂reverseTimeVolume (r₁ - r₀)) +
      ∫ τ, ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2) ∂reverseTimeVolume (r₁ - r₀) := by
    rw [← integral_add htarget hhalf]
    apply integral_congr_ae
    filter_upwards with τ
    ring
  have hyoung_split :
      (∫ τ, ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2 + C_lam * (1 + ‖u τ‖ ^ 2))
        ∂reverseTimeVolume (r₁ - r₀)) =
      (∫ τ, ζ τ * (C_lam * (1 + ‖u τ‖ ^ 2)) ∂reverseTimeVolume (r₁ - r₀)) +
      ∫ τ, ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2) ∂reverseTimeVolume (r₁ - r₀) := by
    rw [← integral_add hC hhalf]
    apply integral_congr_ae
    filter_upwards with τ
    ring
  change
    -(1 / 2 : ℝ) *
        (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * ζ.deriv τ
          ∂reverseTimeVolume (r₁ - r₀)) +
      (∫ τ, ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
        ∂reverseTimeVolume (r₁ - r₀)) ≤
      ∫ τ, ζ τ * (C_lam * (1 + ‖u τ‖ ^ 2)) ∂reverseTimeVolume (r₁ - r₀)
  change
    -(1 / 2 : ℝ) *
        (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * ζ.deriv τ
          ∂reverseTimeVolume (r₁ - r₀)) +
      (∫ τ, ζ τ * (lam * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
        ∂reverseTimeVolume (r₁ - r₀)) ≤
      ∫ τ, ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2 + C_lam * (1 + ‖u τ‖ ^ 2))
        ∂reverseTimeVolume (r₁ - r₀) at hparent'
  let E : ℝ := -(1 / 2 : ℝ) *
    (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * ζ.deriv τ ∂reverseTimeVolume (r₁ - r₀))
  let Ibulk : ℝ := ∫ τ, ζ τ * (lam * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
    ∂reverseTimeVolume (r₁ - r₀)
  let Itarget : ℝ := ∫ τ, ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
    ∂reverseTimeVolume (r₁ - r₀)
  let Ihalf : ℝ := ∫ τ, ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2)
    ∂reverseTimeVolume (r₁ - r₀)
  let Iyoung : ℝ := ∫ τ, ζ τ *
    ((lam / 2) * ‖Gv τ‖ ^ 2 + C_lam * (1 + ‖u τ‖ ^ 2)) ∂reverseTimeVolume (r₁ - r₀)
  let IC : ℝ := ∫ τ, ζ τ * (C_lam * (1 + ‖u τ‖ ^ 2))
    ∂reverseTimeVolume (r₁ - r₀)
  change E + Itarget ≤ IC
  change E + Ibulk ≤ Iyoung at hparent'
  change Ibulk = Itarget + Ihalf at hbulk_split
  change Iyoung = IC + Ihalf at hyoung_split
  rw [hbulk_split, hyoung_split] at hparent'
  linarith

/-- The integrated half-coercive H10 inequality has a constant uniform over
all coefficient data satisfying the supplied literal majorants. -/
theorem exists_uniform_integral_h10Commutator_add_halfCoerciveTerm_le_nonprincipalYoung_of_majorants
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (ζ : ReverseTimeScalarTest (r₁ - r₀)) (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1)
    (delta : ℝ)
    (hcarrier : spatialCoordinateShiftCarrier (tsupport χ.toFun) delta ⊆ Ω)
    (lam : ℝ) (hlam : 0 < lam) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C_lam : ℝ, 0 ≤ C_lam ∧
      ∀ (Lam : ℝ) (a : CoefficientField d)
        (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ),
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
              (fun w : TimeVelocity d => reverseTimeCoefficient r₁ a w.1 w.2) z ≤ M)
          (hB : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) delta,
            PDE.vecEuclideanNorm (reverseTimeDivergenceDrift r₁ a b z.1 z.2) ≤ M)
          (hBD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) delta,
            spatialVectorFDerivFrobeniusNorm
              (fun w : TimeVelocity d => reverseTimeDivergenceDrift r₁ a b w.1 w.2) z ≤ M)
          (hq : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) delta,
            |-(reverseTimeScalarCoefficient r₁ c z.1 z.2)| ≤ M)
          (hqD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) delta,
            spatialScalarFDerivEuclideanNorm
              (fun w : TimeVelocity d => -(reverseTimeScalarCoefficient r₁ c w.1 w.2)) z ≤ M)
          (hfD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) delta,
            spatialScalarFDerivEuclideanNorm
              (fun w : TimeVelocity d => -(reverseTimeScalarCoefficient r₁ F w.1 w.2)) z ≤ M),
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
          let Wv : ℝ → PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
            fun τ => cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h (u τ)
          (-(1 / 2 : ℝ) *
              (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * ζ.deriv τ
                ∂reverseTimeVolume (r₁ - r₀)) +
            (∫ τ, ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
              ∂reverseTimeVolume (r₁ - r₀)) ≤
            (∫ τ, ζ τ * (C_lam * (1 + ‖u τ‖ ^ 2))
              ∂reverseTimeVolume (r₁ - r₀))) := by
  obtain ⟨C_lam, hC_lam, hparent⟩ :=
    exists_uniform_integral_h10Commutator_add_coerciveTerm_le_nonprincipalYoung_of_majorants
      r₀ r₁ h₀₁ hΩ hΩbounded η χ ζ hζunit delta hcarrier M hM
        (lam / 2) (half_pos hlam)
  refine ⟨C_lam, hC_lam, ?_⟩
  intro Lam a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hUpper
    hA hB hBD hq hqD hfD k h hh hζnonneg initial u g hdu hu
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
  have hparent' := hparent lam Lam a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hUpper
    hA hB hBD hq hqD hfD k h hh hζnonneg initial u g hdu hu
  have hGsq : Integrable (fun τ => ‖Gv τ‖ ^ 2) (reverseTimeVolume (r₁ - r₀)) := by
    exact integrable_norm_sq_timewise_apply hΩ (r₁ - r₀) ((gradientCLM hΩ).comp A) u
  have hWsq : Integrable (fun τ => ‖Wv τ‖ ^ 2) (reverseTimeVolume (r₁ - r₀)) := by
    exact integrable_norm_sq_timewise_apply hΩ (r₁ - r₀)
      (cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h) u
  have hUsq : Integrable (fun τ => ‖u τ‖ ^ 2) (reverseTimeVolume (r₁ - r₀)) := by
    simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) u u
  have hhalf : Integrable (fun τ => ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2))
      (reverseTimeVolume (r₁ - r₀)) :=
    integrable_weighted ζ hζunit (hGsq.const_mul (lam / 2))
  have hW : Integrable (fun τ => ζ τ * (Lam * ‖Wv τ‖ ^ 2))
      (reverseTimeVolume (r₁ - r₀)) :=
    integrable_weighted ζ hζunit (hWsq.const_mul Lam)
  letI : IsFiniteMeasure (reverseTimeVolume (r₁ - r₀)) := by
    change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) (r₁ - r₀)))
    infer_instance
  have hOne : Integrable (fun _ : ℝ => (1 : ℝ)) (reverseTimeVolume (r₁ - r₀)) :=
    integrable_const _
  have hC : Integrable (fun τ => ζ τ * (C_lam * (1 + ‖u τ‖ ^ 2)))
      (reverseTimeVolume (r₁ - r₀)) :=
    integrable_weighted ζ hζunit ((hOne.add hUsq).const_mul C_lam)
  have htarget : Integrable (fun τ => ζ τ *
      ((lam / 2) * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2))
      (reverseTimeVolume (r₁ - r₀)) := by
    simpa only [Pi.sub_def, mul_sub] using hhalf.sub hW
  have hbulk_split :
      (∫ τ, ζ τ * (lam * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
        ∂reverseTimeVolume (r₁ - r₀)) =
      (∫ τ, ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
        ∂reverseTimeVolume (r₁ - r₀)) +
      ∫ τ, ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2) ∂reverseTimeVolume (r₁ - r₀) := by
    rw [← integral_add htarget hhalf]
    apply integral_congr_ae
    filter_upwards with τ
    ring
  have hyoung_split :
      (∫ τ, ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2 + C_lam * (1 + ‖u τ‖ ^ 2))
        ∂reverseTimeVolume (r₁ - r₀)) =
      (∫ τ, ζ τ * (C_lam * (1 + ‖u τ‖ ^ 2)) ∂reverseTimeVolume (r₁ - r₀)) +
      ∫ τ, ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2) ∂reverseTimeVolume (r₁ - r₀) := by
    rw [← integral_add hC hhalf]
    apply integral_congr_ae
    filter_upwards with τ
    ring
  change
    -(1 / 2 : ℝ) *
        (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * ζ.deriv τ
          ∂reverseTimeVolume (r₁ - r₀)) +
      (∫ τ, ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
        ∂reverseTimeVolume (r₁ - r₀)) ≤
      ∫ τ, ζ τ * (C_lam * (1 + ‖u τ‖ ^ 2)) ∂reverseTimeVolume (r₁ - r₀)
  change
    -(1 / 2 : ℝ) *
        (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * ζ.deriv τ
          ∂reverseTimeVolume (r₁ - r₀)) +
      (∫ τ, ζ τ * (lam * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
        ∂reverseTimeVolume (r₁ - r₀)) ≤
      ∫ τ, ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2 + C_lam * (1 + ‖u τ‖ ^ 2))
        ∂reverseTimeVolume (r₁ - r₀) at hparent'
  let E : ℝ := -(1 / 2 : ℝ) *
    (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * ζ.deriv τ ∂reverseTimeVolume (r₁ - r₀))
  let Ibulk : ℝ := ∫ τ, ζ τ * (lam * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
    ∂reverseTimeVolume (r₁ - r₀)
  let Itarget : ℝ := ∫ τ, ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
    ∂reverseTimeVolume (r₁ - r₀)
  let Ihalf : ℝ := ∫ τ, ζ τ * ((lam / 2) * ‖Gv τ‖ ^ 2)
    ∂reverseTimeVolume (r₁ - r₀)
  let Iyoung : ℝ := ∫ τ, ζ τ *
    ((lam / 2) * ‖Gv τ‖ ^ 2 + C_lam * (1 + ‖u τ‖ ^ 2)) ∂reverseTimeVolume (r₁ - r₀)
  let IC : ℝ := ∫ τ, ζ τ * (C_lam * (1 + ‖u τ‖ ^ 2))
    ∂reverseTimeVolume (r₁ - r₀)
  change E + Itarget ≤ IC
  change E + Ibulk ≤ Iyoung at hparent'
  change Ibulk = Itarget + Ihalf at hbulk_split
  change Iyoung = IC + Ihalf at hyoung_split
  rw [hbulk_split, hyoung_split] at hparent'
  linarith

/-- The integrated half-coercive H10 inequality has a Young constant uniform
in the reverse-time scalar test and all data satisfying the supplied literal
majorants. -/
theorem
  exists_uniform_timeTest_integral_h10Commutator_add_halfCoercive_le_nonprincipalYoung_of_majorants
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
      ∀ (Lam : ℝ) (a : CoefficientField d)
        (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ),
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
          let Wv : ℝ → PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
            fun τ =>
              cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h (u τ)
          (-(1 / 2 : ℝ) *
              (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * ζ.deriv τ
                ∂reverseTimeVolume (r₁ - r₀)) +
            (∫ τ, ζ τ *
              ((lam / 2) * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
              ∂reverseTimeVolume (r₁ - r₀)) ≤
            (∫ τ, ζ τ * (C_lam * (1 + ‖u τ‖ ^ 2))
              ∂reverseTimeVolume (r₁ - r₀))) := by
  obtain ⟨C_lam, hC_lam, hparent⟩ :=
   exists_uniform_timeTest_integral_h10Commutator_add_coerciveTerm_le_nonprincipalYoung_of_majorants
     r₀ r₁ h₀₁ hΩ hΩbounded η χ delta hcarrier M hM
       (lam / 2) (half_pos hlam)
  refine ⟨C_lam, hC_lam, ?_⟩
  intro zeta hzetaunit Lam a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hUpper
    hA hB hBD hq hqD hfD k h hh hζnonneg initial u g hdu hu
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
  have hparent' := hparent zeta hzetaunit lam Lam a b c F haSmooth hbSmooth hcSmooth hFSmooth
    hLower hUpper hA hB hBD hq hqD hfD k h hh hζnonneg initial u g hdu hu
  have hGsq : Integrable (fun τ => ‖Gv τ‖ ^ 2) (reverseTimeVolume (r₁ - r₀)) := by
    exact integrable_norm_sq_timewise_apply hΩ (r₁ - r₀) ((gradientCLM hΩ).comp A) u
  have hWsq : Integrable (fun τ => ‖Wv τ‖ ^ 2) (reverseTimeVolume (r₁ - r₀)) := by
    exact integrable_norm_sq_timewise_apply hΩ (r₁ - r₀)
      (cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h) u
  have hUsq : Integrable (fun τ => ‖u τ‖ ^ 2) (reverseTimeVolume (r₁ - r₀)) := by
    simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) u u
  have hhalf : Integrable (fun τ => zeta τ * ((lam / 2) * ‖Gv τ‖ ^ 2))
      (reverseTimeVolume (r₁ - r₀)) :=
    integrable_weighted zeta hzetaunit (hGsq.const_mul (lam / 2))
  have hW : Integrable (fun τ => zeta τ * (Lam * ‖Wv τ‖ ^ 2))
      (reverseTimeVolume (r₁ - r₀)) :=
    integrable_weighted zeta hzetaunit (hWsq.const_mul Lam)
  letI : IsFiniteMeasure (reverseTimeVolume (r₁ - r₀)) := by
    change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) (r₁ - r₀)))
    infer_instance
  have hOne : Integrable (fun _ : ℝ => (1 : ℝ)) (reverseTimeVolume (r₁ - r₀)) :=
    integrable_const _
  have hC : Integrable (fun τ => zeta τ * (C_lam * (1 + ‖u τ‖ ^ 2)))
      (reverseTimeVolume (r₁ - r₀)) :=
    integrable_weighted zeta hzetaunit ((hOne.add hUsq).const_mul C_lam)
  have htarget : Integrable (fun τ => zeta τ *
      ((lam / 2) * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2))
      (reverseTimeVolume (r₁ - r₀)) := by
    simpa only [Pi.sub_def, mul_sub] using hhalf.sub hW
  have hbulk_split :
      (∫ τ, zeta τ * (lam * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
        ∂reverseTimeVolume (r₁ - r₀)) =
      (∫ τ, zeta τ * ((lam / 2) * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
        ∂reverseTimeVolume (r₁ - r₀)) +
      ∫ τ, zeta τ * ((lam / 2) * ‖Gv τ‖ ^ 2) ∂reverseTimeVolume (r₁ - r₀) := by
    rw [← integral_add htarget hhalf]
    apply integral_congr_ae
    filter_upwards with τ
    ring
  have hyoung_split :
      (∫ τ, zeta τ * ((lam / 2) * ‖Gv τ‖ ^ 2 + C_lam * (1 + ‖u τ‖ ^ 2))
        ∂reverseTimeVolume (r₁ - r₀)) =
      (∫ τ, zeta τ * (C_lam * (1 + ‖u τ‖ ^ 2)) ∂reverseTimeVolume (r₁ - r₀)) +
      ∫ τ, zeta τ * ((lam / 2) * ‖Gv τ‖ ^ 2) ∂reverseTimeVolume (r₁ - r₀) := by
    rw [← integral_add hC hhalf]
    apply integral_congr_ae
    filter_upwards with τ
    ring
  change
    -(1 / 2 : ℝ) *
        (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * zeta.deriv τ
          ∂reverseTimeVolume (r₁ - r₀)) +
      (∫ τ, zeta τ * ((lam / 2) * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
        ∂reverseTimeVolume (r₁ - r₀)) ≤
      ∫ τ, zeta τ * (C_lam * (1 + ‖u τ‖ ^ 2)) ∂reverseTimeVolume (r₁ - r₀)
  change
    -(1 / 2 : ℝ) *
        (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * zeta.deriv τ
          ∂reverseTimeVolume (r₁ - r₀)) +
      (∫ τ, zeta τ * (lam * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
        ∂reverseTimeVolume (r₁ - r₀)) ≤
      ∫ τ, zeta τ * ((lam / 2) * ‖Gv τ‖ ^ 2 + C_lam * (1 + ‖u τ‖ ^ 2))
        ∂reverseTimeVolume (r₁ - r₀) at hparent'
  let E : ℝ := -(1 / 2 : ℝ) *
    (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * zeta.deriv τ ∂reverseTimeVolume (r₁ - r₀))
  let Ibulk : ℝ := ∫ τ, zeta τ * (lam * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
    ∂reverseTimeVolume (r₁ - r₀)
  let Itarget : ℝ := ∫ τ, zeta τ * ((lam / 2) * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
    ∂reverseTimeVolume (r₁ - r₀)
  let Ihalf : ℝ := ∫ τ, zeta τ * ((lam / 2) * ‖Gv τ‖ ^ 2)
    ∂reverseTimeVolume (r₁ - r₀)
  let Iyoung : ℝ := ∫ τ, zeta τ *
    ((lam / 2) * ‖Gv τ‖ ^ 2 + C_lam * (1 + ‖u τ‖ ^ 2)) ∂reverseTimeVolume (r₁ - r₀)
  let IC : ℝ := ∫ τ, zeta τ * (C_lam * (1 + ‖u τ‖ ^ 2))
    ∂reverseTimeVolume (r₁ - r₀)
  change E + Itarget ≤ IC
  change E + Ibulk ≤ Iyoung at hparent'
  change Ibulk = Itarget + Ihalf at hbulk_split
  change Iyoung = IC + Ihalf at hyoung_split
  rw [hbulk_split, hyoung_split] at hparent'
  linarith

end IsReverseTimeVariationalEnergySolution

end HypoellipticAleksandrov.Parabolic.Dirichlet
