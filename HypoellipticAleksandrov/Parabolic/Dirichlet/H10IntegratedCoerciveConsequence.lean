module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10CoerciveConsequence
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientVariationalWeightedEnergy

/-!
# Integrated localized H10 coercive consequence

This module integrates the fixed-slice coercive consequence along a
reverse-time variational energy solution.  The raw fixed-slice residual is
identified almost everywhere with the Bochner residual before integration.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.Elementwise

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

namespace IsReverseTimeVariationalEnergySolution

private theorem eta_tsupport_subset_chi
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ) :
    tsupport η.toFun ⊆ tsupport χ.toFun := by
  intro y hy
  apply subset_tsupport
  change χ y ≠ 0
  rw [χ.eq_one_on_inner y hy]
  exact one_ne_zero

private def parentFixedSlice
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (ε Cε lam Lam : ℝ) (k : Fin d) (h : ℝ)
    (hχshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω) (τ : ℝ) (u : H10HilbertGraph hΩ) : Prop :=
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
  let B : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
    localizedSpatialDifferenceQuotientEnergyTestH10CLM hΩ η k h η.tsupport_subset hηshift
  let Gv : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) := gradientCLM hΩ (A u)
  let Wv : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
    cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h u
  let Q : ℝ := ζ τ *
    (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (B u) -
      reverseTimeSpatialForm hΩ r₁ τ a b c u (B u))
  Q + ζ τ * (lam * ‖Gv‖ ^ 2 - Lam * ‖Wv‖ ^ 2) ≤
    ζ τ * (ε * ‖Gv‖ ^ 2 + Cε * (1 + ‖u‖ ^ 2))

private def parentOutput
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (_ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (_hb : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (_hc : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (F : ℝ → PDE.Vec d → ℝ)
    (hF : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (ζ : ReverseTimeScalarTest (r₁ - r₀)) (_hζ : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, 0 ≤ Cε ∧
    ∀ (lam Lam : ℝ)
      (_hLower : ∀ z : TimeVelocity d,
        z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
      (_hUpper : ∀ z : TimeVelocity d,
        z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → a z.1 z.2 ≤ Lam • (1 : PDE.Mat d)),
      ∀ (k : Fin d) (h : ℝ), |h| ≤ δ →
        ∃ hχshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
          (tsupport χ.toFun) Ω, ∀ (τ : ℝ) (_hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
          (_hζnonneg : 0 ≤ ζ τ) (u : H10HilbertGraph hΩ),
          parentFixedSlice r₀ r₁ h₀₁ hΩ hΩbounded a b c F hF ζ η χ ε Cε lam Lam
            k h hχshift τ u

private theorem parentOutput_of_public
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hb : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hc : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (F : ℝ → PDE.Vec d → ℝ)
    (hF : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (ζ : ReverseTimeScalarTest (r₁ - r₀)) (hζ : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ) :
    parentOutput r₀ r₁ h₀₁ hΩ hΩbounded a b c ha hb hc F hF ζ hζ η χ := by
  exact exists_smallStep_h10Commutator_add_coerciveTerm_le_nonprincipalYoung
    r₀ r₁ h₀₁ hΩ hΩbounded a b c ha hb hc F hF ζ hζ η χ

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

private theorem integral_energy_term_eq_integral_residual
    {d : ℕ} {Ω : Set (PDE.Vec d)} {Kη : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hb : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hc : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (F : ℝ → PDE.Vec d → ℝ)
    (hF : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u g)
    (hu : IsReverseTimeVariationalEnergySolution
      r₀ r₁ h₀₁ hΩ hΩbounded a b c F hF initial u g hdu)
    {inner : Set (PDE.Vec d)}
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (k : Fin d) (h : ℝ)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω)
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (A B : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ)
    (hA : A = localizedSpatialDifferenceQuotientH10CLM
      hΩ η k h η.tsupport_subset hηshift)
    (hB : B = localizedSpatialDifferenceQuotientEnergyTestH10CLM
      hΩ η k h η.tsupport_subset hηshift) :
    -(1 / 2 : ℝ) *
        (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * ζ.deriv τ
          ∂reverseTimeVolume (r₁ - r₀)) =
      ∫ τ, ζ τ *
        ((reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hF τ) (B (u τ)) -
          (reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
            ha hb hc u τ) (B (u τ))) ∂reverseTimeVolume (r₁ - r₀) := by
  subst A
  subst B
  have henergy :=
    integral_localizedSpatialDifferenceQuotient_norm_sq_mul_reverseTimeScalarTest_deriv_eq
    r₀ r₁ h₀₁ hΩ hΩbounded a b c ha hb hc F hF initial u g hdu hu
      η k h η.tsupport_subset hηshift ζ
  calc
    -(1 / 2 : ℝ) *
        (∫ τ, ‖valueCLM hΩ
          (localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
            (u τ))‖ ^ 2 * ζ.deriv τ ∂reverseTimeVolume (r₁ - r₀)) =
        (1 / 2 : ℝ) *
          ∫ τ, (2 *
            ((reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hF τ)
              (localizedSpatialDifferenceQuotientEnergyTestH10CLM
                hΩ η k h η.tsupport_subset hηshift (u τ)) -
              (reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
                ha hb hc u τ)
                (localizedSpatialDifferenceQuotientEnergyTestH10CLM
                  hΩ η k h η.tsupport_subset hηshift (u τ)))) * ζ τ
            ∂reverseTimeVolume (r₁ - r₀) := by
          rw [henergy]
          ring
    _ = ∫ τ, (1 / 2 : ℝ) * ((2 *
          ((reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hF τ)
            (localizedSpatialDifferenceQuotientEnergyTestH10CLM
              hΩ η k h η.tsupport_subset hηshift (u τ)) -
            (reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
              ha hb hc u τ)
              (localizedSpatialDifferenceQuotientEnergyTestH10CLM
                hΩ η k h η.tsupport_subset hηshift (u τ)))) * ζ τ)
          ∂reverseTimeVolume (r₁ - r₀) := by
      rw [integral_const_mul]
    _ = ∫ τ, ζ τ *
        ((reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hF τ)
          (localizedSpatialDifferenceQuotientEnergyTestH10CLM
            hΩ η k h η.tsupport_subset hηshift (u τ)) -
          (reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
            ha hb hc u τ)
            (localizedSpatialDifferenceQuotientEnergyTestH10CLM
              hΩ η k h η.tsupport_subset hηshift (u τ)))
          ∂reverseTimeVolume (r₁ - r₀) := by
      apply integral_congr_ae
      filter_upwards with τ
      ring

/-- The reducible exact output proposition of the unabsorbed integrated H10
coercive consequence.  This names a conclusion and is not an assumption package. -/
abbrev integratedH10CoerciveConsequenceOutput
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
      ∀ ε : ℝ, 0 < ε →
        ∃ Cε : ℝ, 0 ≤ Cε ∧
          ∀ (lam Lam : ℝ)
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
                    (lam * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
                    ∂reverseTimeVolume (r₁ - r₀)) ≤
                  (∫ τ, ζ τ *
                    (ε * ‖Gv τ‖ ^ 2 + Cε * (1 + ‖u τ‖ ^ 2))
                    ∂reverseTimeVolume (r₁ - r₀)))

private def integratedH10Leaf
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
    (ζ : ReverseTimeScalarTest (r₁ - r₀)) (_hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (ε Cε lam Lam : ℝ) (k : Fin d) (h : ℝ)
    (hχshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω)
    (_hζnonneg : ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀), 0 ≤ ζ τ)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u g)
    (_hu : IsReverseTimeVariationalEnergySolution
      r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth initial u g hdu) : Prop :=
  let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
    intro y hy
    apply subset_tsupport
    change χ y ≠ 0
    rw [χ.eq_one_on_inner y hy]
    exact one_ne_zero
  let hηshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω := hχshift.mono_left hηχ
  let A : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
    localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
  let Gv : ℝ → PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
    fun τ => gradientCLM hΩ (A (u τ))
  let Wv : ℝ → PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
    fun τ => cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h (u τ)
  (-(1 / 2 : ℝ) *
      (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * ζ.deriv τ
        ∂reverseTimeVolume (r₁ - r₀)) +
    (∫ τ, ζ τ * (lam * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
      ∂reverseTimeVolume (r₁ - r₀)) ≤
    (∫ τ, ζ τ * (ε * ‖Gv τ‖ ^ 2 + Cε * (1 + ‖u τ‖ ^ 2))
      ∂reverseTimeVolume (r₁ - r₀)))

private def integratedH10SolutionOutput
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
    (ζ : ReverseTimeScalarTest (r₁ - r₀)) (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (ε Cε lam Lam : ℝ) (k : Fin d) (h : ℝ)
    (hχshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω) : Prop :=
  ∀ (hζnonneg : ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀), 0 ≤ ζ τ)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u g)
    (hu : IsReverseTimeVariationalEnergySolution
      r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth initial u g hdu),
    integratedH10Leaf r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth F hFSmooth
      ζ hζunit η χ ε Cε lam Lam k h hχshift hζnonneg initial u g hdu hu

private def integratedH10StepOutput
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
    (ζ : ReverseTimeScalarTest (r₁ - r₀)) (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (ε Cε δ : ℝ) : Prop :=
  ∀ (lam Lam : ℝ)
    (_hLower : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (_hUpper : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → a z.1 z.2 ≤ Lam • (1 : PDE.Mat d)),
    ∀ (k : Fin d) (h : ℝ), |h| ≤ δ →
      ∃ hχshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
        (tsupport χ.toFun) Ω,
      integratedH10SolutionOutput r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth
        F hFSmooth ζ hζunit η χ ε Cε lam Lam k h hχshift

private def integratedH10EpsilonOutput
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
    (ζ : ReverseTimeScalarTest (r₁ - r₀)) (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ) (δ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, 0 ≤ Cε ∧
    integratedH10StepOutput r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth
      F hFSmooth ζ hζunit η χ ε Cε δ

private def integratedH10OuterOutput
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
    (ζ : ReverseTimeScalarTest (r₁ - r₀)) (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧
    integratedH10EpsilonOutput r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth
      F hFSmooth ζ hζunit η χ δ

private theorem integral_add_of_integrable
    {α : Type*} [MeasurableSpace α] (μ : Measure α) {f g : α → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫ x, f x ∂μ) + ∫ x, g x ∂μ = ∫ x, f x + g x ∂μ := by
  rw [integral_add hf hg]

private theorem integratedH10Pointwise_fixedTime_scalar
    {z raw source form bochner gSq wSq uSq ε Cε lam Lam q : ℝ}
    (hslice : z * (raw - form) + z * (lam * gSq - Lam * wSq) ≤
      z * (ε * gSq + Cε * (1 + uSq)))
    (hraw : raw = q) (hsource : source = q) (hform : bochner = form) :
    z * (source - bochner) + z * (lam * gSq - Lam * wSq) ≤
      z * (ε * gSq + Cε * (1 + uSq)) := by
  rw [hraw, ← hsource, ← hform] at hslice
  exact hslice

private theorem ae_integratedH10Pointwise_of_parent
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
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (ε Cε lam Lam : ℝ) (k : Fin d) (h : ℝ)
    (hχshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω)
    (hparent : ∀ (τ : ℝ), τ ∈ Icc 0 (r₁ - r₀) → 0 ≤ ζ τ →
      ∀ u : H10HilbertGraph hΩ,
        parentFixedSlice r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth ζ η χ ε Cε
          lam Lam k h hχshift τ u)
    (G W : H10HilbertGraph hΩ →L[ℝ] PDE.HilbertVectorLp Ω (2 : ℝ≥0∞))
    (B : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ)
    (hG : G = (gradientCLM hΩ).comp
      (localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset
        (hχshift.mono_left (eta_tsupport_subset_chi η χ))))
    (hW : W = cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h)
    (hB : B = localizedSpatialDifferenceQuotientEnergyTestH10CLM hΩ η k h
      η.tsupport_subset (hχshift.mono_left (eta_tsupport_subset_chi η χ)))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (S R : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hS : S = reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth)
    (hR : R = reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth u)
    (hζnonneg : ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀), 0 ≤ ζ τ) :
    ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀),
      ζ τ * ((S τ) (B (u τ)) - (R τ) (B (u τ))) + ζ τ *
        (lam * ‖G (u τ)‖ ^ 2 - Lam * ‖W (u τ)‖ ^ 2) ≤
        ζ τ * (ε * ‖G (u τ)‖ ^ 2 + Cε * (1 + ‖u τ‖ ^ 2)) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hζnonneg,
    ae_reverseTimeNegativeSource_apply r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth,
    ae_reverseTimeSpatialFormBochnerAction_apply r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth u] with τ hτ hζτ hsource hform
  have hτIcc : τ ∈ Icc 0 (r₁ - r₀) := ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩
  have hraw := reverseTimeNegativeSourceRaw_eq_sourceFunctional_of_mem_Icc
    r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ hτIcc
  subst B
  subst G
  subst W
  subst S
  subst R
  have hslice := hparent τ hτIcc hζτ (u τ)
  dsimp only [parentFixedSlice] at hslice
  exact integratedH10Pointwise_fixedTime_scalar hslice
    (congrArg (fun L => L
      (localizedSpatialDifferenceQuotientEnergyTestH10CLM hΩ η k h
        η.tsupport_subset (hχshift.mono_left (eta_tsupport_subset_chi η χ)) (u τ))) hraw)
    (congrArg (fun L => L
      (localizedSpatialDifferenceQuotientEnergyTestH10CLM hΩ η k h
        η.tsupport_subset (hχshift.mono_left (eta_tsupport_subset_chi η χ)) (u τ)))
      (hsource hτ))
    (hform (localizedSpatialDifferenceQuotientEnergyTestH10CLM hΩ η k h
      η.tsupport_subset (hχshift.mono_left (eta_tsupport_subset_chi η χ)) (u τ)))

/-- An almost-everywhere nonnegative reverse-time test turns the fixed-slice
H10 coercive commutator inequality into its unabsorbed variational integral form. -/
private theorem integratedH10Leaf_proof
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
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (ε Cε lam Lam : ℝ) (k : Fin d) (h : ℝ)
    (hχshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω)
    (hparent : ∀ (τ : ℝ), τ ∈ Icc 0 (r₁ - r₀) → 0 ≤ ζ τ →
      ∀ u : H10HilbertGraph hΩ,
        parentFixedSlice r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth ζ η χ ε Cε
          lam Lam k h hχshift τ u)
    (hζnonneg : ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀), 0 ≤ ζ τ)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u g)
    (hu : IsReverseTimeVariationalEnergySolution
      r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth initial u g hdu) :
    integratedH10Leaf r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth F hFSmooth
      ζ hζunit η χ ε Cε lam Lam k h hχshift hζnonneg initial u g hdu hu := by
  let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := eta_tsupport_subset_chi η χ
  let hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω := hχshift.mono_left hηχ
  let A : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
    localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
  let B : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
    localizedSpatialDifferenceQuotientEnergyTestH10CLM hΩ η k h η.tsupport_subset hηshift
  let G : H10HilbertGraph hΩ →L[ℝ] PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
    (gradientCLM hΩ).comp A
  let W : H10HilbertGraph hΩ →L[ℝ] PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
    cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h
  let S : ReverseTimeL2VStar hΩ (r₁ - r₀) :=
    reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth
  let R : ReverseTimeL2VStar hΩ (r₁ - r₀) :=
    reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth u
  have hQbase : Integrable (fun τ => (S τ) (B (u τ)) - (R τ) (B (u τ)))
      (reverseTimeVolume (r₁ - r₀)) := by
    exact (integrable_reverseTimeDualPairing_timewiseCLM hΩ (r₁ - r₀) B u S).sub
      (integrable_reverseTimeDualPairing_timewiseCLM hΩ (r₁ - r₀) B u R)
  have hQ : Integrable (fun τ => ζ τ * ((S τ) (B (u τ)) - (R τ) (B (u τ))))
      (reverseTimeVolume (r₁ - r₀)) :=
    integrable_weighted ζ hζunit hQbase
  have hGsq : Integrable (fun τ => ‖G (u τ)‖ ^ 2)
      (reverseTimeVolume (r₁ - r₀)) :=
    integrable_norm_sq_timewise_apply hΩ (r₁ - r₀) G u
  have hWsq : Integrable (fun τ => ‖W (u τ)‖ ^ 2)
      (reverseTimeVolume (r₁ - r₀)) :=
    integrable_norm_sq_timewise_apply hΩ (r₁ - r₀) W u
  have hUsq : Integrable (fun τ => ‖u τ‖ ^ 2) (reverseTimeVolume (r₁ - r₀)) := by
    simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) u u
  have hcoerciveBase : Integrable (fun τ =>
      lam * ‖G (u τ)‖ ^ 2 - Lam * ‖W (u τ)‖ ^ 2) (reverseTimeVolume (r₁ - r₀)) :=
    (hGsq.const_mul lam).sub (hWsq.const_mul Lam)
  have hcoercive : Integrable (fun τ => ζ τ *
      (lam * ‖G (u τ)‖ ^ 2 - Lam * ‖W (u τ)‖ ^ 2))
      (reverseTimeVolume (r₁ - r₀)) :=
    integrable_weighted ζ hζunit hcoerciveBase
  letI : IsFiniteMeasure (reverseTimeVolume (r₁ - r₀)) := by
    change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) (r₁ - r₀)))
    infer_instance
  have hOne : Integrable (fun _ : ℝ => (1 : ℝ)) (reverseTimeVolume (r₁ - r₀)) :=
    integrable_const _
  have hYoungBase : Integrable (fun τ =>
      ε * ‖G (u τ)‖ ^ 2 + Cε * (1 + ‖u τ‖ ^ 2))
      (reverseTimeVolume (r₁ - r₀)) :=
    (hGsq.const_mul ε).add ((hOne.add hUsq).const_mul Cε)
  have hYoung : Integrable (fun τ => ζ τ *
      (ε * ‖G (u τ)‖ ^ 2 + Cε * (1 + ‖u τ‖ ^ 2)))
      (reverseTimeVolume (r₁ - r₀)) :=
    integrable_weighted ζ hζunit hYoungBase
  have hpoint := ae_integratedH10Pointwise_of_parent
    r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth F hFSmooth ζ η χ
      ε Cε lam Lam k h hχshift hparent G W B rfl rfl rfl u S R rfl rfl hζnonneg
  have henergy := integral_energy_term_eq_integral_residual
    r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth F hFSmooth initial u g
      hdu hu (inner := inner) η k h hηshift ζ A B rfl rfl
  have hmono := integral_mono_ae (hQ.add hcoercive) hYoung hpoint
  change -(1 / 2 : ℝ) *
      (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * ζ.deriv τ
        ∂reverseTimeVolume (r₁ - r₀)) +
    (∫ τ, ζ τ * (lam * ‖G (u τ)‖ ^ 2 - Lam * ‖W (u τ)‖ ^ 2)
      ∂reverseTimeVolume (r₁ - r₀)) ≤
    ∫ τ, ζ τ * (ε * ‖G (u τ)‖ ^ 2 + Cε * (1 + ‖u τ‖ ^ 2))
      ∂reverseTimeVolume (r₁ - r₀)
  calc
    -(1 / 2 : ℝ) *
        (∫ τ, ‖valueCLM hΩ (A (u τ))‖ ^ 2 * ζ.deriv τ
          ∂reverseTimeVolume (r₁ - r₀)) +
      (∫ τ, ζ τ * (lam * ‖G (u τ)‖ ^ 2 - Lam * ‖W (u τ)‖ ^ 2)
        ∂reverseTimeVolume (r₁ - r₀)) =
        (∫ τ, ζ τ * ((S τ) (B (u τ)) - (R τ) (B (u τ)))
          ∂reverseTimeVolume (r₁ - r₀)) +
        (∫ τ, ζ τ * (lam * ‖G (u τ)‖ ^ 2 - Lam * ‖W (u τ)‖ ^ 2)
          ∂reverseTimeVolume (r₁ - r₀)) := by rw [henergy]
    _ = ∫ τ, ζ τ * ((S τ) (B (u τ)) - (R τ) (B (u τ))) + ζ τ *
        (lam * ‖G (u τ)‖ ^ 2 - Lam * ‖W (u τ)‖ ^ 2)
        ∂reverseTimeVolume (r₁ - r₀) := by
      exact integral_add_of_integrable _ hQ hcoercive
    _ ≤ ∫ τ, ζ τ * (ε * ‖G (u τ)‖ ^ 2 + Cε * (1 + ‖u τ‖ ^ 2))
        ∂reverseTimeVolume (r₁ - r₀) := hmono

private theorem integratedH10OuterOutput_proof
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
    (ζ : ReverseTimeScalarTest (r₁ - r₀)) (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ) :
    integratedH10OuterOutput r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth
      F hFSmooth ζ hζunit η χ := by
  obtain ⟨δ, hδ, hparent⟩ := parentOutput_of_public
    r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth F hFSmooth ζ hζunit η χ
  refine ⟨δ, hδ, ?_⟩
  intro ε hε
  obtain ⟨Cε, hCε, hparent⟩ := hparent ε hε
  refine ⟨Cε, hCε, ?_⟩
  intro lam Lam hLower hUpper k h hh
  obtain ⟨hχshift, hparent⟩ := hparent lam Lam hLower hUpper k h hh
  refine ⟨hχshift, ?_⟩
  intro hζnonneg initial u g hdu hu
  exact integratedH10Leaf_proof
    r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth F hFSmooth ζ hζunit η χ
      ε Cε lam Lam k h hχshift hparent hζnonneg initial u g hdu hu

/-- An almost-everywhere nonnegative reverse-time test turns the fixed-slice
H10 coercive commutator inequality into its unabsorbed variational integral form. -/
theorem exists_smallStep_integral_h10Commutator_add_coerciveTerm_le_nonprincipalYoung
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
    integratedH10CoerciveConsequenceOutput
      r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth
      F hFSmooth ζ hζunit η χ := by
  exact integratedH10OuterOutput_proof
    r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth F hFSmooth
      ζ hζunit η χ

/-- The integrated full H10 coercive inequality has a Young constant uniform
over all coefficient data satisfying the supplied literal majorants. -/
theorem exists_uniform_integral_h10Commutator_add_coerciveTerm_le_nonprincipalYoung_of_majorants
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (ζ : ReverseTimeScalarTest (r₁ - r₀)) (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1)
    (delta : ℝ)
    (hcarrier : spatialCoordinateShiftCarrier (tsupport χ.toFun) delta ⊆ Ω)
    (M : ℝ) (hM : 0 ≤ M) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Cepsilon : ℝ, 0 ≤ Cepsilon ∧
      ∀ (lam Lam : ℝ) (a : CoefficientField d)
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
            (∫ τ, ζ τ * (lam * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
              ∂reverseTimeVolume (r₁ - r₀)) ≤
            (∫ τ, ζ τ *
              (epsilon * ‖Gv τ‖ ^ 2 + Cepsilon * (1 + ‖u τ‖ ^ 2))
              ∂reverseTimeVolume (r₁ - r₀))) := by
  obtain ⟨Cepsilon, hCepsilon, hfixed⟩ :=
    exists_uniform_h10Commutator_add_coerciveTerm_le_nonprincipalYoung_of_majorants
      r₀ r₁ h₀₁ hΩ hΩbounded η χ ζ hζunit delta hcarrier M hM epsilon hepsilon
  refine ⟨Cepsilon, hCepsilon, ?_⟩
  intro lam Lam a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hUpper
    hA hB hBD hq hqD hfD k h hh hζnonneg initial u g hdu hu
  let hχshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω :=
    mapsTo_add_smul_basisVec_of_spatialCoordinateShiftCarrier_subset hcarrier k hh
  change integratedH10Leaf r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth
    F hFSmooth ζ hζunit η χ epsilon Cepsilon lam Lam k h hχshift hζnonneg initial u g hdu hu
  apply integratedH10Leaf_proof
  · intro τ hτ hζτ v
    have hslice := hfixed lam Lam a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hUpper
      hA hB hBD hq hqD hfD k h hh τ hτ hζτ v
    simpa only [parentFixedSlice] using hslice

/-- The integrated full H10 coercive inequality has a Young constant uniform
in the reverse-time scalar test and all data satisfying the supplied literal
majorants. -/
theorem
  exists_uniform_timeTest_integral_h10Commutator_add_coerciveTerm_le_nonprincipalYoung_of_majorants
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (delta : ℝ)
    (hcarrier : spatialCoordinateShiftCarrier (tsupport χ.toFun) delta ⊆ Ω)
    (M : ℝ) (hM : 0 ≤ M) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Cepsilon : ℝ, 0 ≤ Cepsilon ∧
      ∀ (ζ : ReverseTimeScalarTest (r₁ - r₀))
        (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1),
      ∀ (lam Lam : ℝ) (a : CoefficientField d)
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
            (∫ τ, ζ τ * (lam * ‖Gv τ‖ ^ 2 - Lam * ‖Wv τ‖ ^ 2)
              ∂reverseTimeVolume (r₁ - r₀)) ≤
            (∫ τ, ζ τ *
              (epsilon * ‖Gv τ‖ ^ 2 + Cepsilon * (1 + ‖u τ‖ ^ 2))
              ∂reverseTimeVolume (r₁ - r₀))) := by
  obtain ⟨Cepsilon, hCepsilon, hfixed⟩ :=
    exists_uniform_timeTest_h10Commutator_add_coerciveTerm_le_nonprincipalYoung_of_majorants
      r₀ r₁ h₀₁ hΩ hΩbounded η χ delta hcarrier M hM epsilon hepsilon
  refine ⟨Cepsilon, hCepsilon, ?_⟩
  intro zeta hzetaunit lam Lam a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hUpper
    hA hB hBD hq hqD hfD k h hh hζnonneg initial u g hdu hu
  let hχshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω :=
    mapsTo_add_smul_basisVec_of_spatialCoordinateShiftCarrier_subset hcarrier k hh
  change integratedH10Leaf r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth
    F hFSmooth zeta hzetaunit η χ epsilon Cepsilon lam Lam k h hχshift hζnonneg initial u g
      hdu hu
  apply integratedH10Leaf_proof
  · intro τ hτ hζτ v
    have hslice := hfixed zeta hzetaunit lam Lam a b c F haSmooth hbSmooth hcSmooth hFSmooth
      hLower hUpper hA hB hBD hq hqD hfD k h hh τ hτ hζτ v
    simpa only [parentFixedSlice] using hslice

end IsReverseTimeVariationalEnergySolution

end HypoellipticAleksandrov.Parabolic.Dirichlet
