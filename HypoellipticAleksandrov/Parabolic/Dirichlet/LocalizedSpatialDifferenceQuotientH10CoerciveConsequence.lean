module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10CommutatorSplit
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientTranslatedPrincipalCoercivity

/-!
# Fixed-slice H10 coercive commutator consequence
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.Elementwise

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private def rawTranslatedPrincipalValue
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ T : ℝ}
    (r₁ : ℝ) (hΩ : IsOpen Ω) (a : CoefficientField d)
    (ζ : ReverseTimeScalarTest T)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (k : Fin d) (h τ : ℝ)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) (u : H10HilbertGraph hΩ) : ℝ :=
    let A : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
      localizedSpatialDifferenceQuotientH10CLM
        hΩ η k h η.tsupport_subset hηshift
    let Gv : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) := gradientCLM hΩ (A u)
    let G : Fin d → PDE.Vec d → ℝ := fun i y =>
      PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Gv y
    let W : Fin d → PDE.Vec d → ℝ := fun i y =>
      cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
        (valueCLM hΩ u) y
    let E : Fin d → PDE.Vec d → ℝ := fun i y => G i y - W i y
    let H : Fin d → PDE.Vec d → ℝ := fun i y => G i y + W i y
    let α : Fin d → Fin d → TimeVelocity d → ℝ :=
      fun i j z => reverseTimeCoefficient r₁ a z.1 z.2 i j
    ∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
      (ζ τ * χ y * spatialTranslate k h (α i j) (τ, y)) * E j y * H i y ∂volume

private def canonicalTranslatedPrincipalValue
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ T : ℝ}
    (r₁ : ℝ) (hΩ : IsOpen Ω) (a : CoefficientField d)
    (ζ : ReverseTimeScalarTest T)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (k : Fin d) (h τ : ℝ)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) (u : H10HilbertGraph hΩ) : ℝ :=
    let Ev : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
      localizedSpatialDifferenceQuotientPrincipalFieldCLM
        hΩ η k h η.tsupport_subset hηshift u
    let Hv : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
      localizedSpatialDifferenceQuotientCompanionFieldCLM
        hΩ η k h η.tsupport_subset hηshift u
    let α : Fin d → Fin d → TimeVelocity d → ℝ :=
      fun i j z => reverseTimeCoefficient r₁ a z.1 z.2 i j
    ∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
      (ζ τ * χ y * spatialTranslate k h (α i j) (τ, y)) *
        PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j Ev y *
        PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Hv y ∂volume

private theorem integral_eq_of_coord_sub_add
    {d : ℕ} {Ω : Set (PDE.Vec d)} {T : ℝ}
    (ζ : ReverseTimeScalarTest T) (χ : PDE.Vec d → ℝ)
    (k : Fin d) (h τ : ℝ)
    (α : Fin d → Fin d → TimeVelocity d → ℝ)
    (Gv : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞))
    (Wl : Fin d → PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (Ev Hv : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞))
    (hEeq : ∀ j : Fin d, PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j Ev =
      PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j Gv - Wl j)
    (hHeq : ∀ i : Fin d, PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Hv =
      PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Gv + Wl i) :
    (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
      (ζ τ * χ y * spatialTranslate k h (α i j) (τ, y)) *
        (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j Gv y - Wl j y) *
        (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Gv y + Wl i y) ∂volume) =
      ∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
        (ζ τ * χ y * spatialTranslate k h (α i j) (τ, y)) *
          PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j Ev y *
          PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Hv y ∂volume := by
  have hEraw (j : Fin d) : ∀ᵐ y ∂PDE.volumeOn Ω,
      PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j Ev y =
        PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j Gv y - Wl j y := by
    rw [hEeq j]
    filter_upwards [MeasureTheory.Lp.coeFn_sub
      (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j Gv)
      (Wl j)] with y hy
    exact hy
  have hHraw (i : Fin d) : ∀ᵐ y ∂PDE.volumeOn Ω,
      PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Hv y =
        PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Gv y + Wl i y := by
    rw [hHeq i]
    filter_upwards [MeasureTheory.Lp.coeFn_add
      (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Gv)
      (Wl i)] with y hy
    exact hy
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards [hEraw j, hHraw i] with y hE hH
  rw [hE, hH]

private theorem raw_translatedPrincipal_eq_canonical_ev_hv
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ T : ℝ}
    (r₁ : ℝ) (hΩ : IsOpen Ω) (a : CoefficientField d)
    (ζ : ReverseTimeScalarTest T)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (k : Fin d) (h τ : ℝ)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) (u : H10HilbertGraph hΩ) :
    rawTranslatedPrincipalValue r₁ hΩ a ζ η χ k h τ hηshift u =
      canonicalTranslatedPrincipalValue r₁ hΩ a ζ η χ k h τ hηshift u := by
  let A := localizedSpatialDifferenceQuotientH10CLM
    hΩ η k h η.tsupport_subset hηshift
  let Gv : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) := gradientCLM hΩ (A u)
  let Wl : Fin d → PDE.ScalarLp Ω (2 : ℝ≥0∞) := fun i =>
    cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
      (valueCLM hΩ u)
  let Ev : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
    localizedSpatialDifferenceQuotientPrincipalFieldCLM
      hΩ η k h η.tsupport_subset hηshift u
  let Hv : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
    localizedSpatialDifferenceQuotientCompanionFieldCLM
      hΩ η k h η.tsupport_subset hηshift u
  let α : Fin d → Fin d → TimeVelocity d → ℝ :=
    fun i j z => reverseTimeCoefficient r₁ a z.1 z.2 i j
  have hEeq (j : Fin d) :
      PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j Ev =
        PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j Gv - Wl j := by
    calc
      _ = PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
          (gradientCLM hΩ (localizedSpatialDifferenceQuotientH10CLM
            hΩ η k h η.tsupport_subset hηshift u)) -
          cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η j k h
            (valueCLM hΩ u) := by
        dsimp only [Ev]
        exact hilbertVectorLpCoord_localizedSpatialDifferenceQuotientPrincipalFieldCLM
          hΩ η j k h η.tsupport_subset hηshift u
      _ = _ := by
        rw [show Gv = gradientCLM hΩ (localizedSpatialDifferenceQuotientH10CLM
          hΩ η k h η.tsupport_subset hηshift u) by rfl,
          show Wl j = cutoffGradientSpatialDifferenceQuotientL2
            hΩ.measurableSet η j k h (valueCLM hΩ u) by rfl]
  have hHeq (i : Fin d) :
      PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Hv =
        PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Gv + Wl i := by
    calc
      _ = PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
          (gradientCLM hΩ (localizedSpatialDifferenceQuotientH10CLM
            hΩ η k h η.tsupport_subset hηshift u)) +
          cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
            (valueCLM hΩ u) := by
        dsimp only [Hv]
        exact hilbertVectorLpCoord_localizedSpatialDifferenceQuotientCompanionFieldCLM
          hΩ η i k h η.tsupport_subset hηshift u
      _ = _ := by
        rw [show Gv = gradientCLM hΩ (localizedSpatialDifferenceQuotientH10CLM
          hΩ η k h η.tsupport_subset hηshift u) by rfl,
          show Wl i = cutoffGradientSpatialDifferenceQuotientL2
            hΩ.measurableSet η i k h (valueCLM hΩ u) by rfl]
  have hbridge := integral_eq_of_coord_sub_add
    ζ χ k h τ α Gv Wl Ev Hv hEeq hHeq
  simpa only [rawTranslatedPrincipalValue, canonicalTranslatedPrincipalValue,
    A, Gv, Wl, Ev, Hv, α] using hbridge

private theorem scalar_coercive_consequence
    (Q P R z X Y : ℝ) (hsplit : Q = -P + z * R) (hprincipal : z * X ≤ P)
    (hRabs : |R| ≤ Y) (hz : 0 ≤ z) :
    Q + z * X ≤ z * Y := by
  have hRle : R ≤ Y := (le_abs_self R).trans hRabs
  have hzR : z * R ≤ z * Y := mul_le_mul_of_nonneg_left hRle hz
  calc
    Q + z * X = (-P + z * R) + z * X := by rw [hsplit]
    _ = z * R + (z * X - P) := by ring
    _ ≤ z * R + 0 := by
      simpa only [add_comm] using
        add_le_add_left (sub_nonpos.mpr hprincipal) (z * R)
    _ = z * R := by ring
    _ ≤ z * Y := hzR

private theorem translated_principal_raw_lower
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ lam Lam : ℝ) (hΩ : IsOpen Ω) (a : CoefficientField d)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hLower : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hUpper : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → a z.1 z.2 ≤ Lam • (1 : PDE.Mat d))
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (k : Fin d) (h : ℝ)
    (hχshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω)
    (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) (hζnonneg : 0 ≤ ζ τ)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) (u : H10HilbertGraph hΩ) :
    ζ τ * (lam * ‖gradientCLM hΩ
      (localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift u)‖ ^ 2 -
      Lam * ‖cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h u‖ ^ 2) ≤
      rawTranslatedPrincipalValue r₁ hΩ a ζ η χ k h τ hηshift u := by
  have hcanonical :=
    localizedSpatialDifferenceQuotient_translatedPrincipal_lower_of_loewner
      r₀ r₁ lam Lam hΩ a haSmooth hLower hUpper ζ η χ k h hχshift τ hτ hζnonneg u
  let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
    intro y hy
    apply subset_tsupport
    change χ y ≠ 0
    rw [χ.eq_one_on_inner y hy]
    exact one_ne_zero
  have hbridge := raw_translatedPrincipal_eq_canonical_ev_hv
    r₁ hΩ a ζ η χ k h τ hηshift u
  change _ ≤ canonicalTranslatedPrincipalValue r₁ hΩ a ζ η χ k h τ hηshift u at hcanonical
  exact hcanonical.trans_eq hbridge.symm

private def compactSplitOutput
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
  ∃ δ : ℝ, 0 < δ ∧ ∀ (k : Fin d) (h : ℝ), |h| ≤ δ →
    ∃ hχshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω, ∀ (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
      (u : H10HilbertGraph hΩ),
      let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
        intro y hy; apply subset_tsupport; change χ y ≠ 0
        rw [χ.eq_one_on_inner y hy]; exact one_ne_zero
      let hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
          (tsupport η.toFun) Ω := hχshift.mono_left hηχ
      let A := localizedSpatialDifferenceQuotientH10CLM
        hΩ η k h η.tsupport_subset hηshift
      let B := localizedSpatialDifferenceQuotientEnergyTestH10CLM
        hΩ η k h η.tsupport_subset hηshift
      ζ τ * (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hF τ (B u) -
        reverseTimeSpatialForm hΩ r₁ τ a b c u (B u)) =
        -rawTranslatedPrincipalValue r₁ hΩ a ζ η χ k h τ hηshift u + ζ τ *
          localizedSpatialDifferenceQuotientH10NonprincipalRemainder
            r₁ hΩ a b c F η χ k h τ hηshift u

private theorem compactSplitOutput_of_accepted
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
    compactSplitOutput r₀ r₁ h₀₁ hΩ hΩbounded a b c ha hb hc F hF ζ hζ η χ := by
  obtain ⟨δ, hδ, hrest⟩ :=
    exists_smallStep_h10Commutator_eq_neg_translatedPrincipal_add_nonprincipalRemainder
      r₀ r₁ h₀₁ hΩ hΩbounded a b c ha hb hc F hF ζ hζ η χ
  refine ⟨δ, hδ, ?_⟩
  intro k h hh
  obtain ⟨hχshift, hfixed⟩ := hrest k h hh
  refine ⟨hχshift, ?_⟩
  intro τ hτ u
  change _ = -rawTranslatedPrincipalValue r₁ hΩ a ζ η χ k h τ _ u + _
  simpa only [rawTranslatedPrincipalValue] using hfixed τ hτ u

private def compactRemainderOutput
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (hΩ : IsOpen Ω) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (_ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (_hb : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (_hc : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (_hF : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, 0 ≤ Cε ∧
    ∀ (k : Fin d) (h : ℝ), |h| ≤ δ →
      ∀ hχshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
        (tsupport χ.toFun) Ω, ∀ (τ : ℝ), τ ∈ Set.Icc 0 (r₁ - r₀) →
        ∀ u : H10HilbertGraph hΩ,
        let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
          intro y hy; apply subset_tsupport; change χ y ≠ 0
          rw [χ.eq_one_on_inner y hy]; exact one_ne_zero
        let hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
            (tsupport η.toFun) Ω := hχshift.mono_left hηχ
        let A := localizedSpatialDifferenceQuotientH10CLM
          hΩ η k h η.tsupport_subset hηshift
        |localizedSpatialDifferenceQuotientH10NonprincipalRemainder
            r₁ hΩ a b c F η χ k h τ hηshift u| ≤
          ε * ‖gradientCLM hΩ (A u)‖ ^ 2 + Cε * (1 + ‖u‖ ^ 2)

private theorem compactRemainderOutput_of_accepted
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (hΩ : IsOpen Ω) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hb : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hc : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hF : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ) :
    compactRemainderOutput r₀ r₁ hΩ a b c F ha hb hc hF η χ := by
  obtain ⟨δ, hδ, hrest⟩ :=
    exists_smallStep_localizedSpatialDifferenceQuotientH10_nonprincipalRemainder_bound
      r₀ r₁ hΩ a b c F ha hb hc hF η χ
  refine ⟨δ, hδ, ?_⟩
  intro ε hε
  obtain ⟨Cε, hCε, hfixed⟩ := hrest ε hε
  refine ⟨Cε, hCε, ?_⟩
  intro k h hh hχshift τ hτ u
  simpa only using hfixed k h hh hχshift τ hτ u

private def coerciveFixedSlice
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (ε Cε lam Lam : ℝ) (k : Fin d) (h : ℝ)
    (hχshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω) (τ : ℝ) (u : H10HilbertGraph hΩ) : Prop :=
  let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
    intro y hy; apply subset_tsupport; change χ y ≠ 0
    rw [χ.eq_one_on_inner y hy]; exact one_ne_zero
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

private theorem coerciveFixedSlice_of_adapterFacts
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hF : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (ε Cε lam Lam : ℝ)
    (hLower : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hUpper : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → a z.1 z.2 ≤ Lam • (1 : PDE.Mat d))
    (k : Fin d) (h : ℝ)
    (hχshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω) (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
    (hζnonneg : 0 ≤ ζ τ)
    (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) (u : H10HilbertGraph hΩ)
    (hsplit : ζ τ *
      (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hF τ
        (localizedSpatialDifferenceQuotientEnergyTestH10CLM
          hΩ η k h η.tsupport_subset hηshift u) -
        reverseTimeSpatialForm hΩ r₁ τ a b c u
          (localizedSpatialDifferenceQuotientEnergyTestH10CLM
            hΩ η k h η.tsupport_subset hηshift u)) =
        -rawTranslatedPrincipalValue r₁ hΩ a ζ η χ k h τ hηshift u + ζ τ *
          localizedSpatialDifferenceQuotientH10NonprincipalRemainder
            r₁ hΩ a b c F η χ k h τ hηshift u)
    (hrem : |localizedSpatialDifferenceQuotientH10NonprincipalRemainder
      r₁ hΩ a b c F η χ k h τ hηshift u| ≤
        ε * ‖gradientCLM hΩ
          (localizedSpatialDifferenceQuotientH10CLM
            hΩ η k h η.tsupport_subset hηshift u)‖ ^ 2 + Cε * (1 + ‖u‖ ^ 2)) :
    coerciveFixedSlice r₀ r₁ h₀₁ hΩ hΩbounded a b c F hF ζ η χ ε Cε lam Lam
      k h hχshift τ u := by
  let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
    intro y hy; apply subset_tsupport; change χ y ≠ 0
    rw [χ.eq_one_on_inner y hy]; exact one_ne_zero
  let hηshift' : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω := hχshift.mono_left hηχ
  have hshift : hηshift = hηshift' := Subsingleton.elim _ _
  subst hηshift
  let A : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
    localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift'
  let B : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
    localizedSpatialDifferenceQuotientEnergyTestH10CLM hΩ η k h η.tsupport_subset hηshift'
  let Gv : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) := gradientCLM hΩ (A u)
  let Wv : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
    cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h u
  let Q : ℝ := ζ τ *
    (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hF τ (B u) -
      reverseTimeSpatialForm hΩ r₁ τ a b c u (B u))
  let z : ℝ := ζ τ
  let X : ℝ := lam * ‖Gv‖ ^ 2 - Lam * ‖Wv‖ ^ 2
  let Y : ℝ := ε * ‖Gv‖ ^ 2 + Cε * (1 + ‖u‖ ^ 2)
  let R : ℝ := localizedSpatialDifferenceQuotientH10NonprincipalRemainder
    r₁ hΩ a b c F η χ k h τ hηshift' u
  let Praw : ℝ := rawTranslatedPrincipalValue r₁ hΩ a ζ η χ k h τ hηshift' u
  change Q = -Praw + z * R at hsplit
  have hprincipalRaw := translated_principal_raw_lower
    r₀ r₁ lam Lam hΩ a ha hLower hUpper ζ η χ k h hχshift τ hτ hζnonneg hηshift' u
  change z * X ≤ Praw at hprincipalRaw
  change |R| ≤ Y at hrem
  change coerciveFixedSlice r₀ r₁ h₀₁ hΩ hΩbounded a b c F hF ζ η χ ε Cε lam Lam
    k h hχshift τ u
  dsimp only [coerciveFixedSlice]
  exact scalar_coercive_consequence Q Praw R z X Y hsplit hprincipalRaw hrem hζnonneg

private def coerciveConsequenceOutput
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
          coerciveFixedSlice r₀ r₁ h₀₁ hΩ hΩbounded a b c F hF ζ η χ ε Cε lam Lam
            k h hχshift τ u

private theorem coerciveConsequenceOutput_of_adapters
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
    coerciveConsequenceOutput r₀ r₁ h₀₁ hΩ hΩbounded a b c ha hb hc F hF ζ hζ η χ := by
  obtain ⟨δsplit, hδsplit, hsplit⟩ := compactSplitOutput_of_accepted
    r₀ r₁ h₀₁ hΩ hΩbounded a b c ha hb hc F hF ζ hζ η χ
  obtain ⟨δrem, hδrem, hrem⟩ := compactRemainderOutput_of_accepted
    r₀ r₁ hΩ a b c F ha hb hc hF η χ
  refine ⟨min δsplit δrem, lt_min hδsplit hδrem, ?_⟩
  intro ε hε
  obtain ⟨Cε, hCε, hremStep⟩ := hrem ε hε
  refine ⟨Cε, hCε, ?_⟩
  intro lam Lam hLower hUpper k h hh
  have hhsplit : |h| ≤ δsplit := hh.trans (min_le_left _ _)
  have hhrem : |h| ≤ δrem := hh.trans (min_le_right _ _)
  obtain ⟨hχshift, hsplitStep⟩ := hsplit k h hhsplit
  refine ⟨hχshift, ?_⟩
  intro τ hτ hζnonneg u
  let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
    intro y hy; apply subset_tsupport; change χ y ≠ 0
    rw [χ.eq_one_on_inner y hy]; exact one_ne_zero
  let hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω := hχshift.mono_left hηχ
  have hsplitEq := hsplitStep τ hτ u
  change ζ τ *
    (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hF τ
      (localizedSpatialDifferenceQuotientEnergyTestH10CLM
        hΩ η k h η.tsupport_subset hηshift u) -
      reverseTimeSpatialForm hΩ r₁ τ a b c u
        (localizedSpatialDifferenceQuotientEnergyTestH10CLM
          hΩ η k h η.tsupport_subset hηshift u)) =
      -rawTranslatedPrincipalValue r₁ hΩ a ζ η χ k h τ hηshift u + ζ τ *
        localizedSpatialDifferenceQuotientH10NonprincipalRemainder
          r₁ hΩ a b c F η χ k h τ hηshift u at hsplitEq
  have hremBound := hremStep k h hhrem hχshift τ hτ u
  change |localizedSpatialDifferenceQuotientH10NonprincipalRemainder
    r₁ hΩ a b c F η χ k h τ hηshift u| ≤
      ε * ‖gradientCLM hΩ
        (localizedSpatialDifferenceQuotientH10CLM
          hΩ η k h η.tsupport_subset hηshift u)‖ ^ 2 + Cε * (1 + ‖u‖ ^ 2) at hremBound
  exact coerciveFixedSlice_of_adapterFacts r₀ r₁ h₀₁ hΩ hΩbounded a b c F ha hF ζ η χ
    ε Cε lam Lam hLower hUpper k h hχshift τ hτ hζnonneg hηshift u hsplitEq hremBound

private theorem coerciveConsequenceOutput_of_components
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
    coerciveConsequenceOutput r₀ r₁ h₀₁ hΩ hΩbounded a b c ha hb hc F hF ζ hζ η χ := by
  exact coerciveConsequenceOutput_of_adapters
    r₀ r₁ h₀₁ hΩ hΩbounded a b c ha hb hc F hF ζ hζ η χ

/-- For all sufficiently small signed steps, the exact fixed-slice H10
commutator plus its Loewner coercive term is bounded by the weighted
nonprincipal Young remainder. -/
theorem exists_smallStep_h10Commutator_add_coerciveTerm_le_nonprincipalYoung
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
              ∀ (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
                (hζnonneg : 0 ≤ ζ τ) (u : H10HilbertGraph hΩ),
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
                let B : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
                  localizedSpatialDifferenceQuotientEnergyTestH10CLM
                    hΩ η k h η.tsupport_subset hηshift
                let Gv : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
                  gradientCLM hΩ (A u)
                let Wv : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
                  cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h u
                let Q : ℝ := ζ τ *
                  (reverseTimeNegativeSourceRaw
                      r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (B u) -
                    reverseTimeSpatialForm hΩ r₁ τ a b c u (B u))
                Q + ζ τ * (lam * ‖Gv‖ ^ 2 - Lam * ‖Wv‖ ^ 2) ≤
                  ζ τ * (ε * ‖Gv‖ ^ 2 + Cε * (1 + ‖u‖ ^ 2)) := by
  change coerciveConsequenceOutput r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth
    hcSmooth F hFSmooth ζ hζunit η χ
  exact coerciveConsequenceOutput_of_components
    r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth F hFSmooth
      ζ hζunit η χ

private theorem halfCoerciveTerm_le_of_coerciveTerm
    (Q ζτ lam Lam G W C U : ℝ)
    (h : Q + ζτ * (lam * G - Lam * W) ≤ ζτ * ((lam / 2) * G + C * U)) :
    Q + ζτ * ((lam / 2) * G - Lam * W) ≤ ζτ * (C * U) := by
  calc
    Q + ζτ * ((lam / 2) * G - Lam * W) =
        (Q + ζτ * (lam * G - Lam * W)) - ζτ * ((lam / 2) * G) := by ring
    _ ≤ ζτ * ((lam / 2) * G + C * U) - ζτ * ((lam / 2) * G) :=
      sub_le_sub_right h _
    _ = ζτ * (C * U) := by ring

private def halfCoerciveFixedSlice
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (C_lam lam Lam : ℝ) (k : Fin d) (h : ℝ)
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
  Q + ζ τ * ((lam / 2) * ‖Gv‖ ^ 2 - Lam * ‖Wv‖ ^ 2) ≤
    ζ τ * (C_lam * (1 + ‖u‖ ^ 2))

private theorem halfCoerciveFixedSlice_of_coerciveFixedSlice
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (C_lam lam Lam : ℝ) (k : Fin d) (h : ℝ)
    (hχshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω) (τ : ℝ) (u : H10HilbertGraph hΩ)
    (hcoercive : coerciveFixedSlice r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth ζ η χ
      (lam / 2) C_lam lam Lam k h hχshift τ u) :
    halfCoerciveFixedSlice r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth ζ η χ
      C_lam lam Lam k h hχshift τ u := by
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
  change Q + ζ τ * (lam * ‖Gv‖ ^ 2 - Lam * ‖Wv‖ ^ 2) ≤
    ζ τ * ((lam / 2) * ‖Gv‖ ^ 2 + C_lam * (1 + ‖u‖ ^ 2)) at hcoercive
  change Q + ζ τ * ((lam / 2) * ‖Gv‖ ^ 2 - Lam * ‖Wv‖ ^ 2) ≤
    ζ τ * (C_lam * (1 + ‖u‖ ^ 2))
  exact halfCoerciveTerm_le_of_coerciveTerm Q (ζ τ) lam Lam (‖Gv‖ ^ 2)
    (‖Wv‖ ^ 2) C_lam (1 + ‖u‖ ^ 2) hcoercive

private def halfCoerciveConsequenceOutput
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
  ∃ δ : ℝ, 0 < δ ∧ ∀ lam : ℝ, 0 < lam → ∃ C_lam : ℝ, 0 ≤ C_lam ∧
    ∀ (Lam : ℝ)
      (_hLower : ∀ z : TimeVelocity d,
        z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
      (_hUpper : ∀ z : TimeVelocity d,
        z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → a z.1 z.2 ≤ Lam • (1 : PDE.Mat d)),
      ∀ (k : Fin d) (h : ℝ), |h| ≤ δ →
        ∃ hχshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k)
          (tsupport χ.toFun) Ω, ∀ (τ : ℝ) (_hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
          (_hζnonneg : 0 ≤ ζ τ) (u : H10HilbertGraph hΩ),
          halfCoerciveFixedSlice r₀ r₁ h₀₁ hΩ hΩbounded a b c F hF ζ η χ
            C_lam lam Lam k h hχshift τ u

private theorem halfCoerciveConsequenceOutput_of_components
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
    halfCoerciveConsequenceOutput r₀ r₁ h₀₁ hΩ hΩbounded a b c ha hb hc F hF ζ hζ η χ := by
  obtain ⟨δ, hδ, hcoercive⟩ := coerciveConsequenceOutput_of_components
    r₀ r₁ h₀₁ hΩ hΩbounded a b c ha hb hc F hF ζ hζ η χ
  refine ⟨δ, hδ, ?_⟩
  intro lam hlam
  obtain ⟨C_lam, hC_lam, hcoercive⟩ := hcoercive (lam / 2) (half_pos hlam)
  refine ⟨C_lam, hC_lam, ?_⟩
  intro Lam hLower hUpper k h hh
  obtain ⟨hχshift, hcoercive⟩ := hcoercive lam Lam hLower hUpper k h hh
  refine ⟨hχshift, ?_⟩
  intro τ hτ hζnonneg u
  exact halfCoerciveFixedSlice_of_coerciveFixedSlice
    r₀ r₁ h₀₁ hΩ hΩbounded a b c F hF ζ η χ C_lam lam Lam k h hχshift τ u
    (hcoercive τ hτ hζnonneg u)

/-- For a positive lower ellipticity bound and all sufficiently small signed
steps, half of the fixed-slice H10 coercive term is absorbed into the
nonprincipal Young remainder. -/
theorem exists_smallStep_h10Commutator_add_halfCoerciveTerm_le_nonprincipalYoung
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
              ∀ (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
                (hζnonneg : 0 ≤ ζ τ) (u : H10HilbertGraph hΩ),
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
                let B : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
                  localizedSpatialDifferenceQuotientEnergyTestH10CLM
                    hΩ η k h η.tsupport_subset hηshift
                let Gv : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
                  gradientCLM hΩ (A u)
                let Wv : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
                  cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h u
                let Q : ℝ := ζ τ *
                  (reverseTimeNegativeSourceRaw
                      r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (B u) -
                    reverseTimeSpatialForm hΩ r₁ τ a b c u (B u))
                Q + ζ τ * ((lam / 2) * ‖Gv‖ ^ 2 - Lam * ‖Wv‖ ^ 2) ≤
                  ζ τ * (C_lam * (1 + ‖u‖ ^ 2)) := by
  change halfCoerciveConsequenceOutput r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth
    hbSmooth hcSmooth F hFSmooth ζ hζunit η χ
  exact halfCoerciveConsequenceOutput_of_components
    r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth F hFSmooth
      ζ hζunit η χ

/-- The full fixed-slice coercive term is bounded by the uniform nonprincipal
Young remainder under the supplied collar and majorants. -/
theorem exists_uniform_h10Commutator_add_coerciveTerm_le_nonprincipalYoung_of_majorants
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (ζ : ReverseTimeScalarTest (r₁ - r₀)) (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1)
    (δ : ℝ)
    (hcarrier : spatialCoordinateShiftCarrier (tsupport χ.toFun) δ ⊆ Ω)
    (M : ℝ) (hM : 0 ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ Cε : ℝ, 0 ≤ Cε ∧
      ∀ (lam Lam : ℝ) (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
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
        ∀ (k : Fin d) (h : ℝ) (hh : |h| ≤ δ) (τ : ℝ)
          (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) (hζnonneg : 0 ≤ ζ τ)
          (u : H10HilbertGraph hΩ),
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
          let B : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
            localizedSpatialDifferenceQuotientEnergyTestH10CLM
              hΩ η k h η.tsupport_subset hηshift
          let Gv : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) := gradientCLM hΩ (A u)
          let Wv : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
            cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h u
          let Q : ℝ := ζ τ *
            (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (B u) -
              reverseTimeSpatialForm hΩ r₁ τ a b c u (B u))
          Q + ζ τ * (lam * ‖Gv‖ ^ 2 - Lam * ‖Wv‖ ^ 2) ≤
            ζ τ * (ε * ‖Gv‖ ^ 2 + Cε * (1 + ‖u‖ ^ 2)) := by
  obtain ⟨Cε, hCε, hrem⟩ :=
    exists_uniform_nonprincipalRemainder_bound_of_majorants
      r₀ r₁ hΩ η χ δ M hM hcarrier ε hε
  refine ⟨Cε, hCε, ?_⟩
  intro lam Lam a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hUpper
    hA hB hBD hq hqD hfD k h hh τ hτ hζnonneg u
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
  let hηshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω :=
    hχshift.mono_left hηχ
  have hsplit :=
    h10Commutator_eq_neg_translatedPrincipal_add_nonprincipalRemainder_of_majorants
      r₀ r₁ h₀₁ hΩ hΩbounded η χ ζ hζunit δ hcarrier M hM a b c F haSmooth
        hbSmooth hcSmooth hFSmooth hA hB hBD hq hqD hfD k h hh τ hτ u
  have hsplitRaw : ζ τ *
      (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ
        (localizedSpatialDifferenceQuotientEnergyTestH10CLM
          hΩ η k h η.tsupport_subset hηshift u) -
        reverseTimeSpatialForm hΩ r₁ τ a b c u
          (localizedSpatialDifferenceQuotientEnergyTestH10CLM
            hΩ η k h η.tsupport_subset hηshift u)) =
        -rawTranslatedPrincipalValue r₁ hΩ a ζ η χ k h τ hηshift u + ζ τ *
          localizedSpatialDifferenceQuotientH10NonprincipalRemainder
            r₁ hΩ a b c F η χ k h τ hηshift u := by
    simpa only [rawTranslatedPrincipalValue] using hsplit
  have hremBound := hrem a b c F haSmooth hbSmooth hcSmooth hFSmooth hA hB hBD hq hqD hfD
    k h hh τ hτ u
  change |localizedSpatialDifferenceQuotientH10NonprincipalRemainder
    r₁ hΩ a b c F η χ k h τ hηshift u| ≤
      ε * ‖gradientCLM hΩ
        (localizedSpatialDifferenceQuotientH10CLM
          hΩ η k h η.tsupport_subset hηshift u)‖ ^ 2 + Cε * (1 + ‖u‖ ^ 2) at hremBound
  change coerciveFixedSlice r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth ζ η χ ε Cε lam Lam
    k h hχshift τ u
  exact coerciveFixedSlice_of_adapterFacts
    r₀ r₁ h₀₁ hΩ hΩbounded a b c F haSmooth hFSmooth ζ η χ ε Cε lam Lam hLower hUpper
      k h hχshift τ hτ hζnonneg hηshift u hsplitRaw hremBound

/-- The full fixed-slice coercive term is bounded by a nonprincipal Young
remainder, with its constant uniform in the reverse-time scalar test. -/
theorem exists_uniform_timeTest_h10Commutator_add_coerciveTerm_le_nonprincipalYoung_of_majorants
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (δ : ℝ)
    (hcarrier : spatialCoordinateShiftCarrier (tsupport χ.toFun) δ ⊆ Ω)
    (M : ℝ) (hM : 0 ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ Cε : ℝ, 0 ≤ Cε ∧
      ∀ (ζ : ReverseTimeScalarTest (r₁ - r₀))
        (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1),
      ∀ (lam Lam : ℝ) (a : CoefficientField d)
        (b : ℝ → PDE.Vec d → PDE.Vec d)
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
            spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
            spatialMatrixFDerivFrobeniusNorm
              (fun w : TimeVelocity d =>
                reverseTimeCoefficient r₁ a w.1 w.2) z ≤ M)
          (hB : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
            PDE.vecEuclideanNorm
              (reverseTimeDivergenceDrift r₁ a b z.1 z.2) ≤ M)
          (hBD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
            spatialVectorFDerivFrobeniusNorm
              (fun w : TimeVelocity d =>
                reverseTimeDivergenceDrift r₁ a b w.1 w.2) z ≤ M)
          (hq : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
            |-(reverseTimeScalarCoefficient r₁ c z.1 z.2)| ≤ M)
          (hqD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
            spatialScalarFDerivEuclideanNorm
              (fun w : TimeVelocity d =>
                -(reverseTimeScalarCoefficient r₁ c w.1 w.2)) z ≤ M)
          (hfD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
            spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
            spatialScalarFDerivEuclideanNorm
              (fun w : TimeVelocity d =>
                -(reverseTimeScalarCoefficient r₁ F w.1 w.2)) z ≤ M),
        ∀ (k : Fin d) (h : ℝ) (hh : |h| ≤ δ) (τ : ℝ)
          (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
          (hζnonneg : 0 ≤ ζ τ) (u : H10HilbertGraph hΩ),
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
          let B : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
            localizedSpatialDifferenceQuotientEnergyTestH10CLM
              hΩ η k h η.tsupport_subset hηshift
          let Gv : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
            gradientCLM hΩ (A u)
          let Wv : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
            cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h u
          let Q : ℝ := ζ τ *
            (reverseTimeNegativeSourceRaw
                r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (B u) -
              reverseTimeSpatialForm hΩ r₁ τ a b c u (B u))
          Q + ζ τ * (lam * ‖Gv‖ ^ 2 - Lam * ‖Wv‖ ^ 2) ≤
            ζ τ * (ε * ‖Gv‖ ^ 2 + Cε * (1 + ‖u‖ ^ 2)) := by
  obtain ⟨Cε, hCε, hrem⟩ :=
    exists_uniform_nonprincipalRemainder_bound_of_majorants
      r₀ r₁ hΩ η χ δ M hM hcarrier ε hε
  refine ⟨Cε, hCε, ?_⟩
  intro ζ hζunit lam Lam a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hUpper
    hA hB hBD hq hqD hfD k h hh τ hτ hζnonneg u
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
  let hηshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω :=
    hχshift.mono_left hηχ
  have hsplit :=
    h10Commutator_eq_neg_translatedPrincipal_add_nonprincipalRemainder_of_majorants
      r₀ r₁ h₀₁ hΩ hΩbounded η χ ζ hζunit δ hcarrier M hM a b c F haSmooth
        hbSmooth hcSmooth hFSmooth hA hB hBD hq hqD hfD k h hh τ hτ u
  have hsplitRaw : ζ τ *
      (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ
        (localizedSpatialDifferenceQuotientEnergyTestH10CLM
          hΩ η k h η.tsupport_subset hηshift u) -
        reverseTimeSpatialForm hΩ r₁ τ a b c u
          (localizedSpatialDifferenceQuotientEnergyTestH10CLM
            hΩ η k h η.tsupport_subset hηshift u)) =
        -rawTranslatedPrincipalValue r₁ hΩ a ζ η χ k h τ hηshift u + ζ τ *
          localizedSpatialDifferenceQuotientH10NonprincipalRemainder
            r₁ hΩ a b c F η χ k h τ hηshift u := by
    simpa only [rawTranslatedPrincipalValue] using hsplit
  have hremBound :=
    hrem a b c F haSmooth hbSmooth hcSmooth hFSmooth hA hB hBD hq hqD hfD
      k h hh τ hτ u
  change |localizedSpatialDifferenceQuotientH10NonprincipalRemainder
    r₁ hΩ a b c F η χ k h τ hηshift u| ≤
      ε * ‖gradientCLM hΩ
        (localizedSpatialDifferenceQuotientH10CLM
          hΩ η k h η.tsupport_subset hηshift u)‖ ^ 2 + Cε * (1 + ‖u‖ ^ 2) at hremBound
  change coerciveFixedSlice r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth ζ η χ ε Cε lam Lam
    k h hχshift τ u
  exact coerciveFixedSlice_of_adapterFacts
    r₀ r₁ h₀₁ hΩ hΩbounded a b c F haSmooth hFSmooth ζ η χ ε Cε lam Lam hLower hUpper
      k h hχshift τ hτ hζnonneg hηshift u hsplitRaw hremBound

end HypoellipticAleksandrov.Parabolic.Dirichlet
