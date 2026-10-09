module

public import HypoellipticAleksandrov.LinearAlgebra.LoewnerPolarization
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientPrincipalField
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialCoefficientCutoffFields

/-!
# Translated principal coercivity for localized spatial difference quotients

This module proves the fixed-slice lower bound for the literal translated
principal commutator term.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped BigOperators ENNReal MatrixOrder Matrix.Norms.Elementwise

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private theorem vecDot_add_mulVec_sub_expand {d : ℕ} (A : PDE.Mat d)
    (G W : PDE.Vec d) :
    PDE.vecDot (G + W) (Matrix.mulVec A (G - W)) =
      ∑ i : Fin d, ∑ j : Fin d, A i j * (G j - W j) * (G i + W i) := by
  unfold PDE.vecDot Matrix.mulVec
  simp only [dotProduct, Pi.add_apply, Pi.sub_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem weighted_vecDot_add_mulVec_sub_expand {d : ℕ} (c χ : ℝ)
    (A : PDE.Mat d) (G W E H : PDE.Vec d)
    (hE : E = G - W) (hH : H = G + W)
    (hχH : ∀ i : Fin d, χ * H i = H i) :
    c * PDE.vecDot (G + W) (Matrix.mulVec A (G - W)) =
      ∑ i : Fin d, ∑ j : Fin d, (c * χ * A i j) * E j * H i := by
  subst E
  subst H
  rw [vecDot_add_mulVec_sub_expand]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  calc
    c * (A i j * (G j - W j) * (G i + W i)) =
        (c * A i j * (G j - W j)) * (G i + W i) := by ring
    _ = (c * A i j * (G j - W j)) * (χ * (G i + W i)) := by
      have hχHi : χ * (G i + W i) = G i + W i := by
        simpa only [Pi.add_apply] using hχH i
      rw [hχHi]
    _ = (c * χ * A i j) * (G j - W j) * (G i + W i) := by ring

private theorem vecNormSq_zero {d : ℕ} : PDE.vecNormSq (0 : PDE.Vec d) = 0 := by
  unfold PDE.vecNormSq PDE.vecDot
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]

private theorem hilbertVec_vecNormSq_eq_norm_sq {d : ℕ} (v : PDE.HilbertVec d) :
    PDE.vecNormSq v.toVec = ‖v‖ ^ 2 := by
  rw [PDE.HilbertVec.norm_eq_vecEuclideanNorm, PDE.vecEuclideanNorm_sq]

private theorem integral_coercivity_of_ae {d : ℕ} {Ω : Set (PDE.Vec d)}
    (c lam Lam : ℝ) (G W : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞))
    (F : Fin d → Fin d → PDE.Vec d → ℝ)
    (hterm : ∀ i j : Fin d, Integrable (F i j) (PDE.volumeOn Ω))
    (hpoint : ∀ᵐ y ∂PDE.volumeOn Ω,
      c * (lam * ‖G y‖ ^ 2 - Lam * ‖W y‖ ^ 2) ≤ ∑ i : Fin d, ∑ j : Fin d, F i j y) :
    c * (lam * ‖G‖ ^ 2 - Lam * ‖W‖ ^ 2) ≤
      ∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω, F i j y ∂volume := by
  have hsum : Integrable (fun y : PDE.Vec d => ∑ i : Fin d, ∑ j : Fin d, F i j y)
      (PDE.volumeOn Ω) := by
    apply integrable_finset_sum
    intro i _
    apply integrable_finset_sum
    intro j _
    exact hterm i j
  have hGint : Integrable (fun y : PDE.Vec d => ‖G y‖ ^ 2) (PDE.volumeOn Ω) := by
    simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) G G
  have hWint : Integrable (fun y : PDE.Vec d => ‖W y‖ ^ 2) (PDE.volumeOn Ω) := by
    simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) W W
  have hleftint : Integrable (fun y : PDE.Vec d =>
      c * (lam * ‖G y‖ ^ 2 - Lam * ‖W y‖ ^ 2)) (PDE.volumeOn Ω) :=
    ((hGint.const_mul lam).sub (hWint.const_mul Lam)).const_mul c
  have hmono := integral_mono_ae hleftint hsum hpoint
  have hGenergy : (∫ y, ‖G y‖ ^ 2 ∂PDE.volumeOn Ω) = ‖G‖ ^ 2 :=
    PDE.integral_norm_sq_eq_sq_norm_of_ae_eq_hilbert G (fun y => ‖G y‖)
      (Filter.Eventually.of_forall fun _ => rfl)
  have hWenergy : (∫ y, ‖W y‖ ^ 2 ∂PDE.volumeOn Ω) = ‖W‖ ^ 2 :=
    PDE.integral_norm_sq_eq_sq_norm_of_ae_eq_hilbert W (fun y => ‖W y‖)
      (Filter.Eventually.of_forall fun _ => rfl)
  have hleftEq : (∫ y, c * (lam * ‖G y‖ ^ 2 - Lam * ‖W y‖ ^ 2)
      ∂PDE.volumeOn Ω) = c * (lam * ‖G‖ ^ 2 - Lam * ‖W‖ ^ 2) := by
    rw [integral_const_mul, integral_sub (hGint.const_mul lam) (hWint.const_mul Lam),
      integral_const_mul, integral_const_mul, hGenergy, hWenergy]
  rw [← hleftEq]
  calc
    (∫ y, c * (lam * ‖G y‖ ^ 2 - Lam * ‖W y‖ ^ 2) ∂PDE.volumeOn Ω) ≤
        ∫ y, ∑ i : Fin d, ∑ j : Fin d, F i j y ∂PDE.volumeOn Ω := hmono
    _ = ∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω, F i j y ∂volume := by
      calc
        (∫ y, ∑ i : Fin d, ∑ j : Fin d, F i j y ∂PDE.volumeOn Ω) =
            ∑ i : Fin d, ∫ y, ∑ j : Fin d, F i j y ∂PDE.volumeOn Ω := by
          exact integral_finset_sum Finset.univ (fun i _ => by
            apply integrable_finset_sum
            intro j _
            exact hterm i j)
        _ = ∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω, F i j y ∂volume := by
          apply Finset.sum_congr rfl
          intro i _
          exact integral_finset_sum Finset.univ (fun j _ => hterm i j)

/-- The one-cutoff translated principal term controls the sharp localized
difference-quotient gradient-minus-commutator norm expression. -/
theorem localizedSpatialDifferenceQuotient_translatedPrincipal_lower_of_loewner
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ lam Lam : ℝ) (hΩ : IsOpen Ω)
    (a : CoefficientField d)
    (haSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hLower : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
        lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hUpper : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
        a z.1 z.2 ≤ Lam • (1 : PDE.Mat d))
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (k : Fin d) (h : ℝ)
    (hχshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω)
    (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
    (hζnonneg : 0 ≤ ζ τ)
    (u : H10HilbertGraph hΩ) :
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
    let Gv : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
      gradientCLM hΩ
        (localizedSpatialDifferenceQuotientH10CLM
          hΩ η k h η.tsupport_subset hηshift u)
    let Wv : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
      cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h u
    let Ev : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
      localizedSpatialDifferenceQuotientPrincipalFieldCLM
        hΩ η k h η.tsupport_subset hηshift u
    let Hv : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
      localizedSpatialDifferenceQuotientCompanionFieldCLM
        hΩ η k h η.tsupport_subset hηshift u
    let α : Fin d → Fin d → TimeVelocity d → ℝ :=
      fun i j z => reverseTimeCoefficient r₁ a z.1 z.2 i j
    ζ τ * (lam * ‖Gv‖ ^ 2 - Lam * ‖Wv‖ ^ 2) ≤
      ∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
        (ζ τ * χ y * spatialTranslate k h (α i j) (τ, y)) *
            PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j Ev y *
            PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Hv y ∂volume := by
  dsimp only
  let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
    intro y hy
    apply subset_tsupport
    change χ y ≠ 0
    rw [χ.eq_one_on_inner y hy]
    exact one_ne_zero
  let hηshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω := hχshift.mono_left hηχ
  let Gv : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) := gradientCLM hΩ
    (localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift u)
  let Wv : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
    cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h u
  let Ev : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
    localizedSpatialDifferenceQuotientPrincipalFieldCLM
      hΩ η k h η.tsupport_subset hηshift u
  let Hv : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
    localizedSpatialDifferenceQuotientCompanionFieldCLM
      hΩ η k h η.tsupport_subset hηshift u
  let α : Fin d → Fin d → TimeVelocity d → ℝ :=
    fun i j z => reverseTimeCoefficient r₁ a z.1 z.2 i j
  have htime : r₀ ≤ r₁ - τ ∧ r₁ - τ ≤ r₁ := by
    constructor <;> linarith [hτ.1, hτ.2]
  have hcoef (i j : Fin d) : Continuous
      (fun y : PDE.Vec d => χ y * spatialTranslate k h (α i j) (τ, y)) := by
    rcases haSmooth with ⟨V, hVopen, hCylV, hV⟩
    let m : PDE.Vec d → TimeVelocity d := fun y => (r₁ - τ, y + h • PDE.basisVec k)
    have hmcont : Continuous m :=
      continuous_const.prodMk (continuous_id.add continuous_const)
    have hVm : IsOpen (m ⁻¹' V) := hmcont.isOpen_preimage V hVopen
    have hsupp : tsupport χ.toFun ⊆ m ⁻¹' V := by
      intro y hy
      apply hCylV
      rw [mem_scalarParabolicClosedCylinder_iff]
      refine ⟨htime.1, htime.2, subset_closure (hχshift hy)⟩
    have hentry : ContinuousOn (fun z : TimeVelocity d => a z.1 z.2 i j) V := by
      exact (continuous_apply_apply i j).comp_continuousOn hV.continuousOn
    have hq : ContinuousOn (fun y : PDE.Vec d => spatialTranslate k h (α i j) (τ, y))
        (m ⁻¹' V) := by
      simpa only [spatialTranslate_apply, spatialShift_apply, α,
        reverseTimeCoefficient_apply, Function.comp_def, m] using!
        hentry.comp hmcont.continuousOn (fun _ hy => hy)
    exact HypoellipticAleksandrov.continuous_mul_of_tsupport_subset hVm
      χ.smooth.continuous.continuousOn hsupp hq
  have hcoefCompact (i j : Fin d) : HasCompactSupport
      (fun y : PDE.Vec d => χ y * spatialTranslate k h (α i j) (τ, y)) :=
    χ.hasCompactSupport.mul_right
  have hcoord (X : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞)) (i : Fin d) :
      MemLp (fun y : PDE.Vec d => (X y).toVec i) (2 : ℝ≥0∞) (PDE.volumeOn Ω) := by
    exact MeasureTheory.MemLp.ae_eq
      (PDE.coeFn_hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i X) (Lp.memLp _)
  have hterm (i j : Fin d) : Integrable (fun y : PDE.Vec d =>
      (ζ τ * χ y * spatialTranslate k h (α i j) (τ, y)) *
        PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j Ev y *
        PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Hv y) (PDE.volumeOn Ω) := by
    let q : PDE.Vec d → ℝ := fun y => ζ τ * χ y * spatialTranslate k h (α i j) (τ, y)
    have hqcont : Continuous q := by
      dsimp only [q]
      have hbase := (continuous_const : Continuous (fun _ : PDE.Vec d => ζ τ)).mul
        (hcoef i j)
      simpa only [Pi.mul_def, mul_assoc] using hbase
    have hqcompact : HasCompactSupport q := by
      dsimp only [q]
      simpa only [Pi.mul_def, mul_assoc] using
        ((hcoefCompact i j).mul_left : HasCompactSupport
          ((fun _ : PDE.Vec d => ζ τ) * fun y => χ y * spatialTranslate k h (α i j) (τ, y)))
    have hqtopVolume : MemLp q ∞ (volume : Measure (PDE.Vec d)) :=
      hqcont.memLp_of_hasCompactSupport hqcompact
    have hqtop : MemLp q ∞ (PDE.volumeOn Ω) := by
      simpa only [PDE.volumeOn] using hqtopVolume.restrict Ω
    have hE : MemLp (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j Ev) (2 : ℝ≥0∞)
        (PDE.volumeOn Ω) := Lp.memLp _
    have hH : MemLp (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Hv) (2 : ℝ≥0∞)
        (PDE.volumeOn Ω) := Lp.memLp _
    have hEH := hE.integrable_mul hH
    have hweighted := hEH.mul_of_top_right hqtop
    convert hweighted using 1
    ext y
    simp only [Pi.mul_apply]
    dsimp only [q]
    ring
  have hEraw (i : Fin d) : ∀ᵐ y ∂PDE.volumeOn Ω,
      (Ev y).toVec i = (Gv y).toVec i - (Wv y).toVec i := by
    have hEq : PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Ev =
      PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Gv -
        PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Wv := by
      calc
        _ = PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
            (gradientCLM hΩ (localizedSpatialDifferenceQuotientH10CLM
              hΩ η k h η.tsupport_subset hηshift u)) -
            cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
              (valueCLM hΩ u) := by
          exact hilbertVectorLpCoord_localizedSpatialDifferenceQuotientPrincipalFieldCLM
            hΩ η i k h η.tsupport_subset hηshift u
        _ = _ := by
          rw [show Gv = gradientCLM hΩ (localizedSpatialDifferenceQuotientH10CLM
              hΩ η k h η.tsupport_subset hηshift u) by rfl,
            show Wv = cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h u by rfl,
            hilbertVectorLpCoord_cutoffGradientSpatialDifferenceQuotientH10CLM]
    filter_upwards [MeasureTheory.Lp.coeFn_sub
      (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Gv)
      (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Wv),
      PDE.coeFn_hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Ev,
      PDE.coeFn_hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Gv,
      PDE.coeFn_hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Wv] with y hsub hE hG hW
    rw [hEq, hsub] at hE
    simp only [Pi.sub_apply] at hE
    rw [hG, hW] at hE
    simpa only [PDE.HilbertVec.toVec_apply] using hE.symm
  have hHraw (i : Fin d) : ∀ᵐ y ∂PDE.volumeOn Ω,
      (Hv y).toVec i = (Gv y).toVec i + (Wv y).toVec i := by
    have hEq : PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Hv =
      PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Gv +
        PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Wv := by
      calc
        _ = PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
            (gradientCLM hΩ (localizedSpatialDifferenceQuotientH10CLM
              hΩ η k h η.tsupport_subset hηshift u)) +
            cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
              (valueCLM hΩ u) := by
          exact hilbertVectorLpCoord_localizedSpatialDifferenceQuotientCompanionFieldCLM
            hΩ η i k h η.tsupport_subset hηshift u
        _ = _ := by
          rw [show Gv = gradientCLM hΩ (localizedSpatialDifferenceQuotientH10CLM
              hΩ η k h η.tsupport_subset hηshift u) by rfl,
            show Wv = cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h u by rfl,
            hilbertVectorLpCoord_cutoffGradientSpatialDifferenceQuotientH10CLM]
    filter_upwards [MeasureTheory.Lp.coeFn_add
      (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Gv)
      (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Wv),
      PDE.coeFn_hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Hv,
      PDE.coeFn_hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Gv,
      PDE.coeFn_hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Wv] with y hadd hH hG hW
    rw [hEq, hadd] at hH
    simp only [Pi.add_apply] at hH
    rw [hG, hW] at hH
    simpa only [PDE.HilbertVec.toVec_apply] using hH.symm
  have hEplateau (i : Fin d) : ∀ᵐ y ∂PDE.volumeOn Ω,
      χ y * (Ev y).toVec i = (Ev y).toVec i := by
    let Ecoord := PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Ev
    have hfix : cutoffL2Multiplier (Ω := Ω) χ Ecoord = Ecoord := by
      dsimp only [Ecoord, Ev]
      exact cutoffL2Multiplier_apply_principalFieldCoord hΩ η χ (fun _ hy => hy) i k h
        η.tsupport_subset hηshift u
    filter_upwards [cutoffL2Multiplier_apply_ae χ Ecoord,
      PDE.coeFn_hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Ev] with y hmul hE
    rw [hfix, hE] at hmul
    exact hmul.symm
  have hHplateau (i : Fin d) : ∀ᵐ y ∂PDE.volumeOn Ω,
      χ y * (Hv y).toVec i = (Hv y).toVec i := by
    let Hcoord := PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Hv
    have hfix : cutoffL2Multiplier (Ω := Ω) χ Hcoord = Hcoord := by
      dsimp only [Hcoord, Hv]
      exact cutoffL2Multiplier_apply_companionFieldCoord hΩ η χ (fun _ hy => hy) i k h
        η.tsupport_subset hηshift u
    filter_upwards [cutoffL2Multiplier_apply_ae χ Hcoord,
      PDE.coeFn_hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Hv] with y hmul hH
    rw [hfix, hH] at hmul
    exact hmul.symm
  have hraw : ∀ᵐ y ∂PDE.volumeOn Ω,
      (∀ i : Fin d, (Ev y).toVec i = (Gv y).toVec i - (Wv y).toVec i) ∧
      (∀ i : Fin d, (Hv y).toVec i = (Gv y).toVec i + (Wv y).toVec i) ∧
      (∀ i : Fin d, χ y * (Ev y).toVec i = (Ev y).toVec i) ∧
      (∀ i : Fin d, χ y * (Hv y).toVec i = (Hv y).toVec i) ∧
      (∀ i : Fin d, PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Ev y = (Ev y).toVec i) ∧
      (∀ i : Fin d, PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Hv y = (Hv y).toVec i) := by
    filter_upwards [MeasureTheory.ae_all_iff.mpr hEraw,
      MeasureTheory.ae_all_iff.mpr hHraw,
      MeasureTheory.ae_all_iff.mpr hEplateau,
      MeasureTheory.ae_all_iff.mpr hHplateau,
      MeasureTheory.ae_all_iff.mpr (fun i => PDE.coeFn_hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Ev),
      MeasureTheory.ae_all_iff.mpr (fun i => PDE.coeFn_hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Hv)]
      with y hE hH hχE hχH hEcoor hHcoor
    exact ⟨hE, hH, hχE, hχH, hEcoor, hHcoor⟩
  have hpoint : ∀ᵐ y ∂PDE.volumeOn Ω,
      ζ τ * (lam * ‖Gv y‖ ^ 2 - Lam * ‖Wv y‖ ^ 2) ≤
        ∑ i : Fin d, ∑ j : Fin d,
          (ζ τ * χ y * spatialTranslate k h (α i j) (τ, y)) *
            PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j Ev y *
            PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Hv y := by
    filter_upwards [ae_restrict_mem hΩ.measurableSet, hraw] with y hy hraw
    rcases hraw with ⟨hE, hH, hχE, hχH, hEcoor, hHcoor⟩
    have hcoordsE : (Ev y).toVec = (Gv y).toVec - (Wv y).toVec := funext hE
    have hcoordsH : (Hv y).toVec = (Gv y).toVec + (Wv y).toVec := funext hH
    have htarget : ∀ i j : Fin d,
        spatialTranslate k h (α i j) (τ, y) = a (r₁ - τ) (y + h • PDE.basisVec k) i j := by
      intro i j
      simp only [α, spatialTranslate_apply, spatialShift_apply, reverseTimeCoefficient_apply]
    by_cases hχzero : χ y = 0
    · have hEzero : (Ev y).toVec = 0 := by
        ext i
        change (Ev y).toVec i = 0
        have hi := hχE i
        rw [hχzero] at hi
        simpa using hi.symm
      have hHzero : (Hv y).toVec = 0 := by
        ext i
        change (Hv y).toVec i = 0
        have hi := hχH i
        rw [hχzero] at hi
        simpa using hi.symm
      have hGzero : (Gv y).toVec = 0 := by
        ext i
        change (Gv y).toVec i = 0
        have hEi := hE i
        have hHi := hH i
        have he0 := congrFun hEzero i
        have hh0 := congrFun hHzero i
        simp only [Pi.zero_apply] at he0 hh0
        linarith [hEi, hHi, he0, hh0]
      have hWzero : (Wv y).toVec = 0 := by
        ext i
        change (Wv y).toVec i = 0
        have hEi := hE i
        have hHi := hH i
        have he0 := congrFun hEzero i
        have hh0 := congrFun hHzero i
        simp only [Pi.zero_apply] at he0 hh0
        linarith [hEi, hHi, he0, hh0]
      rw [← hilbertVec_vecNormSq_eq_norm_sq (Gv y),
        ← hilbertVec_vecNormSq_eq_norm_sq (Wv y), hGzero, hWzero,
        vecNormSq_zero, hχzero]
      simp only [mul_zero, zero_mul, Finset.sum_const_zero, sub_zero]
      exact le_rfl
    · have hshift : y + h • PDE.basisVec k ∈ Ω := by
        apply hχshift
        exact subset_tsupport χ.toFun hχzero
      have hAlo : lam • (1 : PDE.Mat d) ≤ a (r₁ - τ) (y + h • PDE.basisVec k) :=
        hLower (r₁ - τ, y + h • PDE.basisVec k) (by
          rw [mem_scalarParabolicClosedCylinder_iff]
          exact ⟨htime.1, htime.2, subset_closure hshift⟩)
      have hAhi : a (r₁ - τ) (y + h • PDE.basisVec k) ≤ Lam • (1 : PDE.Mat d) :=
        hUpper (r₁ - τ, y + h • PDE.basisVec k) (by
          rw [mem_scalarParabolicClosedCylinder_iff]
          exact ⟨htime.1, htime.2, subset_closure hshift⟩)
      have hlo := HypoellipticAleksandrov.vecDot_add_mulVec_sub_lower_of_loewner hAlo hAhi
        (Gv y).toVec (Wv y).toVec
      have hscaled := mul_le_mul_of_nonneg_left hlo hζnonneg
      rw [hilbertVec_vecNormSq_eq_norm_sq (Gv y),
        hilbertVec_vecNormSq_eq_norm_sq (Wv y)] at hscaled
      calc
        ζ τ * (lam * ‖Gv y‖ ^ 2 - Lam * ‖Wv y‖ ^ 2) ≤
            ζ τ * PDE.vecDot ((Gv y).toVec + (Wv y).toVec)
            (Matrix.mulVec (a (r₁ - τ) (y + h • PDE.basisVec k))
              ((Gv y).toVec - (Wv y).toVec)) := hscaled
        _ = ∑ i : Fin d, ∑ j : Fin d,
            (ζ τ * χ y * a (r₁ - τ) (y + h • PDE.basisVec k) i j) *
              (Ev y).toVec j * (Hv y).toVec i := by
          exact weighted_vecDot_add_mulVec_sub_expand (ζ τ) (χ y)
            (a (r₁ - τ) (y + h • PDE.basisVec k))
            (Gv y).toVec (Wv y).toVec (Ev y).toVec (Hv y).toVec
            hcoordsE hcoordsH hχH
        _ = ∑ i : Fin d, ∑ j : Fin d,
            (ζ τ * χ y * spatialTranslate k h (α i j) (τ, y)) *
              PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j Ev y *
              PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Hv y := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [htarget i j, hEcoor j, hHcoor i]
  exact integral_coercivity_of_ae (ζ τ) lam Lam Gv Wv
    (fun i j y =>
      (ζ τ * χ y * spatialTranslate k h (α i j) (τ, y)) *
        PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j Ev y *
        PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i Hv y)
    hterm hpoint

end HypoellipticAleksandrov.Parabolic.Dirichlet
