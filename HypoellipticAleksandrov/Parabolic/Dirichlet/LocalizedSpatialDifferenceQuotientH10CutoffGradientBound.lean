module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientPrincipalField

/-!
# Aggregate cutoff-gradient bound for localized spatial difference quotients

This module controls the full Hilbert-vector cutoff-gradient commutator by
the weak gradient of the input.  The proof keeps the Euclidean cutoff-gradient
bound intact, so no coordinate-count factor is introduced.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private theorem cutoffGradientL2Multiplier_apply_ae
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner outer K) (i : Fin d)
    (f : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ⇑(cutoffGradientL2Multiplier (Ω := Ω) η i f) =ᵐ[PDE.volumeOn Ω]
      fun y => PDE.classicalGradient η.toFun y i * f y := by
  simpa only [cutoffGradientL2Multiplier] using
    (scalarL2Multiplier_apply_ae
      (fun y : PDE.Vec d => PDE.classicalGradient η.toFun y i) _ K _ _ f)

/-- The assembled cutoff-gradient commutator field is uniformly controlled
by the input weak gradient through any larger shifted plateau cutoff. -/
theorem norm_sq_cutoffGradientSpatialDifferenceQuotientH10CLM_apply_le_gradient
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (hΩ : IsOpen Ω)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (k : Fin d) (h : ℝ)
    (hχshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport χ.toFun) Ω)
    (u : H10HilbertGraph hΩ) :
    ‖cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h u‖ ^ 2 ≤
      Kη ^ 2 * ‖gradientCLM hΩ u‖ ^ 2 := by
  let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
    intro y hy
    apply subset_tsupport
    change χ y ≠ 0
    rw [χ.eq_one_on_inner y hy]
    exact one_ne_zero
  let hηshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω := hχshift.mono_left hηχ
  let Q : PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
    valueCLM hΩ
      (localizedSpatialDifferenceQuotientH10CLM
        hΩ χ k h χ.tsupport_subset hχshift u)
  let W : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
    cutoffGradientSpatialDifferenceQuotientH10CLM hΩ η k h u
  have hfactor (i : Fin d) :
      cutoffGradientSpatialDifferenceQuotientL2
          hΩ.measurableSet η i k h (valueCLM hΩ u) =
        cutoffGradientL2Multiplier (Ω := Ω) η i Q := by
    dsimp only [Q]
    exact cutoffGradientSpatialDifferenceQuotientL2_apply_valueCLM_eq
      hΩ η χ subset_rfl i k h χ.tsupport_subset hχshift u
  have hcoord (i : Fin d) :
      ⇑(cutoffGradientSpatialDifferenceQuotientL2
        hΩ.measurableSet η i k h (valueCLM hΩ u)) =ᵐ[PDE.volumeOn Ω]
        fun y => PDE.classicalGradient η.toFun y i * Q y := by
    rw [hfactor i]
    exact cutoffGradientL2Multiplier_apply_ae η i Q
  have hcoords : ∀ᵐ y : PDE.Vec d ∂PDE.volumeOn Ω, ∀ i : Fin d,
      cutoffGradientSpatialDifferenceQuotientL2
          hΩ.measurableSet η i k h (valueCLM hΩ u) y =
        PDE.classicalGradient η.toFun y i * Q y := by
    apply ae_all_iff.mpr
    intro i
    exact hcoord i
  have hassemble : ⇑W =ᵐ[PDE.volumeOn Ω]
      fun y => WithLp.toLp 2 (fun i =>
        cutoffGradientSpatialDifferenceQuotientL2
          hΩ.measurableSet η i k h (valueCLM hΩ u) y) := by
    dsimp only [W, cutoffGradientSpatialDifferenceQuotientH10CLM]
    simpa only [ContinuousLinearMap.comp_apply] using
      (PDE.hilbertVectorLpAssemble_apply_ae
        (fun i => (cutoffGradientSpatialDifferenceQuotientL2
          hΩ.measurableSet η i k h).comp (valueCLM hΩ)) u)
  have hWae : ⇑W =ᵐ[PDE.volumeOn Ω]
      fun y => Q y • (PDE.classicalGradient η.toFun y).toHilbertVec := by
    filter_upwards [hcoords, hassemble] with y hcoords hassemble
    rw [hassemble]
    apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).injective
    ext i
    change cutoffGradientSpatialDifferenceQuotientL2
        hΩ.measurableSet η i k h (valueCLM hΩ u) y =
      Q y * PDE.classicalGradient η.toFun y i
    rw [hcoords i]
    ring
  let g : PDE.Vec d → ℝ := fun y =>
    PDE.vecEuclideanNorm (PDE.classicalGradient η.toFun y)
  let w : PDE.Vec d → ℝ := fun y => |Q y| * g y
  have hnorm : (fun y => ‖W y‖) =ᵐ[PDE.volumeOn Ω] w := by
    filter_upwards [hWae] with y hW
    rw [hW]
    dsimp only [w, g]
    rw [norm_smul, Real.norm_eq_abs,
      PDE.HilbertVec.norm_eq_vecEuclideanNorm,
      PDE.HilbertVec.toVec_toHilbertVec]
  have hWint : Integrable (fun y => w y ^ 2) (PDE.volumeOn Ω) := by
    refine (show Integrable (fun y => ‖W y‖ ^ 2) (PDE.volumeOn Ω) by
      simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) W W).congr ?_
    filter_upwards [hnorm] with y hy
    rw [hy]
  have hQint : Integrable (fun y => Q y ^ 2) (PDE.volumeOn Ω) := by
    refine (show Integrable (fun y => ‖Q y‖ ^ 2) (PDE.volumeOn Ω) by
      simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) Q Q).congr ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, sq_abs]
  have hpoint : ∀ y : PDE.Vec d, w y ^ 2 ≤ Kη ^ 2 * Q y ^ 2 := by
    intro y
    have hgrad := η.gradient_bound y
    have hleft : |Q y| * g y ≤ |Q y| * Kη :=
      mul_le_mul_of_nonneg_left hgrad (abs_nonneg _)
    have hnonnegLeft : 0 ≤ |Q y| * g y :=
      mul_nonneg (abs_nonneg _) (PDE.vecEuclideanNorm_nonneg _)
    have hnonnegRight : 0 ≤ |Q y| * Kη :=
      mul_nonneg (abs_nonneg _) η.gradient_bound_nonneg
    calc
      w y ^ 2 = (|Q y| * g y) ^ 2 := rfl
      _ ≤ (|Q y| * Kη) ^ 2 := (sq_le_sq₀ hnonnegLeft hnonnegRight).mpr hleft
      _ = |Q y| ^ 2 * Kη ^ 2 := by ring
      _ = Kη ^ 2 * Q y ^ 2 := by rw [sq_abs]; ring
  have hWenergy : (∫ y, w y ^ 2 ∂PDE.volumeOn Ω) = ‖W‖ ^ 2 :=
    PDE.integral_norm_sq_eq_sq_norm_of_ae_eq_hilbert W w hnorm
  have hQenergy : (∫ y, Q y ^ 2 ∂PDE.volumeOn Ω) = ‖Q‖ ^ 2 :=
    PDE.integral_sq_eq_sq_norm_of_ae_eq Q (fun y => Q y)
      (Filter.Eventually.of_forall fun _ => rfl)
  have hQbound : ‖Q‖ ≤ ‖gradientCLM hΩ u‖ := by
    dsimp only [Q]
    exact norm_valueCLM_localizedSpatialDifferenceQuotientH10CLM_apply_le_gradient
      hΩ χ k h χ.tsupport_subset hχshift u
  change ‖W‖ ^ 2 ≤ Kη ^ 2 * ‖gradientCLM hΩ u‖ ^ 2
  calc
    ‖W‖ ^ 2 = ∫ y, w y ^ 2 ∂PDE.volumeOn Ω := hWenergy.symm
    _ ≤ ∫ y, Kη ^ 2 * Q y ^ 2 ∂PDE.volumeOn Ω :=
      integral_mono_ae hWint (hQint.const_mul (Kη ^ 2))
        (Filter.Eventually.of_forall hpoint)
    _ = Kη ^ 2 * ‖Q‖ ^ 2 := by
      rw [integral_const_mul, hQenergy]
    _ ≤ Kη ^ 2 * ‖gradientCLM hΩ u‖ ^ 2 :=
      mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hQbound)
        (sq_nonneg _)

end HypoellipticAleksandrov.Parabolic.Dirichlet
