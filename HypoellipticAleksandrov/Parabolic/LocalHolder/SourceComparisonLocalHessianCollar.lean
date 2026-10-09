module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalHessianBound
public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxCoefficientBounds
public import HypoellipticAleksandrov.Parabolic.QuantitativeSmoothCutoffExistence
public import HypoellipticAleksandrov.Parabolic.OriginalTimePlateau

/-! # Removing Hessian cutoff weights on smaller product collars

Coefficient derivative bounds and smooth plateau cutoffs are chosen before the weak jet.
The resulting estimate controls the actual unweighted Hessian on the inner collar.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set
open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise

/-- A fixed inner collar has a uniform unweighted Hessian estimate for homogeneous jets. -/
theorem exists_local_homogeneous_hessian_collar_constant {d : ℕ}
    (a t₀ t₁ T : ℝ) (hat₀ : a < t₀) (ht₀t₁ : t₀ ≤ t₁) (ht₁T : t₁ < T)
    (O V : Set (PDE.Vec d)) (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVO : closure V ⊆ O)
    (A : CoefficientField d) (hA : IsSmoothCoefficient A)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hlo : HasLowerEllipticity lam A) (hhi : HasUpperEllipticity Lam A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ J : ParabolicW12Function d (Ioo a T ×ˢ O) 2,
      (∀ᵐ z ∂timeVelocityVolumeOn (Ioo a T ×ˢ O),
        J.timeDeriv z + ∑ i, ∑ j, A z.1 z.2 i j * J.velocityHessian z j i = 0) →
      (∫ z in Ioo t₀ t₁ ×ˢ V, ∑ k, ∑ i, J.velocityHessian z k i ^ 2) ≤
        C * ((eLpNorm J.toFun 2 (timeVelocityVolumeOn (Ioo a T ×ˢ O))).toReal ^ 2 +
          ∑ j, (eLpNorm (fun z => J.velocityGrad z j) 2
            (timeVelocityVolumeOn (Ioo a T ×ˢ O))).toReal ^ 2) := by
  classical
  let Q := Ioo a T ×ˢ O
  have hQ : IsOpen Q := isOpen_Ioo.prod hO
  have hQc : IsCompact (closure Q) := by
    rw [closure_prod_eq]
    exact (isCompact_Icc.of_isClosed_subset isClosed_closure
      (closure_minimal Ioo_subset_Icc_self isClosed_Icc)).prod hOc
  obtain ⟨M, hM, hDA⟩ :=
    exists_compact_coefficient_spatial_derivative_bound A hA (closure Q) hQc
  obtain ⟨Kη, ⟨η⟩⟩ := exists_quantitativeSmoothCutoff_tsupport_subset hVc hO hVO
  have hKη : 0 ≤ Kη := (PDE.vecEuclideanNorm_nonneg _).trans (η.gradient_bound 0)
  obtain ⟨ζ, Kζ, hζ, hcζ, hKζ, hζ0, hζ1, hζone, hsζ, hdζ⟩ :=
    exists_smooth_timePlateau_with_deriv_bound a t₀ t₁ T hat₀ ht₀t₁ ht₁T
  have hAs : ∀ t ∈ Ioo a T, ∀ i j,
      ContDiffOn ℝ 1 (fun y => A t y i j) O := by
    intro t _ i j
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => A z.1 z.2 i j) :=
      (contDiff_apply ℝ ℝ j).comp ((contDiff_apply ℝ (Fin d → ℝ) i).comp hA)
    exact ((hc.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)).contDiffOn
  obtain ⟨C, hC, hrun⟩ := exists_local_homogeneous_hessian_constant a T O hO
    (fun z => A z.1 z.2) hA.continuous.aestronglyMeasurable.restrict hAs
    lam Lam M hlam hlamLam hM (fun z _ => hlo z.1 z.2) (fun z _ => hhi z.1 z.2)
    (fun z hz i j k => hDA z (subset_closure hz) i j k)
    η.toFun η.smooth η.hasCompactSupport η.tsupport_subset η.nonneg η.le_one
    Kη hKη (fun y _ i => η.abs_classicalGradient_apply_le y i)
    ζ hζ hcζ hsζ hζ0 hζ1 Kζ hKζ (fun t _ => hdζ t)
  refine ⟨C, hC, ?_⟩
  intro J heq
  let f (z : TimeVelocity d) := ∑ k, ∑ i, J.velocityHessian z k i ^ 2
  have hfi : IntegrableOn f Q := by
    apply integrable_finsetSum
    intro k _
    apply integrable_finsetSum
    intro i _
    simpa only [Real.norm_eq_abs, sq_abs, timeVelocityVolumeOn, IntegrableOn] using
      (J.velocityHessian_memLp k i).integrable_norm_pow (by norm_num)
  have hwcont : Continuous (fun z : TimeVelocity d => ζ z.1 * η.toFun z.2 ^ 2) :=
    (hζ.continuous.comp continuous_fst).mul ((η.smooth.continuous.comp continuous_snd).pow 2)
  have hwbound : ∀ᵐ z ∂volume.restrict Q,
      ‖ζ z.1 * η.toFun z.2 ^ 2‖ ≤ 1 := Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hζ0 _) (sq_nonneg _))]
    exact (mul_le_mul_of_nonneg_left
      (pow_le_one₀ (η.nonneg _) (η.le_one _)) (hζ0 _)).trans
        (by simpa only [mul_one] using hζ1 z.1)
  have hwi := hfi.bdd_mul hwcont.aestronglyMeasurable.restrict hwbound
  have hmono := setIntegral_mono_set hwi
    (Eventually.of_forall (fun z => mul_nonneg
      (mul_nonneg (hζ0 _) (sq_nonneg _))
      (Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun i _ => sq_nonneg _)))))
    (Eventually.of_forall (fun z (hz : z ∈ Ioo t₀ t₁ ×ˢ V) =>
      ⟨⟨hat₀.trans hz.1.1, hz.1.2.trans ht₁T⟩, hVO (subset_closure hz.2)⟩))
  have he : (∫ z in Ioo t₀ t₁ ×ˢ V, ζ z.1 * η.toFun z.2 ^ 2 * f z) =
      ∫ z in Ioo t₀ t₁ ×ˢ V, f z := by
    apply setIntegral_congr_fun (isOpen_Ioo.prod hV).measurableSet
    intro z hz
    change ζ z.1 * η.toFun z.2 ^ 2 * f z = f z
    rw [hζone z.1 ⟨hz.1.1.le, hz.1.2.le⟩,
      η.eq_one_on_inner z.2 (subset_closure hz.2), one_pow, one_mul, one_mul]
  rw [he] at hmono
  exact hmono.trans (hrun J heq)

end HypoellipticAleksandrov.Parabolic.LocalHolder
