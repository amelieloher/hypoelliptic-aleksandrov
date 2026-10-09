module

public import PDEFoundation.Sobolev.Inequalities.SmoothSegment
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Group.Measure

/-!
# Global `L²` control of smooth spatial difference quotients

This file proves the constant-one whole-space estimate needed before local
cutoffs are introduced.
-/

@[expose] public section

open MeasureTheory

private theorem integrable_sq_classicalGradient
    {d : ℕ} (φ : PDE.Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφcompact : HasCompactSupport φ) :
    Integrable (fun y => PDE.vecEuclideanNorm (PDE.classicalGradient φ y) ^ 2)
      (volume : Measure (PDE.Vec d)) := by
  have hcomponent : ∀ i : Fin d,
      Integrable (fun y => ((fderiv ℝ φ y) (PDE.basisVec i)) ^ 2)
      (volume : Measure (PDE.Vec d)) := by
    intro i
    have hc : Continuous (fun y => ((fderiv ℝ φ y) (PDE.basisVec i)) ^ 2) :=
      ((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2
    have hs : HasCompactSupport (fun y => ((fderiv ℝ φ y) (PDE.basisVec i)) ^ 2) :=
      (hφcompact.fderiv_apply ℝ (PDE.basisVec i)).comp_left
        (g := fun x : ℝ => x ^ 2) (by norm_num)
    exact hc.integrable_of_hasCompactSupport hs
  simp_rw [PDE.vecEuclideanNorm_sq, PDE.vecNormSq_eq_sum_sq,
    PDE.classicalGradient_apply]
  exact integrable_finsetSum _ fun i _ => hcomponent i

private theorem spatialDifferenceQuotient_sq_le_segmentIntegral
    {d : ℕ} (φ : PDE.Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (k : Fin d) (h : ℝ) (hh : h ≠ 0) (y : PDE.Vec d) :
    ((φ (y + h • PDE.basisVec k) - φ y) / h) ^ 2 ≤
      ∫ t in (0 : ℝ)..1,
        PDE.vecEuclideanNorm (PDE.classicalGradient φ (y + t • (h • PDE.basisVec k))) ^ 2 := by
  let z : PDE.Vec d := h • PDE.basisVec k
  have hbase := PDE.abs_sub_rpow_le_integral_euclideanGradient_mul_distance_rpow
    (p := (2 : ℝ)) (by norm_num) hφ (y + z) y
  have hnormz : PDE.vecEuclideanNorm z = |h| := by
    rw [show z = h • PDE.basisVec k by rfl,
      PDE.vecEuclideanNorm_smul, PDE.vecEuclideanNorm_basisVec]
    simp
  have hbase' : |φ (y + z) - φ y| ^ (2 : ℝ) ≤
      ∫ t in (0 : ℝ)..1,
        (PDE.vecEuclideanNorm (PDE.classicalGradient φ (y + t • z)) * |h|) ^ (2 : ℝ) := by
    simpa only [PDE.segmentBlend_eq_add_smul_sub, add_sub_cancel_left, hnormz] using hbase
  have hsq : 0 < h ^ 2 := sq_pos_of_ne_zero hh
  have hdivide : |φ (y + z) - φ y| ^ (2 : ℝ) / h ^ 2 ≤
      (∫ t in (0 : ℝ)..1,
        (PDE.vecEuclideanNorm (PDE.classicalGradient φ (y + t • z)) * |h|) ^ (2 : ℝ)) / h ^ 2 :=
    (div_le_div_iff_of_pos_right hsq).mpr hbase'
  rw [← intervalIntegral.integral_div] at hdivide
  have hrewrite : (fun t : ℝ =>
      (PDE.vecEuclideanNorm (PDE.classicalGradient φ (y + t • z)) * |h|) ^ (2 : ℝ) / h ^ 2) =
      fun t => PDE.vecEuclideanNorm (PDE.classicalGradient φ (y + t • z)) ^ 2 := by
    funext t
    rw [Real.rpow_two]
    ring_nf
    rw [sq_abs]
    field_simp
  rw [hrewrite] at hdivide
  have hleft : ((φ (y + z) - φ y) / h) ^ 2 =
      |φ (y + z) - φ y| ^ (2 : ℝ) / h ^ 2 := by
    rw [Real.rpow_two, sq_abs]
    field_simp
  calc
    ((φ (y + h • PDE.basisVec k) - φ y) / h) ^ 2 =
        ((φ (y + z) - φ y) / h) ^ 2 := by simp only [z]
    _ = |φ (y + z) - φ y| ^ (2 : ℝ) / h ^ 2 := hleft
    _ ≤ ∫ t in (0 : ℝ)..1,
        PDE.vecEuclideanNorm (PDE.classicalGradient φ (y + t • z)) ^ 2 := hdivide
    _ = ∫ t in (0 : ℝ)..1,
        PDE.vecEuclideanNorm
          (PDE.classicalGradient φ (y + t • (h • PDE.basisVec k))) ^ 2 := by
      simp only [z]

private theorem integrable_sq_spatialDifferenceQuotient
    {d : ℕ} (φ : PDE.Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφcompact : HasCompactSupport φ)
    (k : Fin d) (h : ℝ) :
    Integrable (fun y => ((φ (y + h • PDE.basisVec k) - φ y) / h) ^ 2)
      (volume : Measure (PDE.Vec d)) := by
  let z : PDE.Vec d := h • PDE.basisVec k
  have htranslatecontinuous : Continuous (fun y : PDE.Vec d => φ (y + z)) := by
    exact hφ.continuous.comp (Homeomorph.addRight z).continuous
  have htranslatesupport : HasCompactSupport (fun y : PDE.Vec d => φ (y + z)) := by
    have hs := hφcompact.comp_homeomorph (Homeomorph.addRight z)
    simpa only [Function.comp_def, Homeomorph.coe_addRight] using hs
  have hdiffcontinuous : Continuous (fun y : PDE.Vec d => φ (y + z) - φ y) :=
    htranslatecontinuous.sub hφ.continuous
  have hdiffsupport : HasCompactSupport (fun y : PDE.Vec d => φ (y + z) - φ y) := by
    simpa only [Pi.sub_def] using htranslatesupport.sub hφcompact
  have hqcontinuous : Continuous (fun y : PDE.Vec d => ((φ (y + z) - φ y) / h) ^ 2) :=
    by simpa only [div_eq_mul_inv, Pi.mul_def, Pi.pow_def] using
      (hdiffcontinuous.mul continuous_const).pow 2
  have hqsupport : HasCompactSupport (fun y : PDE.Vec d => ((φ (y + z) - φ y) / h) ^ 2) :=
    hdiffsupport.comp_left (g := fun x : ℝ => (x / h) ^ 2) (by simp)
  simpa only [z] using hqcontinuous.integrable_of_hasCompactSupport hqsupport

private theorem integrable_translate_segmentAverage
    {d : ℕ} (g : PDE.Vec d → ℝ)
    (hg : Integrable g (volume : Measure (PDE.Vec d))) (z : PDE.Vec d) :
    Integrable (fun y => ∫ t in (0 : ℝ)..1, g (y + t • z))
      (volume : Measure (PDE.Vec d)) := by
  have hshear : MeasurePreserving
      (fun p : ℝ × PDE.Vec d => (p.1, p.2 + p.1 • z))
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
        (volume : Measure (PDE.Vec d)))
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
        (volume : Measure (PDE.Vec d))) := by
    refine MeasurePreserving.skew_product (g := fun t y => y + t • z)
      (MeasurePreserving.id _) ?_ ?_
    · exact measurable_snd.add (measurable_fst.smul measurable_const)
    · filter_upwards [] with t
      exact (measurePreserving_add_right volume (t • z)).map_eq
  have hproduct : Integrable (fun p : ℝ × PDE.Vec d => g p.2)
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
        (volume : Measure (PDE.Vec d))) :=
    hg.comp_snd _
  have hcomposed : Integrable (fun p : ℝ × PDE.Vec d => g (p.2 + p.1 • z))
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
        (volume : Measure (PDE.Vec d))) := by
    simpa only [Function.comp_def] using hshear.integrable_comp_of_integrable hproduct
  have hright := hcomposed.integral_prod_right
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    Function.uncurry] using hright

private theorem integral_translate_segmentAverage
    {d : ℕ} (g : PDE.Vec d → ℝ)
    (hg : Integrable g (volume : Measure (PDE.Vec d))) (z : PDE.Vec d) :
    (∫ y, ∫ t in (0 : ℝ)..1, g (y + t • z)) = ∫ y, g y := by
  have hshear : MeasurePreserving
      (fun p : ℝ × PDE.Vec d => (p.1, p.2 + p.1 • z))
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
        (volume : Measure (PDE.Vec d)))
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
        (volume : Measure (PDE.Vec d))) := by
    refine MeasurePreserving.skew_product (g := fun t y => y + t • z)
      (MeasurePreserving.id _) ?_ ?_
    · exact measurable_snd.add (measurable_fst.smul measurable_const)
    · filter_upwards [] with t
      exact (measurePreserving_add_right volume (t • z)).map_eq
  have hproduct : Integrable (fun p : ℝ × PDE.Vec d => g p.2)
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
        (volume : Measure (PDE.Vec d))) :=
    hg.comp_snd _
  have hcomposed : Integrable (fun p : ℝ × PDE.Vec d => g (p.2 + p.1 • z))
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
        (volume : Measure (PDE.Vec d))) := by
    simpa only [Function.comp_def] using hshear.integrable_comp_of_integrable hproduct
  have hcomposed' : Integrable (Function.uncurry fun t y => g (y + t • z))
      ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod
        (volume : Measure (PDE.Vec d))) := by
    simpa only [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), Function.uncurry_def]
      using hcomposed
  have hswap : (∫ t in (0 : ℝ)..1, ∫ y, g (y + t • z)) =
      ∫ y, ∫ t in (0 : ℝ)..1, g (y + t • z) := by
    exact intervalIntegral_integral_swap hcomposed'
  rw [← hswap]
  simp_rw [show (fun t : ℝ => ∫ y, g (y + t • z)) = fun _ => ∫ y, g y by
    funext t
    exact (measurePreserving_add_right volume (t • z)).integral_comp
      (Homeomorph.addRight _).measurableEmbedding g]
  simp

/-- A signed coordinate difference quotient of a smooth compactly supported
function is controlled in global `L²` by its Euclidean classical gradient.
The quotient is totalized at `h = 0`. -/
theorem integral_sq_spatialDifferenceQuotient_le_integral_sq_classicalGradient
    {d : ℕ} (φ : PDE.Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφcompact : HasCompactSupport φ)
    (k : Fin d) (h : ℝ) :
    (∫ y, ((φ (y + h • PDE.basisVec k) - φ y) / h) ^ 2
      ∂(volume : Measure (PDE.Vec d))) ≤
      ∫ y, PDE.vecEuclideanNorm (PDE.classicalGradient φ y) ^ 2
        ∂(volume : Measure (PDE.Vec d)) := by
  by_cases hh : h = 0
  · simp only [hh, zero_smul, add_zero, sub_self, zero_div]
    simp only [pow_two, zero_mul, integral_zero]
    apply integral_nonneg
    intro y
    simpa only [Pi.zero_apply, pow_two] using
      sq_nonneg (PDE.vecEuclideanNorm (PDE.classicalGradient φ y))
  let g : PDE.Vec d → ℝ :=
    fun y => PDE.vecEuclideanNorm (PDE.classicalGradient φ y) ^ 2
  have hg : Integrable g (volume : Measure (PDE.Vec d)) :=
    integrable_sq_classicalGradient φ hφ hφcompact
  have hq : Integrable (fun y => ((φ (y + h • PDE.basisVec k) - φ y) / h) ^ 2)
      (volume : Measure (PDE.Vec d)) :=
    integrable_sq_spatialDifferenceQuotient φ hφ hφcompact k h
  have hr : Integrable (fun y => ∫ t in (0 : ℝ)..1,
      g (y + t • (h • PDE.basisVec k))) (volume : Measure (PDE.Vec d)) :=
    integrable_translate_segmentAverage g hg _
  have hpoint : ∀ y : PDE.Vec d,
      ((φ (y + h • PDE.basisVec k) - φ y) / h) ^ 2 ≤
        ∫ t in (0 : ℝ)..1, g (y + t • (h • PDE.basisVec k)) := by
    intro y
    exact spatialDifferenceQuotient_sq_le_segmentIntegral φ hφ k h hh y
  calc
    (∫ y, ((φ (y + h • PDE.basisVec k) - φ y) / h) ^ 2) ≤
        ∫ y, ∫ t in (0 : ℝ)..1, g (y + t • (h • PDE.basisVec k)) :=
      integral_mono_ae hq hr (Filter.Eventually.of_forall hpoint)
    _ = ∫ y, g y := integral_translate_segmentAverage g hg _
    _ = ∫ y, PDE.vecEuclideanNorm (PDE.classicalGradient φ y) ^ 2 := rfl
