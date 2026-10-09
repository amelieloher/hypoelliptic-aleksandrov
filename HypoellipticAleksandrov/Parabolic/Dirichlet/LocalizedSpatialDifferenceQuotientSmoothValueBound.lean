module

public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientSmoothL2
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientL2
public import HypoellipticAleksandrov.Parabolic.Dirichlet.WeakTestFunctionSobolevJet
public import PDEFoundation.Sobolev.W1p.GraphEnergy

/-!
# Sharp localized value bound on smooth Dirichlet tests

The global smooth difference-quotient estimate descends to the restricted
value class of an actual compactly supported smooth Dirichlet test without a
step-size collar assumption.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private theorem zeroExtend_value_eq_smoothWeakTest_ae
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (φ : PDE.WeakTestFunction Ω) :
    ⇑(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ.measurableSet
      (valueCLM hΩ
        (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ))) =ᵐ[volume] φ := by
  let f : PDE.ScalarLp Ω (2 : ℝ≥0∞) := valueCLM hΩ
    (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ)
  have hvalue : ⇑f =ᵐ[PDE.volumeOn Ω] φ := by
    exact ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ φ
  have hzero := MeasureTheory.Lp.coeFn_zeroExtendLinearIsometry hΩ.measurableSet f
  have hvalue' := ae_imp_of_ae_restrict hvalue
  filter_upwards [hzero, hvalue'] with y hzero hvalue
  rw [hzero]
  by_cases hy : y ∈ Ω
  · rw [Set.indicator_of_mem hy]
    exact hvalue hy
  · rw [Set.indicator_of_notMem hy]
    have hnot : y ∉ tsupport φ := fun hsupport => hy (φ.tsupport_subset hsupport)
    exact (image_eq_zero_of_notMem_tsupport hnot).symm

private theorem localizedSpatialDifferenceQuotientL2_apply_smooth_ae
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω) :
    ⇑(localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h
      (valueCLM hΩ
        (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ))) =ᵐ[PDE.volumeOn Ω]
      localizedSpatialDifferenceQuotient η k h φ := by
  let f : PDE.ScalarLp Ω (2 : ℝ≥0∞) := valueCLM hΩ
    (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ)
  have hambient : ⇑(MeasureTheory.Lp.zeroExtendLinearIsometry hΩ.measurableSet f) =ᵐ[volume] φ := by
    simpa only [f] using zeroExtend_value_eq_smoothWeakTest_ae hΩ φ
  have hlocal := localizedSpatialDifferenceQuotientL2_apply_ae hΩ.measurableSet η k h f
  have hshifted := (measurePreserving_add_right (volume : Measure (PDE.Vec d))
    (h • PDE.basisVec k)).quasiMeasurePreserving.ae hambient
  filter_upwards [hlocal, ae_restrict_of_ae hambient,
    ae_restrict_of_ae hshifted] with y hlocal hambient hshifted
  rw [hlocal]
  simp only [localizedSpatialDifferenceQuotient_apply]
  rw [hambient, hshifted]

private theorem integrable_sq_smoothWeakTest_differenceQuotient
    {d : ℕ} {Ω : Set (PDE.Vec d)} (φ : PDE.WeakTestFunction Ω)
    (k : Fin d) (h : ℝ) :
    Integrable (fun y => ((φ (y + h • PDE.basisVec k) - φ y) / h) ^ 2)
      (volume : Measure (PDE.Vec d)) := by
  let z : PDE.Vec d := h • PDE.basisVec k
  have htranslatecontinuous : Continuous (fun y : PDE.Vec d => φ (y + z)) := by
    exact φ.contDiff.continuous.comp (Homeomorph.addRight z).continuous
  have htranslatesupport : HasCompactSupport (fun y : PDE.Vec d => φ (y + z)) := by
    have hs := φ.hasCompactSupport.comp_homeomorph (Homeomorph.addRight z)
    simpa only [Function.comp_def, Homeomorph.coe_addRight] using hs
  have hdiffcontinuous : Continuous (fun y : PDE.Vec d => φ (y + z) - φ y) :=
    htranslatecontinuous.sub φ.contDiff.continuous
  have hdiffsupport : HasCompactSupport (fun y : PDE.Vec d => φ (y + z) - φ y) := by
    simpa only [Pi.sub_def] using htranslatesupport.sub φ.hasCompactSupport
  have hqcontinuous : Continuous (fun y : PDE.Vec d => ((φ (y + z) - φ y) / h) ^ 2) :=
    by simpa only [div_eq_mul_inv, Pi.pow_def, Pi.mul_def] using
      (hdiffcontinuous.mul continuous_const).pow 2
  have hqsupport : HasCompactSupport (fun y : PDE.Vec d => ((φ (y + z) - φ y) / h) ^ 2) :=
    hdiffsupport.comp_left (g := fun x : ℝ => (x / h) ^ 2) (by simp)
  simpa only [z] using hqcontinuous.integrable_of_hasCompactSupport hqsupport

private theorem integrable_sq_localizedSpatialDifferenceQuotient_smoothWeakTest
    {d : ℕ} {inner outer : Set (PDE.Vec d)} {K : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (f : PDE.Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (k : Fin d) (h : ℝ) :
    Integrable (fun y => localizedSpatialDifferenceQuotient η k h f y ^ 2)
      (volume : Measure (PDE.Vec d)) := by
  have hcont : Continuous (fun y => localizedSpatialDifferenceQuotient η k h f y ^ 2) :=
    (ContDiff.localizedSpatialDifferenceQuotient hf η k h).continuous.pow 2
  have hsupp : HasCompactSupport (fun y => localizedSpatialDifferenceQuotient η k h f y ^ 2) :=
    (localizedSpatialDifferenceQuotient_hasCompactSupport η k h f).comp_left
      (g := fun x : ℝ => x ^ 2) (by norm_num)
  exact hcont.integrable_of_hasCompactSupport hsupp

private theorem sq_localizedSpatialDifferenceQuotient_le_sq_differenceQuotient
    {d : ℕ} {inner outer : Set (PDE.Vec d)} {K : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (f : PDE.Vec d → ℝ) (y : PDE.Vec d) (k : Fin d) (h : ℝ) :
    localizedSpatialDifferenceQuotient η k h f y ^ 2 ≤
      ((f (y + h • PDE.basisVec k) - f y) / h) ^ 2 := by
  rw [localizedSpatialDifferenceQuotient_apply]
  have hnonneg := η.nonneg y
  have hleone := η.le_one y
  have hsq : η.toFun y ^ 2 ≤ (1 : ℝ) ^ 2 :=
    (sq_le_sq₀ hnonneg zero_le_one).mpr hleone
  calc
    (η.toFun y * ((f (y + h • PDE.basisVec k) - f y) / h)) ^ 2 =
        η.toFun y ^ 2 * ((f (y + h • PDE.basisVec k) - f y) / h) ^ 2 := by ring
    _ ≤ (1 : ℝ) ^ 2 * ((f (y + h • PDE.basisVec k) - f y) / h) ^ 2 :=
      mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    _ = ((f (y + h • PDE.basisVec k) - f y) / h) ^ 2 := by norm_num

private theorem integral_sq_classicalGradient_eq_restrict
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (φ : PDE.WeakTestFunction Ω) :
    (∫ y, PDE.vecEuclideanNorm (PDE.classicalGradient φ y) ^ 2) =
      ∫ y, PDE.vecEuclideanNorm (PDE.classicalGradient φ y) ^ 2 ∂PDE.volumeOn Ω := by
  rw [← MeasureTheory.setIntegral_univ]
  rw [MeasureTheory.setIntegral_eq_of_subset_of_forall_diff_eq_zero MeasurableSet.univ
    (Set.subset_univ Ω)]
  intro y hy
  have hynot : y ∉ tsupport φ := fun hsupport => hy.2 (φ.tsupport_subset hsupport)
  unfold PDE.classicalGradient
  have hfderiv : fderiv ℝ φ y = 0 := fderiv_of_notMem_tsupport ℝ hynot
  rw [hfderiv]
  simp [PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot]

private theorem ae_norm_gradientCLM_smoothWeakTest_eq_classicalGradient
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (φ : PDE.WeakTestFunction Ω) :
    (fun y => ‖gradientCLM hΩ
      (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ) y‖)
      =ᵐ[PDE.volumeOn Ω]
      fun y => PDE.vecEuclideanNorm (PDE.classicalGradient φ y) := by
  have hcoords : ∀ᵐ y : PDE.Vec d ∂PDE.volumeOn Ω, ∀ j : Fin d,
      gradientCLM hΩ
        (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ) y j =
        φ.partialDeriv j y := by
    apply ae_all_iff.mpr
    intro j
    exact ae_gradientCoordCLM_smoothCompactlySupportedH1HilbertGraph hΩ φ j
  filter_upwards [hcoords] with y hcoords
  have hvec : gradientCLM hΩ
      (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ) y =
      PDE.toHilbertVecField (PDE.classicalGradient φ) y := by
    apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).injective
    ext j
    simpa only [PiLp.coe_continuousLinearEquiv, PiLp.coe_symm_continuousLinearEquiv,
      PDE.toHilbertVecField_apply, PDE.Vec.toHilbertVec_apply,
      PDE.classicalGradient_apply, PDE.WeakTestFunction.partialDeriv] using hcoords j
  rw [hvec]
  exact PDE.norm_toHilbertVecField_apply _ _

/-- The localized quotient of an actual smooth zero-boundary test is
controlled by its weak-gradient `L²` norm. -/
theorem norm_localizedSpatialDifferenceQuotientL2_apply_smooth_le_gradient
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω)
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω) :
    ‖localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h
        (valueCLM hΩ
          (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ))‖ ≤
      ‖gradientCLM hΩ
        (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ)‖ := by
  let u : H10HilbertGraph hΩ :=
    smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ φ
  let Q : PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
    localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h (valueCLM hΩ u)
  let G : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) := gradientCLM hΩ u
  let q : PDE.Vec d → ℝ := fun y =>
    ((φ (y + h • PDE.basisVec k) - φ y) / h)
  let ℓ : PDE.Vec d → ℝ := localizedSpatialDifferenceQuotient η k h φ
  let g : PDE.Vec d → ℝ := fun y =>
    PDE.vecEuclideanNorm (PDE.classicalGradient φ y)
  have hQae : ⇑Q =ᵐ[PDE.volumeOn Ω] ℓ := by
    dsimp only [Q, u, ℓ]
    exact localizedSpatialDifferenceQuotientL2_apply_smooth_ae hΩ η k h φ
  have hqint : Integrable (fun y => q y ^ 2) (volume : Measure (PDE.Vec d)) := by
    simpa only [q] using integrable_sq_smoothWeakTest_differenceQuotient φ k h
  have hℓint : Integrable (fun y => ℓ y ^ 2) (volume : Measure (PDE.Vec d)) := by
    simpa only [ℓ] using integrable_sq_localizedSpatialDifferenceQuotient_smoothWeakTest
      η φ φ.contDiff k h
  have hcutoff : ∀ y : PDE.Vec d, ℓ y ^ 2 ≤ q y ^ 2 := by
    intro y
    exact sq_localizedSpatialDifferenceQuotient_le_sq_differenceQuotient η φ y k h
  have hlocalLeRaw : (∫ y, ℓ y ^ 2 ∂PDE.volumeOn Ω) ≤ ∫ y, q y ^ 2 := by
    calc
      (∫ y, ℓ y ^ 2 ∂PDE.volumeOn Ω) ≤ ∫ y, q y ^ 2 ∂PDE.volumeOn Ω :=
        integral_mono_ae hℓint.restrict hqint.restrict
          (Filter.Eventually.of_forall hcutoff)
      _ ≤ ∫ y, q y ^ 2 :=
        MeasureTheory.setIntegral_le_integral hqint
          (Filter.Eventually.of_forall fun y => sq_nonneg (q y))
  have hglobal : (∫ y, q y ^ 2) ≤ ∫ y, g y ^ 2 := by
    simpa only [q, g] using
      integral_sq_spatialDifferenceQuotient_le_integral_sq_classicalGradient
        φ φ.contDiff φ.hasCompactSupport k h
  have hgradientRestrict : (∫ y, g y ^ 2) = ∫ y, g y ^ 2 ∂PDE.volumeOn Ω := by
    simpa only [g] using integral_sq_classicalGradient_eq_restrict φ
  have hGae : (fun y => ‖G y‖) =ᵐ[PDE.volumeOn Ω] g := by
    simpa only [G, u, g] using
      ae_norm_gradientCLM_smoothWeakTest_eq_classicalGradient hΩ φ
  have hGenergy : (∫ y, g y ^ 2 ∂PDE.volumeOn Ω) = ‖G‖ ^ 2 :=
    PDE.integral_norm_sq_eq_sq_norm_of_ae_eq_hilbert G g hGae
  have hQenergy : (∫ y, ℓ y ^ 2 ∂PDE.volumeOn Ω) = ‖Q‖ ^ 2 :=
    PDE.integral_sq_eq_sq_norm_of_ae_eq Q ℓ hQae
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  calc
    ‖Q‖ ^ 2 = ∫ y, ℓ y ^ 2 ∂PDE.volumeOn Ω := hQenergy.symm
    _ ≤ ∫ y, q y ^ 2 := hlocalLeRaw
    _ ≤ ∫ y, g y ^ 2 := hglobal
    _ = ∫ y, g y ^ 2 ∂PDE.volumeOn Ω := hgradientRestrict
    _ = ‖G‖ ^ 2 := hGenergy

end HypoellipticAleksandrov.Parabolic.Dirichlet
