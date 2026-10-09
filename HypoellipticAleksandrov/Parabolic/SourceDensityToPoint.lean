module

public import HypoellipticAleksandrov.Parabolic.DensityToPoint
public import HypoellipticAleksandrov.Parabolic.ScalingMeasure

/-!
# Source-aware density-to-point relations for parabolic boxes

This file records the supplied-source analogue of the transparent
`DensityToPoint` relation.  Its scaled form keeps the source on the literal
open parabolic box and has the exact `R^(d / (d + 1))` error factor.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- A relative unit-box superlevel-set bound forces a lower terminal bound,
up to the supplied nonnegative source norm. -/
def SourceDensityToPoint (d : ℕ) (lam Lam beta g C : ℝ) : Prop :=
  ∀ (U : Set (TimeVelocity d)) (B : CoefficientField d)
    (F u : TimeVelocity d → ℝ),
    IsOpen U →
    parabolicClosedBox 1 1 0 0 ⊆ U →
    IsContinuousCoefficientOn B U →
    ContDiffOn ℝ 2 u U →
    ContinuousOn F U →
    IsNonnegativeOn u (parabolicBox 1 1 0 0) →
    IsNonnegativeOn F (parabolicBox 1 1 0 0) →
    HasLowerEllipticityOn lam B (parabolicBox 1 1 0 0) →
    HasUpperEllipticityOn Lam B (parabolicBox 1 1 0 0) →
    IsParabolicSupersolutionOn B (fun z ↦ -F z) u
      (parabolicBox 1 1 0 0) →
    beta * ((volume : Measure (TimeVelocity d))
      (parabolicBox 1 1 0 0)).toReal ≤
      ((volume : Measure (TimeVelocity d))
        (parabolicBox 1 1 0 0 ∩ {z | 1 ≤ u z})).toReal →
    ∀ v ∈ velocityClosedCube (0 : PDE.Vec d) (1 / 2),
      g ≤ u (1, v) + C * parabolicLpNormOn d F
        (parabolicBox 1 1 0 0)

/-- Eliminates a source-aware density-to-point relation at fixed local data. -/
theorem SourceDensityToPoint.apply {d : ℕ} {lam Lam beta g C : ℝ}
    (h : SourceDensityToPoint d lam Lam beta g C) (U : Set (TimeVelocity d))
    (B : CoefficientField d) (F u : TimeVelocity d → ℝ) (hU : IsOpen U)
    (hclosed : parabolicClosedBox 1 1 0 0 ⊆ U)
    (hB : IsContinuousCoefficientOn B U) (hu : ContDiffOn ℝ 2 u U)
    (hF : ContinuousOn F U)
    (hnonneg : IsNonnegativeOn u (parabolicBox 1 1 0 0))
    (hFnonneg : IsNonnegativeOn F (parabolicBox 1 1 0 0))
    (hlower : HasLowerEllipticityOn lam B (parabolicBox 1 1 0 0))
    (hupper : HasUpperEllipticityOn Lam B (parabolicBox 1 1 0 0))
    (hsuper : IsParabolicSupersolutionOn B (fun z ↦ -F z) u
      (parabolicBox 1 1 0 0))
    (hdensity : beta * ((volume : Measure (TimeVelocity d))
      (parabolicBox 1 1 0 0)).toReal ≤
      ((volume : Measure (TimeVelocity d))
        (parabolicBox 1 1 0 0 ∩ {z | 1 ≤ u z})).toReal)
    (v : PDE.Vec d) (hv : v ∈ velocityClosedCube (0 : PDE.Vec d) (1 / 2)) :
    g ≤ u (1, v) + C * parabolicLpNormOn d F (parabolicBox 1 1 0 0) :=
  h U B F u hU hclosed hB hu hF hnonneg hFnonneg hlower hupper hsuper hdensity v hv

/-- Increasing the required density preserves a source-aware relation. -/
theorem SourceDensityToPoint.mono_density {d : ℕ} {lam Lam beta beta' g C : ℝ}
    (hbeta : beta ≤ beta') (h : SourceDensityToPoint d lam Lam beta g C) :
    SourceDensityToPoint d lam Lam beta' g C := by
  intro U B F u hU hclosed hB hu hF hnonneg hFnonneg hlower hupper hsuper hdensity v hv
  refine h.apply U B F u hU hclosed hB hu hF hnonneg hFnonneg hlower hupper hsuper ?_ v hv
  calc
    beta * ((volume : Measure (TimeVelocity d)) (parabolicBox 1 1 0 0)).toReal ≤
        beta' * ((volume : Measure (TimeVelocity d)) (parabolicBox 1 1 0 0)).toReal := by
      gcongr
    _ ≤ ((volume : Measure (TimeVelocity d))
      (parabolicBox 1 1 0 0 ∩ {z | 1 ≤ u z})).toReal := hdensity

/-- Decreasing the asserted terminal value preserves a source-aware relation. -/
theorem SourceDensityToPoint.mono_value {d : ℕ} {lam Lam beta g g' C : ℝ}
    (hg : g' ≤ g) (h : SourceDensityToPoint d lam Lam beta g C) :
    SourceDensityToPoint d lam Lam beta g' C := by
  intro U B F u hU hclosed hB hu hF hnonneg hFnonneg hlower hupper hsuper hdensity v hv
  exact hg.trans (h.apply U B F u hU hclosed hB hu hF hnonneg hFnonneg hlower hupper
    hsuper hdensity v hv)

/-- Increasing the source-error coefficient preserves a source-aware relation. -/
theorem SourceDensityToPoint.mono_error {d : ℕ} {lam Lam beta g C C' : ℝ}
    (hC : C ≤ C') (h : SourceDensityToPoint d lam Lam beta g C) :
    SourceDensityToPoint d lam Lam beta g C' := by
  intro U B F u hU hclosed hB hu hF hnonneg hFnonneg hlower hupper hsuper hdensity v hv
  have hnorm : 0 ≤ parabolicLpNormOn d F (parabolicBox 1 1 0 0) := by
    exact ENNReal.toReal_nonneg
  calc
    g ≤ u (1, v) + C * parabolicLpNormOn d F (parabolicBox 1 1 0 0) :=
      h.apply U B F u hU hclosed hB hu hF hnonneg hFnonneg hlower hupper hsuper hdensity v hv
    _ ≤ u (1, v) + C' * parabolicLpNormOn d F (parabolicBox 1 1 0 0) := by
      gcongr

private theorem IsParabolicSupersolutionOn.const_smul_source
    {d : ℕ} {B : CoefficientField d} {f u : TimeVelocity d → ℝ}
    {V : Set (TimeVelocity d)} {c : ℝ} (hc : 0 ≤ c)
    (h : IsParabolicSupersolutionOn B f u V) :
    IsParabolicSupersolutionOn B (fun z ↦ c * f z) (c • u) V := by
  intro z hz
  rw [parabolicOperator_const_smul]
  exact mul_le_mul_of_nonneg_left (h z hz) hc

/-- Parabolic affine scaling preserves the source-aware relation with the
exact source-norm scaling factor. -/
theorem SourceDensityToPoint.scaled {d : ℕ} {lam Lam beta g C : ℝ}
    (h : SourceDensityToPoint d lam Lam beta g C)
    {R eps t₀ : ℝ} {v₀ : PDE.Vec d}
    (hR : 0 < R) (heps : 0 < eps)
    (U : Set (TimeVelocity d)) (B : CoefficientField d)
    (F u : TimeVelocity d → ℝ) (hU : IsOpen U)
    (hclosed : parabolicClosedBox 1 R t₀ v₀ ⊆ U)
    (hB : IsContinuousCoefficientOn B U)
    (hu : ContDiffOn ℝ 2 u U) (hF : ContinuousOn F U)
    (hnonneg : IsNonnegativeOn u (parabolicBox 1 R t₀ v₀))
    (hFnonneg : IsNonnegativeOn F (parabolicBox 1 R t₀ v₀))
    (hlower : HasLowerEllipticityOn lam B (parabolicBox 1 R t₀ v₀))
    (hupper : HasUpperEllipticityOn Lam B (parabolicBox 1 R t₀ v₀))
    (hsuper : IsParabolicSupersolutionOn B (fun z ↦ -F z) u
      (parabolicBox 1 R t₀ v₀))
    (hdensity : beta * ((volume : Measure (TimeVelocity d))
      (parabolicBox 1 R t₀ v₀)).toReal ≤
      ((volume : Measure (TimeVelocity d))
        (parabolicBox 1 R t₀ v₀ ∩ {z | eps ≤ u z})).toReal) :
    ∀ v ∈ velocityClosedCube v₀ (R / 2),
      eps * g ≤ u (t₀ + R ^ 2, v) +
        C * R ^ ((d : ℝ) / ((d : ℝ) + 1)) *
          parabolicLpNormOn d F (parabolicBox 1 R t₀ v₀) := by
  let a := parabolicAffine t₀ v₀ R
  let V := a ⁻¹' U
  let uHat : TimeVelocity d → ℝ := eps⁻¹ • pullbackScalar u t₀ v₀ R
  let FHat : TimeVelocity d → ℝ := fun z ↦ eps⁻¹ * (R ^ 2 * F (a z))
  have hmapU : MapsTo a V U := fun _ hz => hz
  have hmapBox : MapsTo a (parabolicBox 1 1 0 0) (parabolicBox 1 R t₀ v₀) :=
    mapsTo_parabolicAffine_parabolicBox hR
  have hVopen : IsOpen V :=
    hU.preimage (contDiff_parabolicAffine t₀ v₀ R).continuous
  have hVclosed : parabolicClosedBox 1 1 0 0 ⊆ V := by
    intro z hz
    exact hclosed (mapsTo_parabolicAffine_parabolicClosedBox hR hz)
  have hBpull : IsContinuousCoefficientOn (pullbackCoefficient B t₀ v₀ R) V :=
    IsContinuousCoefficientOn.pullback hB hmapU
  have hupull : ContDiffOn ℝ 2 (pullbackScalar u t₀ v₀ R) V :=
    ContDiffOn.pullbackScalar hu hmapU
  have hFpull : ContinuousOn (pullbackScalar F t₀ v₀ R) V := by
    simpa only [pullbackScalar, Function.comp_def] using
      hF.comp (contDiff_parabolicAffine t₀ v₀ R).continuous.continuousOn hmapU
  have hnonnegpull : IsNonnegativeOn (pullbackScalar u t₀ v₀ R)
      (parabolicBox 1 1 0 0) :=
    hnonneg.pullbackScalar hmapBox
  have hFnonnegpull : IsNonnegativeOn (pullbackScalar F t₀ v₀ R)
      (parabolicBox 1 1 0 0) :=
    hFnonneg.pullbackScalar hmapBox
  have hlowerpull : HasLowerEllipticityOn lam (pullbackCoefficient B t₀ v₀ R)
      (parabolicBox 1 1 0 0) :=
    hlower.pullback hmapBox
  have hupperpull : HasUpperEllipticityOn Lam (pullbackCoefficient B t₀ v₀ R)
      (parabolicBox 1 1 0 0) :=
    hupper.pullback hmapBox
  have hboxU : parabolicBox 1 R t₀ v₀ ⊆ U := by
    rintro ⟨t, v⟩ ⟨⟨ht0, htR⟩, hv⟩
    exact hclosed ⟨⟨ht0.le, htR.le⟩, fun i ↦ (hv i).le⟩
  have hsuperpull : IsParabolicSupersolutionOn (pullbackCoefficient B t₀ v₀ R)
      (fun z ↦ R ^ 2 * (-F (a z))) (pullbackScalar u t₀ v₀ R)
      (parabolicBox 1 1 0 0) := by
    simpa only [a] using IsParabolicSupersolutionOn.pullback
      (U := parabolicBox 1 R t₀ v₀) (V := parabolicBox 1 1 0 0)
      (isOpen_parabolicBox 1 R t₀ v₀) (hu.mono hboxU) hsuper hmapBox
  have hinvnonneg : 0 ≤ eps⁻¹ := inv_nonneg.mpr heps.le
  have hnormalnonneg : IsNonnegativeOn uHat (parabolicBox 1 1 0 0) := by
    intro z hz
    exact mul_nonneg hinvnonneg (hnonnegpull z hz)
  have hFHat : ContinuousOn FHat V := by
    dsimp only [FHat, a]
    exact continuousOn_const.mul (continuousOn_const.mul hFpull)
  have hFHatnonneg : IsNonnegativeOn FHat (parabolicBox 1 1 0 0) := by
    intro z hz
    dsimp only [FHat, a]
    exact mul_nonneg hinvnonneg (mul_nonneg (sq_nonneg R) (hFnonnegpull z hz))
  have hnormalsuper : IsParabolicSupersolutionOn (pullbackCoefficient B t₀ v₀ R)
      (fun z ↦ -FHat z) uHat (parabolicBox 1 1 0 0) := by
    dsimp only [uHat, FHat, a]
    simpa only [Pi.smul_apply, smul_eq_mul, mul_neg] using
      hsuperpull.const_smul_source hinvnonneg
  let c : ℝ≥0∞ := ENNReal.ofReal |LinearMap.det (parabolicLinear (d := d) R :
    TimeVelocity d →ₗ[ℝ] TimeVelocity d)|
  have hcne : c ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]
    exact abs_pos.mpr (parabolicLinear_det_ne_zero hR)
  have hcpos : 0 < c.toReal := ENNReal.toReal_pos hcne ENNReal.ofReal_ne_top
  have hbox : (volume : Measure (TimeVelocity d)) (parabolicBox 1 R t₀ v₀) =
      c * (volume : Measure (TimeVelocity d)) (parabolicBox 1 1 0 0) := by
    rw [← parabolicAffine_image_parabolicBox hR]
    exact volume_parabolicAffine_image t₀ v₀ R _
  have hlevel : (volume : Measure (TimeVelocity d))
      (parabolicBox 1 R t₀ v₀ ∩ {z | eps ≤ u z}) =
      c * (volume : Measure (TimeVelocity d)) (parabolicBox 1 1 0 0 ∩
        {z | 1 ≤ uHat z}) := by
    rw [show uHat = eps⁻¹ • pullbackScalar u t₀ v₀ R by rfl,
      ← parabolicAffine_image_normalizedSuperlevel hR heps]
    exact volume_parabolicAffine_image t₀ v₀ R _
  have hnormaldensity : beta * ((volume : Measure (TimeVelocity d))
      (parabolicBox 1 1 0 0)).toReal ≤
      ((volume : Measure (TimeVelocity d)) (parabolicBox 1 1 0 0 ∩
        {z | 1 ≤ uHat z})).toReal := by
    rw [hbox, hlevel, ENNReal.toReal_mul, ENNReal.toReal_mul] at hdensity
    suffices hscaled : c.toReal * (beta * ((volume : Measure (TimeVelocity d))
        (parabolicBox 1 1 0 0)).toReal) ≤ c.toReal *
        ((volume : Measure (TimeVelocity d)) (parabolicBox 1 1 0 0 ∩
          {z | 1 ≤ uHat z})).toReal by
      nlinarith
    calc
      c.toReal * (beta * ((volume : Measure (TimeVelocity d))
          (parabolicBox 1 1 0 0)).toReal) =
          beta * (c.toReal * ((volume : Measure (TimeVelocity d))
            (parabolicBox 1 1 0 0)).toReal) := by ring
      _ ≤ c.toReal * ((volume : Measure (TimeVelocity d)) (parabolicBox 1 1 0 0 ∩
          {z | 1 ≤ uHat z})).toReal := hdensity
  have hnorm : parabolicLpNormOn d FHat (parabolicBox 1 1 0 0) =
      eps⁻¹ * (R ^ ((d : ℝ) / ((d : ℝ) + 1)) *
        parabolicLpNormOn d F (parabolicBox 1 R t₀ v₀)) := by
    calc
      parabolicLpNormOn d FHat (parabolicBox 1 1 0 0) =
          eps⁻¹ * parabolicLpNormOn d (fun z ↦ R ^ 2 * F (a z))
            (parabolicBox 1 1 0 0) := by
        dsimp only [FHat]
        unfold parabolicLpNormOn parabolicELpNormOn
        change (eLpNorm (eps⁻¹ • fun z ↦ R ^ 2 * F (a z)) (parabolicExponent d)
          (volume.restrict (parabolicBox 1 1 0 0))).toReal = _
        rw [eLpNorm_const_smul, ENNReal.toReal_mul]
        simp only [Real.enorm_of_nonneg hinvnonneg,
          ENNReal.toReal_ofReal hinvnonneg]
      _ = eps⁻¹ * (R ^ ((d : ℝ) / ((d : ℝ) + 1)) *
          parabolicLpNormOn d F (parabolicBox 1 R t₀ v₀)) := by
        rw [parabolicLpNormOn_pullback t₀ v₀ hR F,
          parabolicAffine_image_parabolicBox hR]
  intro v hv
  let w : PDE.Vec d := R⁻¹ • (v - v₀)
  have hw : w ∈ velocityClosedCube (0 : PDE.Vec d) (1 / 2) := by
    intro i
    have hvi := hv i
    dsimp [w]
    simp only [sub_zero]
    rw [abs_mul, abs_inv, abs_of_pos hR]
    exact (inv_mul_le_iff₀ hR).mpr (by simpa only [mul_comm, div_eq_mul_inv, one_mul] using hvi)
  have hpoint := h.apply V (pullbackCoefficient B t₀ v₀ R) FHat uHat hVopen hVclosed
    hBpull (hupull.const_smul eps⁻¹) hFHat hnormalnonneg hFHatnonneg hlowerpull hupperpull
    hnormalsuper hnormaldensity w hw
  rw [hnorm] at hpoint
  have haeval : a (1, w) = (t₀ + R ^ 2, v) := by
    dsimp [a, w, parabolicAffine]
    ext
    · ring
    · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul]
      ring
  have hdivision : g ≤ u (t₀ + R ^ 2, v) / eps +
      C * (R ^ ((d : ℝ) / ((d : ℝ) + 1)) *
        parabolicLpNormOn d F (parabolicBox 1 R t₀ v₀) / eps) := by
    rw [← haeval]
    simpa only [a, uHat, FHat, Pi.smul_apply, pullbackScalar_apply, smul_eq_mul,
      mul_assoc, inv_mul_eq_div] using hpoint
  calc
    eps * g ≤ eps * (u (t₀ + R ^ 2, v) / eps +
        C * (R ^ ((d : ℝ) / ((d : ℝ) + 1)) *
          parabolicLpNormOn d F (parabolicBox 1 R t₀ v₀) / eps)) :=
      mul_le_mul_of_nonneg_left hdivision heps.le
    _ = u (t₀ + R ^ 2, v) + C * R ^ ((d : ℝ) / ((d : ℝ) + 1)) *
          parabolicLpNormOn d F (parabolicBox 1 R t₀ v₀) := by
      field_simp [heps.ne']

end

end HypoellipticAleksandrov.Parabolic
