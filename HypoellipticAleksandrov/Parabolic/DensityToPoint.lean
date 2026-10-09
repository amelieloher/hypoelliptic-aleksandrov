module

public import HypoellipticAleksandrov.Parabolic.Scaling
public import HypoellipticAleksandrov.Measure.TimeVelocity

/-!
# Density-to-point relations for parabolic boxes

This file defines the transparent density-to-point relation used in the
parabolic Krylov--Safonov argument and proves its elementary monotonicity API.
The local sign, ellipticity, and supersolution hypotheses are imposed on the
open box itself, while continuity and `C²` regularity hold on a neighborhood of
its closed counterpart.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- A relative superlevel-set bound on the unit parabolic box forces a lower
bound on its closed terminal half-cube. -/
def DensityToPoint (d : ℕ) (lam Lam beta g : ℝ) : Prop :=
  ∀ (U : Set (TimeVelocity d)) (B : CoefficientField d) (u : TimeVelocity d → ℝ),
    IsOpen U →
    parabolicClosedBox 1 1 0 0 ⊆ U →
    IsContinuousCoefficientOn B U →
    ContDiffOn ℝ 2 u U →
    IsNonnegativeOn u (parabolicBox 1 1 0 0) →
    HasLowerEllipticityOn lam B (parabolicBox 1 1 0 0) →
    HasUpperEllipticityOn Lam B (parabolicBox 1 1 0 0) →
    IsParabolicSupersolutionOn B (fun _ ↦ 0) u (parabolicBox 1 1 0 0) →
    beta * ((volume : Measure (TimeVelocity d)) (parabolicBox 1 1 0 0)).toReal ≤
      ((volume : Measure (TimeVelocity d))
        (parabolicBox 1 1 0 0 ∩ {z | 1 ≤ u z})).toReal →
    ∀ v ∈ velocityClosedCube (0 : PDE.Vec d) (1 / 2), g ≤ u (1, v)

/-- Eliminates a density-to-point relation at fixed local coefficient and solution data. -/
theorem DensityToPoint.apply {d : ℕ} {lam Lam beta g : ℝ}
    (h : DensityToPoint d lam Lam beta g) (U : Set (TimeVelocity d))
    (B : CoefficientField d) (u : TimeVelocity d → ℝ) (hU : IsOpen U)
    (hclosed : parabolicClosedBox 1 1 0 0 ⊆ U)
    (hB : IsContinuousCoefficientOn B U) (hu : ContDiffOn ℝ 2 u U)
    (hnonneg : IsNonnegativeOn u (parabolicBox 1 1 0 0))
    (hlower : HasLowerEllipticityOn lam B (parabolicBox 1 1 0 0))
    (hupper : HasUpperEllipticityOn Lam B (parabolicBox 1 1 0 0))
    (hsuper : IsParabolicSupersolutionOn B (fun _ ↦ 0) u (parabolicBox 1 1 0 0))
    (hdensity : beta * ((volume : Measure (TimeVelocity d))
      (parabolicBox 1 1 0 0)).toReal ≤
      ((volume : Measure (TimeVelocity d))
        (parabolicBox 1 1 0 0 ∩ {z | 1 ≤ u z})).toReal)
    (v : PDE.Vec d) (hv : v ∈ velocityClosedCube (0 : PDE.Vec d) (1 / 2)) :
    g ≤ u (1, v) :=
  h U B u hU hclosed hB hu hnonneg hlower hupper hsuper hdensity v hv

/-- Increasing the required density preserves a density-to-point relation. -/
theorem DensityToPoint.mono_density {d : ℕ} {lam Lam beta beta' g : ℝ}
    (hbeta : beta ≤ beta') (h : DensityToPoint d lam Lam beta g) :
    DensityToPoint d lam Lam beta' g := by
  intro U B u hU hclosed hB hu hnonneg hlower hupper hsuper hdensity v hv
  refine h.apply U B u hU hclosed hB hu hnonneg hlower hupper hsuper ?_ v hv
  calc
    beta * ((volume : Measure (TimeVelocity d)) (parabolicBox 1 1 0 0)).toReal ≤
        beta' * ((volume : Measure (TimeVelocity d)) (parabolicBox 1 1 0 0)).toReal := by
      gcongr
    _ ≤ ((volume : Measure (TimeVelocity d))
      (parabolicBox 1 1 0 0 ∩ {z | 1 ≤ u z})).toReal := hdensity

/-- Decreasing the asserted terminal value preserves a density-to-point relation. -/
theorem DensityToPoint.mono_value {d : ℕ} {lam Lam beta g g' : ℝ}
    (hg : g' ≤ g) (h : DensityToPoint d lam Lam beta g) :
    DensityToPoint d lam Lam beta g' := by
  intro U B u hU hclosed hB hu hnonneg hlower hupper hsuper hdensity v hv
  exact hg.trans (h.apply U B u hU hclosed hB hu hnonneg hlower hupper hsuper hdensity v hv)

/-- Parabolic affine scaling sends the closed reference box into its translated counterpart. -/
theorem mapsTo_parabolicAffine_parabolicClosedBox {d : ℕ} {vartheta r t₀ : ℝ}
    {v₀ : PDE.Vec d} (hr : 0 < r) :
    MapsTo (parabolicAffine t₀ v₀ r) (parabolicClosedBox vartheta 1 0 0)
      (parabolicClosedBox vartheta r t₀ v₀) := by
  intro z hz
  rcases hz with ⟨⟨hz₀, hz₁⟩, hzv⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · dsimp [parabolicAffine]
    nlinarith [sq_pos_of_pos hr]
  · dsimp [parabolicAffine]
    nlinarith [sq_pos_of_pos hr]
  · intro i
    have hi := hzv i
    dsimp [parabolicAffine]
    have hi' : |z.2 i| ≤ 1 := by
      simpa only [Pi.zero_apply, sub_zero] using hi
    rw [add_sub_cancel_left, abs_mul, abs_of_pos hr]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hi' hr.le

/-- Multiplying a scalar function by a constant scales the parabolic operator by that constant. -/
theorem parabolicOperator_const_smul {d : ℕ} (B : CoefficientField d)
    (c : ℝ) (u : TimeVelocity d → ℝ) (z : TimeVelocity d) :
    parabolicOperator B (c • u) z = c * parabolicOperator B u z := by
  have hfirst : fderiv ℝ (c • u) = c • fderiv ℝ u :=
    fderiv_const_smul_field c
  have htime : timeDerivative (c • u) z = c * timeDerivative u z := by
    unfold timeDerivative
    rw [fderiv_const_smul_field]
    rfl
  have hhessian : velocityHessian (c • u) z = c • velocityHessian u z := by
    have hsecond : fderiv ℝ (fderiv ℝ (c • u)) z =
        c • fderiv ℝ (fderiv ℝ u) z := by
      rw [hfirst]
      exact congrFun (fderiv_const_smul_field (f := fderiv ℝ u) c) z
    ext i j
    unfold velocityHessian
    rw [hsecond]
    rfl
  rw [parabolicOperator_apply, parabolicOperator_apply, htime, hhessian,
    HypoellipticAleksandrov.matrixContraction_smul_right]
  ring

/-- A positive constant multiple of a local zero-source supersolution is again one. -/
theorem IsParabolicSupersolutionOn.const_smul {d : ℕ} {B : CoefficientField d}
    {u : TimeVelocity d → ℝ} {V : Set (TimeVelocity d)} {c : ℝ} (hc : 0 ≤ c)
    (h : IsParabolicSupersolutionOn B (fun _ ↦ 0) u V) :
    IsParabolicSupersolutionOn B (fun _ ↦ 0) (c • u) V := by
  intro z hz
  rw [parabolicOperator_const_smul]
  exact mul_nonneg hc (h z hz)

/-- The linear part of positive-radius parabolic scaling is injective. -/
theorem parabolicLinear_injective {d : ℕ} {r : ℝ} (hr : 0 < r) :
    Function.Injective (parabolicLinear (d := d) r) := by
  intro z w hzw
  have htime := congrArg Prod.fst hzw
  have hvelocity := congrArg Prod.snd hzw
  rw [parabolicLinear_apply, parabolicLinear_apply] at htime hvelocity
  apply Prod.ext
  · nlinarith [sq_pos_of_pos hr]
  · ext i
    have hi := congrFun hvelocity i
    simp only [Pi.smul_apply, smul_eq_mul] at hi
    nlinarith

/-- The determinant of the positive-radius parabolic linear part is nonzero. -/
theorem parabolicLinear_det_ne_zero {d : ℕ} {r : ℝ} (hr : 0 < r) :
    LinearMap.det (parabolicLinear (d := d) r : TimeVelocity d →ₗ[ℝ] TimeVelocity d) ≠ 0 := by
  intro hdet
  have hker : LinearMap.ker (parabolicLinear (d := d) r : TimeVelocity d →ₗ[ℝ]
      TimeVelocity d) ≠ ⊥ :=
    (LinearMap.det_eq_zero_iff_ker_ne_bot).mp hdet
  exact hker (LinearMap.ker_eq_bot_of_injective (parabolicLinear_injective hr))

/-- Positive-radius parabolic affine scaling is surjective. -/
theorem parabolicAffine_surjective {d : ℕ} {t₀ r : ℝ} {v₀ : PDE.Vec d}
    (hr : 0 < r) : Function.Surjective (parabolicAffine t₀ v₀ r) := by
  intro z
  refine ⟨((z.1 - t₀) / r ^ 2, r⁻¹ • (z.2 - v₀)), ?_⟩
  ext
  · dsimp [parabolicAffine]
    field_simp [hr.ne']
    ring
  · dsimp [parabolicAffine]
    rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
    ring

/-- The affine image of any set has the determinant factor of its parabolic linear part. -/
theorem volume_parabolicAffine_image {d : ℕ} (t₀ : ℝ) (v₀ : PDE.Vec d) (r : ℝ)
    (s : Set (TimeVelocity d)) :
    (volume : Measure (TimeVelocity d)) (parabolicAffine t₀ v₀ r '' s) =
      ENNReal.ofReal |LinearMap.det (parabolicLinear (d := d) r :
        TimeVelocity d →ₗ[ℝ] TimeVelocity d)| * volume s := by
  let q : TimeVelocity d := (t₀, v₀)
  have ha : parabolicAffine t₀ v₀ r = fun z ↦ q + parabolicLinear r z := by
    funext z
    ext <;> simp [q, parabolicAffine, parabolicLinear]
  calc
    (volume : Measure (TimeVelocity d)) (parabolicAffine t₀ v₀ r '' s) =
        volume ((fun z ↦ q + z) '' (parabolicLinear r '' s)) := by
      rw [ha, Set.image_image]
    _ = volume ((fun z ↦ -q + z) ⁻¹' (parabolicLinear r '' s)) := by
      rw [Set.image_add_left]
    _ = volume (parabolicLinear r '' s) := by
      rw [measure_preimage_add]
    _ = ENNReal.ofReal |LinearMap.det (parabolicLinear (d := d) r :
        TimeVelocity d →ₗ[ℝ] TimeVelocity d)| * volume s := by
      exact Measure.addHaar_image_continuousLinearMap volume (parabolicLinear r) s

/-- The normalized and translated open boxes are exact affine images. -/
theorem parabolicAffine_image_parabolicBox {d : ℕ} {vartheta r t₀ : ℝ}
    {v₀ : PDE.Vec d} (hr : 0 < r) :
    parabolicAffine t₀ v₀ r '' parabolicBox vartheta 1 0 0 =
      parabolicBox vartheta r t₀ v₀ := by
  calc
    parabolicAffine t₀ v₀ r '' parabolicBox vartheta 1 0 0 =
        parabolicAffine t₀ v₀ r ''
          (parabolicAffine t₀ v₀ r ⁻¹' parabolicBox vartheta r t₀ v₀) := by
      congr 1
      ext z
      exact (mem_parabolicAffine_preimage_parabolicBox_iff hr).symm
    _ = parabolicBox vartheta r t₀ v₀ :=
      Set.image_preimage_eq _ (parabolicAffine_surjective hr)

/-- Superlevel sets in a translated box are exact affine images after amplitude normalization. -/
theorem parabolicAffine_image_normalizedSuperlevel {d : ℕ} {r t₀ eps : ℝ}
    {v₀ : PDE.Vec d} {u : TimeVelocity d → ℝ} (hr : 0 < r) (heps : 0 < eps) :
    parabolicAffine t₀ v₀ r ''
        (parabolicBox 1 1 0 0 ∩ {z | 1 ≤ eps⁻¹ • pullbackScalar u t₀ v₀ r z}) =
      parabolicBox 1 r t₀ v₀ ∩ {z | eps ≤ u z} := by
  calc
    parabolicAffine t₀ v₀ r ''
        (parabolicBox 1 1 0 0 ∩ {z | 1 ≤ eps⁻¹ • pullbackScalar u t₀ v₀ r z}) =
      parabolicAffine t₀ v₀ r ''
        (parabolicAffine t₀ v₀ r ⁻¹'
          (parabolicBox 1 r t₀ v₀ ∩ {z | eps ≤ u z})) := by
      congr 1
      ext z
      constructor
      · rintro ⟨hzbox, hzlevel⟩
        refine ⟨(mem_parabolicAffine_preimage_parabolicBox_iff hr).mpr hzbox, ?_⟩
        have hlevel : 1 ≤ u (parabolicAffine t₀ v₀ r z) / eps := by
          simpa [div_eq_mul_inv, mul_comm, pullbackScalar_apply] using hzlevel
        simpa using (le_div_iff₀ heps).mp hlevel
      · rintro ⟨hzbox, hzlevel⟩
        refine ⟨(mem_parabolicAffine_preimage_parabolicBox_iff hr).mp hzbox, ?_⟩
        change eps ≤ u (parabolicAffine t₀ v₀ r z) at hzlevel
        have hlevel : 1 ≤ u (parabolicAffine t₀ v₀ r z) / eps :=
          (le_div_iff₀ heps).mpr (by simpa using hzlevel)
        simpa [div_eq_mul_inv, mul_comm, pullbackScalar_apply] using hlevel
    _ = parabolicBox 1 r t₀ v₀ ∩ {z | eps ≤ u z} :=
      Set.image_preimage_eq _ (parabolicAffine_surjective hr)

/-- The density-to-point relation has the translated, parabolically scaled, and
amplitude-normalized form of Krylov--Safonov's Lemma 1.1. -/
theorem DensityToPoint.scaled {d : ℕ} {lam Lam beta g : ℝ}
    (h : DensityToPoint d lam Lam beta g) {R eps t₀ : ℝ} {v₀ : PDE.Vec d}
    (hR : 0 < R) (heps : 0 < eps) (U : Set (TimeVelocity d))
    (B : CoefficientField d) (u : TimeVelocity d → ℝ) (hU : IsOpen U)
    (hclosed : parabolicClosedBox 1 R t₀ v₀ ⊆ U)
    (hB : IsContinuousCoefficientOn B U) (hu : ContDiffOn ℝ 2 u U)
    (hnonneg : IsNonnegativeOn u (parabolicBox 1 R t₀ v₀))
    (hlower : HasLowerEllipticityOn lam B (parabolicBox 1 R t₀ v₀))
    (hupper : HasUpperEllipticityOn Lam B (parabolicBox 1 R t₀ v₀))
    (hsuper : IsParabolicSupersolutionOn B (fun _ ↦ 0) u (parabolicBox 1 R t₀ v₀))
    (hdensity : beta * ((volume : Measure (TimeVelocity d))
      (parabolicBox 1 R t₀ v₀)).toReal ≤
      ((volume : Measure (TimeVelocity d))
        (parabolicBox 1 R t₀ v₀ ∩ {z | eps ≤ u z})).toReal) :
    ∀ v ∈ velocityClosedCube v₀ (R / 2), eps * g ≤ u (t₀ + R ^ 2, v) := by
  let a := parabolicAffine t₀ v₀ R
  let V := a ⁻¹' U
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
  have hnonnegpull : IsNonnegativeOn (pullbackScalar u t₀ v₀ R)
      (parabolicBox 1 1 0 0) :=
    hnonneg.pullbackScalar hmapBox
  have hlowerpull : HasLowerEllipticityOn lam (pullbackCoefficient B t₀ v₀ R)
      (parabolicBox 1 1 0 0) :=
    hlower.pullback hmapBox
  have hupperpull : HasUpperEllipticityOn Lam (pullbackCoefficient B t₀ v₀ R)
      (parabolicBox 1 1 0 0) :=
    hupper.pullback hmapBox
  have hsuperpull : IsParabolicSupersolutionOn (pullbackCoefficient B t₀ v₀ R)
      (fun _ ↦ 0) (pullbackScalar u t₀ v₀ R) (parabolicBox 1 1 0 0) := by
    have hboxU : parabolicBox 1 R t₀ v₀ ⊆ U := by
      intro z hz
      rcases hz with ⟨⟨hz₀, hz₁⟩, hzv⟩
      apply hclosed
      exact ⟨⟨hz₀.le, hz₁.le⟩, fun i ↦ (hzv i).le⟩
    simpa using IsParabolicSupersolutionOn.pullback
      (U := parabolicBox 1 R t₀ v₀) (V := parabolicBox 1 1 0 0)
      (isOpen_parabolicBox 1 R t₀ v₀) (hu.mono hboxU)
      hsuper hmapBox
  have hinvnonneg : 0 ≤ eps⁻¹ := inv_nonneg.mpr heps.le
  have hnormalnonneg : IsNonnegativeOn (eps⁻¹ • pullbackScalar u t₀ v₀ R)
      (parabolicBox 1 1 0 0) := by
    intro z hz
    exact mul_nonneg hinvnonneg (hnonnegpull z hz)
  have hnormalsuper : IsParabolicSupersolutionOn (pullbackCoefficient B t₀ v₀ R)
      (fun _ ↦ 0) (eps⁻¹ • pullbackScalar u t₀ v₀ R) (parabolicBox 1 1 0 0) :=
    hsuperpull.const_smul hinvnonneg
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
        {z | 1 ≤ eps⁻¹ • pullbackScalar u t₀ v₀ R z}) := by
    rw [← parabolicAffine_image_normalizedSuperlevel hR heps]
    exact volume_parabolicAffine_image t₀ v₀ R _
  have hnormaldensity : beta * ((volume : Measure (TimeVelocity d))
      (parabolicBox 1 1 0 0)).toReal ≤
      ((volume : Measure (TimeVelocity d)) (parabolicBox 1 1 0 0 ∩
        {z | 1 ≤ eps⁻¹ • pullbackScalar u t₀ v₀ R z})).toReal := by
    rw [hbox, hlevel, ENNReal.toReal_mul, ENNReal.toReal_mul] at hdensity
    suffices hscaled : c.toReal * (beta * ((volume : Measure (TimeVelocity d))
        (parabolicBox 1 1 0 0)).toReal) ≤ c.toReal *
        ((volume : Measure (TimeVelocity d)) (parabolicBox 1 1 0 0 ∩
          {z | 1 ≤ eps⁻¹ • pullbackScalar u t₀ v₀ R z})).toReal by
      nlinarith
    calc
      c.toReal * (beta * ((volume : Measure (TimeVelocity d))
          (parabolicBox 1 1 0 0)).toReal) =
          beta * (c.toReal * ((volume : Measure (TimeVelocity d))
            (parabolicBox 1 1 0 0)).toReal) := by ring
      _ ≤ c.toReal * ((volume : Measure (TimeVelocity d)) (parabolicBox 1 1 0 0 ∩
          {z | 1 ≤ eps⁻¹ • pullbackScalar u t₀ v₀ R z})).toReal := hdensity
  intro v hv
  let w : PDE.Vec d := R⁻¹ • (v - v₀)
  have hw : w ∈ velocityClosedCube (0 : PDE.Vec d) (1 / 2) := by
    intro i
    have hvi := hv i
    dsimp [w]
    simp only [sub_zero]
    rw [abs_mul, abs_inv, abs_of_pos hR]
    exact (inv_mul_le_iff₀ hR).mpr (by simpa only [div_eq_mul_inv, one_mul, mul_comm] using hvi)
  have hpoint := h.apply V (pullbackCoefficient B t₀ v₀ R)
    (eps⁻¹ • pullbackScalar u t₀ v₀ R) hVopen hVclosed hBpull
    (hupull.const_smul eps⁻¹) hnormalnonneg hlowerpull hupperpull hnormalsuper
    hnormaldensity w hw
  have haeval : a (1, w) = (t₀ + R ^ 2, v) := by
    dsimp [a, w, parabolicAffine]
    ext
    · ring
    · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul]
      ring
  have hdivision : g ≤ u (t₀ + R ^ 2, v) / eps := by
    rw [← haeval]
    simpa [div_eq_mul_inv, mul_comm, pullbackScalar_apply] using hpoint
  simpa [mul_comm] using (le_div_iff₀ heps).mp hdivision

end

end HypoellipticAleksandrov.Parabolic
