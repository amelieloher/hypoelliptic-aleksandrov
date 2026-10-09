module

public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import HypoellipticAleksandrov.Parabolic.HarnackGeometry
public import HypoellipticAleksandrov.Parabolic.LocalClassical

/-!
# Parabolic affine scaling

This file records the exact translation and parabolic-dilation identities for
the forward time--velocity operator.  The affine map itself is defined in
`HarnackGeometry`; this module supplies its differential and the induced local
classical pullback API.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter Set
open scoped MatrixOrder Topology

/-- The derivative of parabolic affine scaling. -/
def parabolicLinear {d : ℕ} (r : ℝ) :
    TimeVelocity d →L[ℝ] TimeVelocity d :=
  ((r ^ 2) • ContinuousLinearMap.fst ℝ ℝ (PDE.Vec d)).prod
    (r • ContinuousLinearMap.snd ℝ ℝ (PDE.Vec d))

/-- Evaluation of the linear part of parabolic affine scaling. -/
@[simp] theorem parabolicLinear_apply {d : ℕ} (r : ℝ) (z : TimeVelocity d) :
    parabolicLinear r z = (r ^ 2 * z.1, r • z.2) :=
  rfl

/-- The affine parabolic map has its constant linear part as Fréchet derivative. -/
theorem hasFDerivAt_parabolicAffine {d : ℕ} (t₀ : ℝ) (v₀ : PDE.Vec d) (r : ℝ)
    (z : TimeVelocity d) :
    HasFDerivAt (parabolicAffine t₀ v₀ r) (parabolicLinear r) z := by
  change HasFDerivAt (fun z : TimeVelocity d ↦
    (t₀ + r ^ 2 * z.1, v₀ + r • z.2)) (parabolicLinear r) z
  convert ((hasFDerivAt_const t₀ z).add
    ((hasFDerivAt_const (r ^ 2) z).mul hasFDerivAt_fst)).prodMk
      ((hasFDerivAt_const v₀ z).add
        ((hasFDerivAt_const r z).smul
          (hasFDerivAt_snd (𝕜 := ℝ) (p := z)))) using 1
  ext <;> simp [parabolicLinear]

/-- Parabolic affine scaling is globally smooth. -/
theorem contDiff_parabolicAffine {d : ℕ} (t₀ : ℝ) (v₀ : PDE.Vec d) (r : ℝ) :
    ContDiff ℝ 2 (parabolicAffine t₀ v₀ r) := by
  change ContDiff ℝ 2 (fun z : TimeVelocity d ↦
    (t₀ + r ^ 2 * z.1, v₀ + r • z.2))
  fun_prop

/-- Parabolic affine scaling is smooth at every order. -/
theorem contDiff_infty_parabolicAffine {d : ℕ} (t₀ : ℝ) (v₀ : PDE.Vec d)
    (r : ℝ) : ContDiff ℝ (⊤ : WithTop ℕ∞) (parabolicAffine t₀ v₀ r) := by
  change ContDiff ℝ (⊤ : WithTop ℕ∞) (fun z : TimeVelocity d ↦
    (t₀ + r ^ 2 * z.1, v₀ + r • z.2))
  fun_prop

/-- Pulls a scalar function back by parabolic affine scaling. -/
def pullbackScalar {d : ℕ} (q : TimeVelocity d → ℝ)
    (t₀ : ℝ) (v₀ : PDE.Vec d) (r : ℝ) : TimeVelocity d → ℝ :=
  q ∘ parabolicAffine t₀ v₀ r

/-- Pulls a coefficient field back by parabolic affine scaling. -/
def pullbackCoefficient {d : ℕ} (B : CoefficientField d)
    (t₀ : ℝ) (v₀ : PDE.Vec d) (r : ℝ) : CoefficientField d :=
  fun t v ↦ B (t₀ + r ^ 2 * t) (v₀ + r • v)

/-- Evaluation of a scalar pullback. -/
@[simp] theorem pullbackScalar_apply {d : ℕ} (q : TimeVelocity d → ℝ)
    (t₀ : ℝ) (v₀ : PDE.Vec d) (r : ℝ) (z : TimeVelocity d) :
    pullbackScalar q t₀ v₀ r z = q (parabolicAffine t₀ v₀ r z) :=
  rfl

/-- Evaluation of a coefficient pullback. -/
@[simp] theorem coefficientAt_pullbackCoefficient {d : ℕ} (B : CoefficientField d)
    (t₀ : ℝ) (v₀ : PDE.Vec d) (r : ℝ) (z : TimeVelocity d) :
    coefficientAt (pullbackCoefficient B t₀ v₀ r) z =
      coefficientAt B (parabolicAffine t₀ v₀ r z) :=
  rfl

/-- Local coefficient continuity is preserved by parabolic affine pullback. -/
theorem IsContinuousCoefficientOn.pullback {d : ℕ} {B : CoefficientField d}
    {U V : Set (TimeVelocity d)} {t₀ r : ℝ} {v₀ : PDE.Vec d}
    (hB : IsContinuousCoefficientOn B U)
    (hmap : MapsTo (parabolicAffine t₀ v₀ r) V U) :
    IsContinuousCoefficientOn (pullbackCoefficient B t₀ v₀ r) V := by
  exact hB.comp (contDiff_parabolicAffine t₀ v₀ r).continuous.continuousOn hmap

/-- Local `C²` regularity is preserved by parabolic affine pullback. -/
theorem ContDiffOn.pullbackScalar {d : ℕ} {q : TimeVelocity d → ℝ}
    {U V : Set (TimeVelocity d)} {t₀ r : ℝ} {v₀ : PDE.Vec d}
    (hq : ContDiffOn ℝ 2 q U) (hmap : MapsTo (parabolicAffine t₀ v₀ r) V U) :
    ContDiffOn ℝ 2 (pullbackScalar q t₀ v₀ r) V := by
  exact hq.comp (contDiff_parabolicAffine t₀ v₀ r).contDiffOn hmap

/-- Local nonnegativity is preserved by parabolic affine pullback. -/
theorem IsNonnegativeOn.pullbackScalar {d : ℕ} {q : TimeVelocity d → ℝ}
    {U V : Set (TimeVelocity d)} {t₀ r : ℝ} {v₀ : PDE.Vec d}
    (hq : IsNonnegativeOn q U) (hmap : MapsTo (parabolicAffine t₀ v₀ r) V U) :
    IsNonnegativeOn (pullbackScalar q t₀ v₀ r) V :=
  fun z hz => by
    simpa only [pullbackScalar_apply] using hq (parabolicAffine t₀ v₀ r z) (hmap hz)

/-- Local lower ellipticity is preserved by parabolic affine pullback. -/
theorem HasLowerEllipticityOn.pullback {d : ℕ} {B : CoefficientField d}
    {U V : Set (TimeVelocity d)} {lam t₀ r : ℝ} {v₀ : PDE.Vec d}
    (hB : HasLowerEllipticityOn lam B U)
    (hmap : MapsTo (parabolicAffine t₀ v₀ r) V U) :
    HasLowerEllipticityOn lam (pullbackCoefficient B t₀ v₀ r) V :=
  fun z hz => by
    simpa only [coefficientAt_pullbackCoefficient] using
      hB (parabolicAffine t₀ v₀ r z) (hmap hz)

/-- Local upper ellipticity is preserved by parabolic affine pullback. -/
theorem HasUpperEllipticityOn.pullback {d : ℕ} {B : CoefficientField d}
    {U V : Set (TimeVelocity d)} {Lam t₀ r : ℝ} {v₀ : PDE.Vec d}
    (hB : HasUpperEllipticityOn Lam B U)
    (hmap : MapsTo (parabolicAffine t₀ v₀ r) V U) :
    HasUpperEllipticityOn Lam (pullbackCoefficient B t₀ v₀ r) V :=
  fun z hz => by
    simpa only [coefficientAt_pullbackCoefficient] using
      hB (parabolicAffine t₀ v₀ r z) (hmap hz)

private theorem fderiv_pullbackScalar_eventually {d : ℕ} {q : TimeVelocity d → ℝ}
    {z : TimeVelocity d} {t₀ r : ℝ} {v₀ : PDE.Vec d}
    (hq : ContDiffAt ℝ 2 q (parabolicAffine t₀ v₀ r z)) :
    fderiv ℝ (pullbackScalar q t₀ v₀ r) =ᶠ[𝓝 z]
      fun y ↦ (fderiv ℝ q (parabolicAffine t₀ v₀ r y)).comp
        (parabolicLinear (d := d) r) := by
  have hfinite : (2 : WithTop ℕ∞) ≠ ((↑(⊤ : ℕ∞)) : WithTop ℕ∞) := by
    norm_cast
  have hlocal := hq.eventually hfinite
  filter_upwards [(hasFDerivAt_parabolicAffine t₀ v₀ r z).continuousAt.tendsto.eventually
    hlocal] with y hy
  change fderiv ℝ (q ∘ parabolicAffine t₀ v₀ r) y = _
  rw [fderiv_comp y (hy.differentiableAt (by norm_num))
    (hasFDerivAt_parabolicAffine t₀ v₀ r y).differentiableAt,
    (hasFDerivAt_parabolicAffine t₀ v₀ r y).fderiv]

/-- The velocity Hessian of a scalar pullback has the exact parabolic scale. -/
theorem velocityHessian_pullbackScalar {d : ℕ} {q : TimeVelocity d → ℝ}
    {z : TimeVelocity d} {t₀ r : ℝ} {v₀ : PDE.Vec d}
    (hq : ContDiffAt ℝ 2 q (parabolicAffine t₀ v₀ r z)) :
    velocityHessian (pullbackScalar q t₀ v₀ r) z =
      r ^ 2 • velocityHessian q (parabolicAffine t₀ v₀ r z) := by
  let a := parabolicAffine t₀ v₀ r
  let L := parabolicLinear (d := d) r
  let c : TimeVelocity d → TimeVelocity d →L[ℝ] ℝ := fun y ↦ fderiv ℝ q (a y)
  have hc : HasFDerivAt c ((fderiv ℝ (fderiv ℝ q) (a z)).comp L) z := by
    exact ((hq.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt.comp z (hasFDerivAt_parabolicAffine t₀ v₀ r z)
  have hL : HasFDerivAt (fun _ : TimeVelocity d ↦ L)
      (0 : TimeVelocity d →L[ℝ] (TimeVelocity d →L[ℝ] TimeVelocity d)) z :=
    hasFDerivAt_const L z
  have hF := hc.clm_comp hL
  have heq := fderiv_pullbackScalar_eventually hq
  have hfp := hF.congr_of_eventuallyEq heq
  ext i j
  unfold velocityHessian
  rw [hfp.fderiv]
  simp [a, L, c, parabolicLinear, parabolicAffine, ContinuousLinearMap.compL]
  let H := fderiv ℝ (fderiv ℝ q) (t₀ + r ^ 2 * z.1, v₀ + r • z.2)
  change H ((0 : ℝ), r • (Pi.single i (1 : ℝ) : PDE.Vec d))
      ((0 : ℝ), r • (Pi.single j (1 : ℝ) : PDE.Vec d)) =
    r ^ 2 * H ((0 : ℝ), (Pi.single i (1 : ℝ) : PDE.Vec d))
      ((0 : ℝ), (Pi.single j (1 : ℝ) : PDE.Vec d))
  have hi : ((0 : ℝ), r • (Pi.single i (1 : ℝ) : PDE.Vec d)) =
      r • ((0 : ℝ), (Pi.single i (1 : ℝ) : PDE.Vec d)) := by
    ext <;> simp
  have hj : ((0 : ℝ), r • (Pi.single j (1 : ℝ) : PDE.Vec d)) =
      r • ((0 : ℝ), (Pi.single j (1 : ℝ) : PDE.Vec d)) := by
    ext <;> simp
  rw [hi, H.map_smul]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hj, (H ((0 : ℝ), (Pi.single i (1 : ℝ) : PDE.Vec d))).map_smul]
  simp only [smul_eq_mul]
  ring

/-- The time derivative of a scalar pullback has the exact parabolic scale. -/
theorem timeDerivative_pullbackScalar {d : ℕ} {q : TimeVelocity d → ℝ}
    {z : TimeVelocity d} {t₀ r : ℝ} {v₀ : PDE.Vec d}
    (hq : ContDiffAt ℝ 2 q (parabolicAffine t₀ v₀ r z)) :
    timeDerivative (pullbackScalar q t₀ v₀ r) z =
      r ^ 2 * timeDerivative q (parabolicAffine t₀ v₀ r z) := by
  unfold timeDerivative
  rw [show fderiv ℝ (pullbackScalar q t₀ v₀ r) z =
      (fderiv ℝ q (parabolicAffine t₀ v₀ r z)).comp (parabolicLinear (d := d) r) by
    exact (hq.differentiableAt (by norm_num)).hasFDerivAt.comp z
      (hasFDerivAt_parabolicAffine t₀ v₀ r z) |>.fderiv]
  simp only [ContinuousLinearMap.comp_apply, parabolicLinear_apply]
  simpa [smul_eq_mul] using
    (fderiv ℝ q (parabolicAffine t₀ v₀ r z)).map_smul (r ^ 2)
      ((1 : ℝ), (0 : PDE.Vec d))

/-- Matrix contraction with a pullback Hessian has the exact parabolic scale. -/
theorem matrixContraction_pullbackScalar {d : ℕ} {B : CoefficientField d}
    {q : TimeVelocity d → ℝ} {z : TimeVelocity d} {t₀ r : ℝ} {v₀ : PDE.Vec d}
    (hq : ContDiffAt ℝ 2 q (parabolicAffine t₀ v₀ r z)) :
    matrixContraction (coefficientAt (pullbackCoefficient B t₀ v₀ r) z)
      (velocityHessian (pullbackScalar q t₀ v₀ r) z) =
      r ^ 2 * matrixContraction (coefficientAt B (parabolicAffine t₀ v₀ r z))
        (velocityHessian q (parabolicAffine t₀ v₀ r z)) := by
  rw [coefficientAt_pullbackCoefficient, velocityHessian_pullbackScalar hq,
    HypoellipticAleksandrov.matrixContraction_smul_right]

/-- The forward parabolic operator is covariant under every parabolic affine map. -/
theorem parabolicOperator_pullbackScalar {d : ℕ} {B : CoefficientField d}
    {q : TimeVelocity d → ℝ} {z : TimeVelocity d} {t₀ r : ℝ} {v₀ : PDE.Vec d}
    (hq : ContDiffAt ℝ 2 q (parabolicAffine t₀ v₀ r z)) :
    parabolicOperator (pullbackCoefficient B t₀ v₀ r) (pullbackScalar q t₀ v₀ r) z =
      r ^ 2 * parabolicOperator B q (parabolicAffine t₀ v₀ r z) := by
  rw [parabolicOperator_apply, parabolicOperator_apply,
    timeDerivative_pullbackScalar hq, matrixContraction_pullbackScalar hq]
  ring

/-- A homogeneous local solution pulls back to a homogeneous local solution. -/
theorem IsParabolicSolutionOn.pullback {d : ℕ} {B : CoefficientField d}
    {q : TimeVelocity d → ℝ} {U V : Set (TimeVelocity d)} {t₀ r : ℝ}
    {v₀ : PDE.Vec d} (hU : IsOpen U) (hq : ContDiffOn ℝ 2 q U)
    (h : IsParabolicSolutionOn B q U)
    (hmap : MapsTo (parabolicAffine t₀ v₀ r) V U) :
    IsParabolicSolutionOn (pullbackCoefficient B t₀ v₀ r) (pullbackScalar q t₀ v₀ r) V := by
  intro z hz
  rw [parabolicOperator_pullbackScalar
    (contDiffAt_of_contDiffOn_of_isOpen hU hq (hmap hz))]
  rw [h (parabolicAffine t₀ v₀ r z) (hmap hz), mul_zero]

/-- A local subsolution pulls back with its source multiplied by the square scale. -/
theorem IsParabolicSubsolutionOn.pullback {d : ℕ} {B : CoefficientField d}
    {f q : TimeVelocity d → ℝ} {U V : Set (TimeVelocity d)} {t₀ r : ℝ}
    {v₀ : PDE.Vec d} (hU : IsOpen U) (hq : ContDiffOn ℝ 2 q U)
    (h : IsParabolicSubsolutionOn B f q U)
    (hmap : MapsTo (parabolicAffine t₀ v₀ r) V U) :
    IsParabolicSubsolutionOn (pullbackCoefficient B t₀ v₀ r)
      (fun z ↦ r ^ 2 * f (parabolicAffine t₀ v₀ r z))
      (pullbackScalar q t₀ v₀ r) V := by
  intro z hz
  rw [parabolicOperator_pullbackScalar
    (contDiffAt_of_contDiffOn_of_isOpen hU hq (hmap hz))]
  exact mul_le_mul_of_nonneg_left (h (parabolicAffine t₀ v₀ r z) (hmap hz)) (sq_nonneg r)

/-- A local supersolution pulls back with its source multiplied by the square scale. -/
theorem IsParabolicSupersolutionOn.pullback {d : ℕ} {B : CoefficientField d}
    {f q : TimeVelocity d → ℝ} {U V : Set (TimeVelocity d)} {t₀ r : ℝ}
    {v₀ : PDE.Vec d} (hU : IsOpen U) (hq : ContDiffOn ℝ 2 q U)
    (h : IsParabolicSupersolutionOn B f q U)
    (hmap : MapsTo (parabolicAffine t₀ v₀ r) V U) :
    IsParabolicSupersolutionOn (pullbackCoefficient B t₀ v₀ r)
      (fun z ↦ r ^ 2 * f (parabolicAffine t₀ v₀ r z))
      (pullbackScalar q t₀ v₀ r) V := by
  intro z hz
  rw [parabolicOperator_pullbackScalar
    (contDiffAt_of_contDiffOn_of_isOpen hU hq (hmap hz))]
  exact mul_le_mul_of_nonneg_left (h (parabolicAffine t₀ v₀ r z) (hmap hz)) (sq_nonneg r)

/-- The full transparent local classical surface is preserved by affine pullback. -/
theorem IsLocalClassicalSolutionOn.pullback {d : ℕ} {B : CoefficientField d}
    {q : TimeVelocity d → ℝ} {U V : Set (TimeVelocity d)} {lam Lam t₀ r : ℝ}
    {v₀ : PDE.Vec d} (hU : IsOpen U)
    (h : IsLocalClassicalSolutionOn d B q U lam Lam)
    (hmap : MapsTo (parabolicAffine t₀ v₀ r) V U) :
    IsLocalClassicalSolutionOn d (pullbackCoefficient B t₀ v₀ r)
      (pullbackScalar q t₀ v₀ r) V lam Lam := by
  refine ⟨IsContinuousCoefficientOn.pullback h.continuousCoefficientOn hmap,
    ContDiffOn.pullbackScalar h.contDiffOn hmap,
    IsNonnegativeOn.pullbackScalar h.nonnegativeOn hmap,
    HasLowerEllipticityOn.pullback h.lowerEllipticityOn hmap,
    HasUpperEllipticityOn.pullback h.upperEllipticityOn hmap,
    IsParabolicSolutionOn.pullback hU h.contDiffOn h.solutionOn hmap⟩

/-- A coefficient field expressed in the absolute-time age variable. -/
def ageCoefficient {d : ℕ} (A : CoefficientField d) (T : ℝ) : CoefficientField d :=
  fun theta v ↦ A (T - theta) v

/-- Evaluation of the absolute-time age coefficient. -/
@[simp] theorem coefficientAt_ageCoefficient {d : ℕ} (A : CoefficientField d)
    (T : ℝ) (z : TimeVelocity d) :
    coefficientAt (ageCoefficient A T) z = A (T - z.1) z.2 :=
  rfl

/-- The normalized age-coefficient pullback exposes its absolute-time evaluation formula. -/
@[simp] theorem pullbackCoefficient_ageCoefficient_zero {d : ℕ} (A : CoefficientField d)
    (T r : ℝ) (vStar : PDE.Vec d) (zHat : TimeVelocity d) :
    coefficientAt (pullbackCoefficient (ageCoefficient A T) 0 vStar r) zHat =
      A (T - r ^ 2 * zHat.1) (vStar + r • zHat.2) := by
  simp only [coefficientAt_pullbackCoefficient, coefficientAt_ageCoefficient,
    parabolicAffine, zero_add]

/-- The corresponding scalar pullback evaluates at forward age, without time reflection. -/
@[simp] theorem pullbackScalar_zero_apply {d : ℕ} (q : TimeVelocity d → ℝ)
    (r : ℝ) (vStar : PDE.Vec d) (zHat : TimeVelocity d) :
    pullbackScalar q 0 vStar r zHat = q (r ^ 2 * zHat.1, vStar + r • zHat.2) := by
  simp [pullbackScalar, parabolicAffine]

/-- Local continuity of an age coefficient transports through zero-base parabolic scaling. -/
theorem IsContinuousCoefficientOn.age_pullback {d : ℕ} {A : CoefficientField d}
    {T r : ℝ} {vStar : PDE.Vec d} {U V : Set (TimeVelocity d)}
    (hA : IsContinuousCoefficientOn (ageCoefficient A T) U)
    (hmap : MapsTo (parabolicAffine 0 vStar r) V U) :
    IsContinuousCoefficientOn (pullbackCoefficient (ageCoefficient A T) 0 vStar r) V :=
  hA.pullback hmap

/-- Local lower ellipticity of an age coefficient transports through zero-base scaling. -/
theorem HasLowerEllipticityOn.age_pullback {d : ℕ} {A : CoefficientField d}
    {lam T r : ℝ} {vStar : PDE.Vec d} {U V : Set (TimeVelocity d)}
    (hA : HasLowerEllipticityOn lam (ageCoefficient A T) U)
    (hmap : MapsTo (parabolicAffine 0 vStar r) V U) :
    HasLowerEllipticityOn lam (pullbackCoefficient (ageCoefficient A T) 0 vStar r) V :=
  hA.pullback hmap

/-- Local upper ellipticity of an age coefficient transports through zero-base scaling. -/
theorem HasUpperEllipticityOn.age_pullback {d : ℕ} {A : CoefficientField d}
    {Lam T r : ℝ} {vStar : PDE.Vec d} {U V : Set (TimeVelocity d)}
    (hA : HasUpperEllipticityOn Lam (ageCoefficient A T) U)
    (hmap : MapsTo (parabolicAffine 0 vStar r) V U) :
    HasUpperEllipticityOn Lam (pullbackCoefficient (ageCoefficient A T) 0 vStar r) V :=
  hA.pullback hmap

end HypoellipticAleksandrov.Parabolic
