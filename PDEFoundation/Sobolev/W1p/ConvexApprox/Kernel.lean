module

public import PDEFoundation.Measure.AffineVolume
public import PDEFoundation.Sobolev.W1p.ConvexApprox.Geometry
public import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Convex-domain smoothing kernels

This file defines the normalized smooth kernel and the affine
convex-approximation operator. It also records the exact positive-dilation
Jacobian formulas and the convolution representation used by later smoothness,
weak-derivative, and convergence modules.
-/

@[expose] public section

open scoped Pointwise Convolution

namespace PDE

/-- Cache smooth-bump existence on native vectors for this module and its
transitive importers. -/
private instance instHasContDiffBumpVec (d : ℕ) :
    HasContDiffBump (Vec d) :=
  inferInstance

/-- A nonnegative smooth unit-mass kernel supported in the closed unit ball
for the inherited native-vector norm. -/
structure IsConvexApproxKernel {d : ℕ} (ρ : Vec d → ℝ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) ρ
  compactSupport : HasCompactSupport ρ
  support_subset_closedBall :
    tsupport ρ ⊆ Metric.closedBall (0 : Vec d) 1
  nonneg : ∀ z, 0 ≤ ρ z
  setIntegral_one : ∫ z in tsupport ρ, ρ z = 1

namespace IsConvexApproxKernel

theorem continuous {d : ℕ} {ρ : Vec d → ℝ}
    (hρ : IsConvexApproxKernel ρ) :
    Continuous ρ :=
  hρ.smooth.continuous

end IsConvexApproxKernel

namespace ContDiffBump

theorem isConvexApproxKernel_normed {d : ℕ}
    (φ : ContDiffBump (0 : Vec d)) (hφ : φ.rOut ≤ 1) :
    IsConvexApproxKernel (φ.normed MeasureTheory.volume) := by
  refine
    { smooth := by
        simpa using
          (φ.contDiff_normed (μ := MeasureTheory.volume))
      compactSupport := by
        simpa using
          (φ.hasCompactSupport_normed
            (μ := MeasureTheory.volume))
      support_subset_closedBall := by
        rw [φ.tsupport_normed_eq (μ := MeasureTheory.volume)]
        exact Metric.closedBall_subset_closedBall hφ
      nonneg := by
        intro z
        simpa using
          (φ.nonneg_normed (μ := MeasureTheory.volume) z)
      setIntegral_one := by
        calc
          ∫ z in tsupport (φ.normed MeasureTheory.volume),
              φ.normed MeasureTheory.volume z =
              ∫ z, φ.normed MeasureTheory.volume z := by
            exact
              MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
                (fun z hz =>
                  image_eq_zero_of_notMem_tsupport
                    (f := φ.normed MeasureTheory.volume) hz)
          _ = 1 :=
            φ.integral_normed (μ := MeasureTheory.volume) }

end ContDiffBump

/-- A concrete smooth bump centered at the origin with outer radius `1`. -/
noncomputable def unitContDiffBump {d : ℕ} :
    ContDiffBump (0 : Vec d) :=
  ⟨(1 / 2 : ℝ), 1, by positivity, by norm_num⟩

/-- The normalized kernel associated with `unitContDiffBump`. -/
noncomputable def unitConvexApproxKernel {d : ℕ} :
    Vec d → ℝ :=
  (unitContDiffBump (d := d)).normed MeasureTheory.volume

theorem isConvexApproxKernel_unitConvexApproxKernel {d : ℕ} :
    IsConvexApproxKernel
      (unitConvexApproxKernel (d := d)) := by
  simpa only [unitConvexApproxKernel, unitContDiffBump] using
    (ContDiffBump.isConvexApproxKernel_normed
      (φ := unitContDiffBump (d := d))
      (by norm_num [unitContDiffBump]))

/-- The standard positive scale sequence for convex approximation. -/
noncomputable def unitConvexApproxScale (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

theorem unitConvexApproxScale_nonneg (n : ℕ) :
    0 ≤ unitConvexApproxScale n := by
  dsimp only [unitConvexApproxScale]
  positivity

theorem unitConvexApproxScale_pos (n : ℕ) :
    0 < unitConvexApproxScale n := by
  dsimp only [unitConvexApproxScale]
  positivity

theorem unitConvexApproxScale_le_one (n : ℕ) :
    unitConvexApproxScale n ≤ 1 := by
  dsimp only [unitConvexApproxScale]
  have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have hn : (0 : ℝ) ≤ n := by
      positivity
    linarith
  have hnonneg : 0 ≤ (n : ℝ) + 1 := by
    positivity
  simpa only [one_div] using
    div_le_one_of_le₀ hden hnonneg

theorem tendsto_unitConvexApproxScale_zero :
    Filter.Tendsto unitConvexApproxScale
      Filter.atTop (nhds 0) := by
  simpa only [unitConvexApproxScale] using!
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- The integrand defining convex approximation at a point. -/
def convexApproxIntegrand {d : ℕ}
    (ρ u : Vec d → ℝ) (x0 : Vec d) (r ε : ℝ)
    (x z : Vec d) : ℝ :=
  ρ z * u (convexApproxSample x0 z r ε x)

@[simp]
theorem convexApproxIntegrand_apply {d : ℕ}
    (ρ u : Vec d → ℝ) (x0 : Vec d) (r ε : ℝ)
    (x z : Vec d) :
    convexApproxIntegrand ρ u x0 r ε x z =
      ρ z * u (convexApproxSample x0 z r ε x) :=
  rfl

/-- The convex-domain smoothing operator attached to a kernel `ρ`. -/
noncomputable def convexApproxSmoothing {d : ℕ}
    (ρ u : Vec d → ℝ) (x0 : Vec d) (r ε : ℝ)
    (x : Vec d) : ℝ :=
  ∫ z in tsupport ρ, convexApproxIntegrand ρ u x0 r ε x z

@[simp]
theorem convexApproxSmoothing_apply {d : ℕ}
    (ρ u : Vec d → ℝ) (x0 : Vec d) (r ε : ℝ)
    (x : Vec d) :
    convexApproxSmoothing ρ u x0 r ε x =
      ∫ z in tsupport ρ,
        convexApproxIntegrand ρ u x0 r ε x z :=
  rfl

/-- The concrete convex smoothing sequence using the unit kernel and scale. -/
noncomputable def unitConvexApproxSequence {d : ℕ}
    (u : Vec d → ℝ) (x0 : Vec d) (r : ℝ) (n : ℕ) :
    Vec d → ℝ :=
  fun x =>
    convexApproxSmoothing
      (unitConvexApproxKernel (d := d)) u x0 r
        (unitConvexApproxScale n) x

/-- Rescale a kernel by a positive length `a`, displaying the exact
dimension-`d` Jacobian factor. -/
noncomputable def scaledConvexApproxKernel {d : ℕ}
    (ρ : Vec d → ℝ) (a : ℝ) : Vec d → ℝ :=
  fun y => (a ^ d)⁻¹ * ρ (a⁻¹ • y)

theorem continuous_scaledConvexApproxKernel {d : ℕ}
    {ρ : Vec d → ℝ} (hρ : Continuous ρ) (a : ℝ) :
    Continuous (scaledConvexApproxKernel ρ a) := by
  unfold scaledConvexApproxKernel
  fun_prop

theorem contDiff_scaledConvexApproxKernel {d : ℕ}
    {ρ : Vec d → ℝ} (hρ : IsConvexApproxKernel ρ)
    (a : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (scaledConvexApproxKernel ρ a) := by
  have hscale :
      ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => a⁻¹ • y) := by
    fun_prop
  simpa only [scaledConvexApproxKernel] using!
    contDiff_const.mul (hρ.smooth.comp hscale)

theorem measurable_scaledConvexApproxKernel {d : ℕ}
    {ρ : Vec d → ℝ} (hρ : Continuous ρ) (a : ℝ) :
    Measurable (scaledConvexApproxKernel ρ a) :=
  (continuous_scaledConvexApproxKernel hρ a).measurable

theorem hasCompactSupport_scaledConvexApproxKernel {d : ℕ}
    {ρ : Vec d → ℝ} (hρ : HasCompactSupport ρ)
    {a : ℝ} (ha : 0 < a) :
    HasCompactSupport (scaledConvexApproxKernel ρ a) := by
  have hcomp :
      HasCompactSupport (fun y : Vec d => ρ (a⁻¹ • y)) := by
    simpa only [Function.comp_def] using
      hρ.comp_smul (inv_ne_zero ha.ne')
  simpa only [scaledConvexApproxKernel] using!
    (hcomp.mul_left :
      HasCompactSupport
        (fun y : Vec d => (a ^ d)⁻¹ * ρ (a⁻¹ • y)))

theorem integrable_scaledConvexApproxKernel {d : ℕ}
    {ρ : Vec d → ℝ} (hρ : IsConvexApproxKernel ρ)
    {a : ℝ} (ha : 0 < a) :
    MeasureTheory.Integrable
      (scaledConvexApproxKernel ρ a) := by
  exact
    (continuous_scaledConvexApproxKernel hρ.continuous a).integrable_of_hasCompactSupport
      (hasCompactSupport_scaledConvexApproxKernel
        hρ.compactSupport ha)

theorem scaledConvexApproxKernel_nonneg {d : ℕ}
    {ρ : Vec d → ℝ} (hρ : IsConvexApproxKernel ρ)
    {a : ℝ} (_ha : 0 < a) (y : Vec d) :
    0 ≤ scaledConvexApproxKernel ρ a y := by
  have hpowNonneg : 0 ≤ (a ^ d)⁻¹ := by
    positivity
  exact mul_nonneg hpowNonneg (hρ.nonneg _)

theorem integral_scaledConvexApproxKernel {d : ℕ}
    {ρ : Vec d → ℝ} (hρ : IsConvexApproxKernel ρ)
    {a : ℝ} (ha : 0 < a) :
    ∫ y, scaledConvexApproxKernel ρ a y = 1 := by
  have haNe : a ≠ 0 :=
    ha.ne'
  have hzero :
      ∀ y, y ∉ a • tsupport ρ →
        scaledConvexApproxKernel ρ a y = 0 := by
    intro y hy
    have hy' : a⁻¹ • y ∉ tsupport ρ := by
      intro hmem
      apply hy
      exact Set.mem_smul_set.mpr
        ⟨a⁻¹ • y, hmem, by
          rw [smul_smul, mul_inv_cancel₀ haNe, one_smul]⟩
    simp only [scaledConvexApproxKernel,
      image_eq_zero_of_notMem_tsupport hy', mul_zero]
  rw [←
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      hzero]
  calc
    ∫ y in a • tsupport ρ,
        scaledConvexApproxKernel ρ a y
        ∂MeasureTheory.volume =
        (a ^ d)⁻¹ *
          ∫ y in a • tsupport ρ, ρ (a⁻¹ • y)
            ∂MeasureTheory.volume := by
      simp only [scaledConvexApproxKernel,
        MeasureTheory.integral_const_mul]
    _ = ∫ z in tsupport ρ, ρ z
          ∂MeasureTheory.volume := by
      simpa [smul_eq_mul, smul_smul,
        inv_mul_cancel₀ haNe, mul_inv_cancel₀ haNe] using
        (MeasureTheory.Measure.setIntegral_comp_smul_of_pos
          (μ := MeasureTheory.volume)
          (f := fun y : Vec d => ρ (a⁻¹ • y))
          (s := tsupport ρ) ha).symm
    _ = 1 :=
      hρ.setIntegral_one

theorem convexApproxImage_subset_translateSet_smul {d : ℕ}
    {U : Set (Vec d)} (x0 z : Vec d) (r ε : ℝ) :
    convexApproxSample x0 z r ε '' U ⊆
      translateSet (ε • (x0 - r • z)) ((1 - ε) • U) := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  refine ⟨(1 - ε) • x, Set.smul_mem_smul_set hx, ?_⟩
  simp [convexApproxSample]

theorem translateSet_smul_subset_of_convexApproxSample_mapsTo
    {d : ℕ} {U : Set (Vec d)}
    {x0 z : Vec d} {r ε : ℝ}
    (hmap :
      Set.MapsTo (convexApproxSample x0 z r ε) U U) :
    translateSet (ε • (x0 - r • z)) ((1 - ε) • U) ⊆
      U := by
  intro y hy
  rcases hy with ⟨w, hw, hyw⟩
  rcases Set.mem_smul_set.mp hw with ⟨x, hx, rfl⟩
  have hx' : convexApproxSample x0 z r ε x ∈ U :=
    hmap hx
  rw [hyw]
  simpa only [convexApproxSample] using hx'

theorem setIntegral_comp_smul_add_of_pos
    {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a : ℝ} (ha : 0 < a) (b : Vec d) (U : Set (Vec d))
    (f : Vec d → E) :
    ∫ x in U, f (a • x + b) ∂MeasureTheory.volume =
      (a ^ d)⁻¹ •
        ∫ y in translateSet b (a • U), f y
          ∂MeasureTheory.volume := by
  calc
    ∫ x in U, f (a • x + b) ∂MeasureTheory.volume =
        (a ^ d)⁻¹ •
          ∫ z in a • U, f (z + b)
            ∂MeasureTheory.volume := by
      simpa [Vec] using
        (MeasureTheory.Measure.setIntegral_comp_smul_of_pos
          (μ := MeasureTheory.volume)
          (f := fun z : Vec d => f (z + b))
          (s := U) ha)
    _ = (a ^ d)⁻¹ •
          ∫ y in translateSet b (a • U), f y
            ∂MeasureTheory.volume := by
      rw [setIntegral_comp_addRight_translateSet
        (d := d) (E := E) b (a • U) f]

theorem setIntegral_comp_inv_smul_sub_of_pos
    {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a : ℝ} (ha : 0 < a) (b : Vec d) (U : Set (Vec d))
    (f : Vec d → E) :
    (a ^ d)⁻¹ •
        ∫ y in translateSet b (a • U),
          f (a⁻¹ • (y - b)) ∂MeasureTheory.volume =
      ∫ x in U, f x ∂MeasureTheory.volume := by
  have haNe : a ≠ 0 :=
    ha.ne'
  calc
    (a ^ d)⁻¹ •
        ∫ y in translateSet b (a • U),
          f (a⁻¹ • (y - b)) ∂MeasureTheory.volume =
        (a ^ d)⁻¹ •
          ∫ z in a • U, f (a⁻¹ • z)
            ∂MeasureTheory.volume := by
      congr 1
      exact
        setIntegral_comp_subRight_translateSet
          (d := d) (E := E) b (a • U)
            (fun z => f (a⁻¹ • z))
    _ = ∫ x in U, f (a⁻¹ • (a • x))
          ∂MeasureTheory.volume := by
      simpa [Vec] using
        (MeasureTheory.Measure.setIntegral_comp_smul_of_pos
          (μ := MeasureTheory.volume)
          (f := fun z : Vec d => f (a⁻¹ • z))
          (s := U) ha).symm
    _ = ∫ x in U, f x ∂MeasureTheory.volume := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      simp only [smul_smul, inv_mul_cancel₀ haNe, one_smul]

theorem convolution_scaledConvexApproxKernel_indicator_eq_setIntegral
    {d : ℕ} {ρ u : Vec d → ℝ} {U : Set (Vec d)}
    {x0 x : Vec d} {r ε : ℝ}
    (hr : 0 < r) (hε0 : 0 < ε) :
    (scaledConvexApproxKernel ρ (ε * r) ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, MeasureTheory.volume]
      Set.indicator U u) ((1 - ε) • x + ε • x0) =
      ∫ z in tsupport ρ,
        ρ z * Set.indicator U u
          (((1 - ε) • x + ε • x0) - (ε * r) • z)
          ∂MeasureTheory.volume := by
  let a : ℝ :=
    ε * r
  let A : Vec d :=
    (1 - ε) • x + ε • x0
  have ha : 0 < a := by
    dsimp only [a]
    positivity
  have haNe : a ≠ 0 :=
    ha.ne'
  change
    ∫ t, scaledConvexApproxKernel ρ a t *
        Set.indicator U u (A - t) ∂MeasureTheory.volume =
      ∫ z in tsupport ρ,
        ρ z * Set.indicator U u (A - a • z)
          ∂MeasureTheory.volume
  simp only [scaledConvexApproxKernel]
  have hzero :
      ∀ y, y ∉ a • tsupport ρ →
        ((a ^ d)⁻¹ * ρ (a⁻¹ • y)) *
          Set.indicator U u (A - y) = 0 := by
    intro y hy
    have hy' : a⁻¹ • y ∉ tsupport ρ := by
      intro hmem
      apply hy
      exact Set.mem_smul_set.mpr
        ⟨a⁻¹ • y, hmem, by
          rw [smul_smul, mul_inv_cancel₀ haNe, one_smul]⟩
    simp only [image_eq_zero_of_notMem_tsupport hy',
      zero_mul, mul_zero]
  rw [←
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      hzero]
  have hmul :
      (fun y : Vec d =>
        ((a ^ d)⁻¹ * ρ (a⁻¹ • y)) *
          Set.indicator U u (A - y)) =
        fun y : Vec d =>
          (a ^ d)⁻¹ *
            (ρ (a⁻¹ • y) * Set.indicator U u (A - y)) := by
    funext y
    ring
  calc
    ∫ y in a • tsupport ρ,
        ((a ^ d)⁻¹ * ρ (a⁻¹ • y)) *
          Set.indicator U u (A - y) ∂MeasureTheory.volume =
        (a ^ d)⁻¹ *
          ∫ y in a • tsupport ρ,
            ρ (a⁻¹ • y) * Set.indicator U u (A - y)
              ∂MeasureTheory.volume := by
      rw [hmul, MeasureTheory.integral_const_mul]
    _ = ∫ z in tsupport ρ,
          ρ z * Set.indicator U u (A - a • z)
            ∂MeasureTheory.volume := by
      simpa [smul_eq_mul, mul_assoc, mul_left_comm,
        mul_comm, sub_eq_add_neg, smul_smul,
        inv_mul_cancel₀ haNe, mul_inv_cancel₀ haNe,
        zero_smul, add_zero] using
        (setIntegral_comp_smul_add_of_pos
          (d := d) (E := ℝ) (a := a) ha (b := 0)
          (U := tsupport ρ)
          (f := fun y : Vec d =>
            ρ (a⁻¹ • y) * Set.indicator U u (A - y))).symm

theorem
    convexApproxSmoothing_eq_convolution_scaledConvexApproxKernel_indicator
    {d : ℕ} {ρ u : Vec d → ℝ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    (hρ : IsConvexApproxKernel ρ)
    {x0 x : Vec d} {r ε : ℝ} (hx : x ∈ U)
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) (hε0 : 0 < ε) (hε1 : ε < 1) :
    convexApproxSmoothing ρ u x0 r ε x =
      (scaledConvexApproxKernel ρ (ε * r) ⋆[
          ContinuousLinearMap.lsmul ℝ ℝ,
          MeasureTheory.volume]
        Set.indicator U u) ((1 - ε) • x + ε • x0) := by
  rw [
    convolution_scaledConvexApproxKernel_indicator_eq_setIntegral
      hr hε0,
    convexApproxSmoothing]
  have htsupportMeas : MeasurableSet (tsupport ρ) :=
    (isClosed_tsupport (f := ρ)).measurableSet
  apply MeasureTheory.integral_congr_ae
  change
    ∀ᵐ z ∂MeasureTheory.volume.restrict (tsupport ρ),
      convexApproxIntegrand ρ u x0 r ε x z =
        ρ z * Set.indicator U u
          (((1 - ε) • x + ε • x0) - (ε * r) • z)
  rw [MeasureTheory.ae_restrict_iff' htsupportMeas]
  filter_upwards with z hz
  have hzNorm : ‖z‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      hρ.support_subset_closedBall hz
  have hsampleMem :
      convexApproxSample x0 z r ε x ∈ U :=
    convexApproxSample_mem_of_isOpenBoundedConvexDomain
      hU hx hball hr.le hzNorm hε0.le (le_of_lt hε1)
  have hsampleEq :
      ((1 - ε) • x + ε • x0) - (ε * r) • z =
        convexApproxSample x0 z r ε x := by
    simp [convexApproxSample, sub_eq_add_neg, smul_smul,
      add_assoc, add_left_comm, add_comm]
  have hind :
      Set.indicator U u (convexApproxSample x0 z r ε x) =
        u (convexApproxSample x0 z r ε x) := by
    rw [Set.indicator_of_mem hsampleMem]
  calc
    convexApproxIntegrand ρ u x0 r ε x z =
        ρ z * u (convexApproxSample x0 z r ε x) :=
      convexApproxIntegrand_apply ρ u x0 r ε x z
    _ = ρ z *
        Set.indicator U u
          (convexApproxSample x0 z r ε x) := by
      rw [hind]
    _ = ρ z *
        Set.indicator U u
          (((1 - ε) • x + ε • x0) -
            (ε * r) • z) := by
      rw [hsampleEq]

end PDE
