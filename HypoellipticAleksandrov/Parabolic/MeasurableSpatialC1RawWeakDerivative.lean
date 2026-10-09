module

public import HypoellipticAleksandrov.Parabolic.SpatialSliceFDerivMeasurability
public import HypoellipticAleksandrov.Parabolic.LocalCompactSupportIntegrationByParts
public import HypoellipticAleksandrov.Parabolic.WeakDerivatives
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Measurable-time spatial weak derivatives

This module identifies the literal spatial derivative of a jointly measurable,
fixed-time spatial-`C¹` function as its raw weak velocity derivative.  The proof
uses spatial integration by parts on each time slice and Fubini to recover the
time--velocity distributional identity, without assuming time regularity.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter Function MeasureTheory Set Topology
open scoped ENNReal Topology

private theorem isClosedEmbedding_timeSlice {d : ℕ} (r : ℝ) :
    IsClosedEmbedding (Prod.mk r : PDE.Vec d → TimeVelocity d) := by
  refine IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_const.prodMk continuous_id) (fun x y h => by simpa using congrArg Prod.snd h) ?_
  intro s hs
  have himage : Prod.mk r '' s = ({r} : Set ℝ) ×ˢ s := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨Set.mem_singleton r, hy⟩
    · rintro ⟨hr, hy⟩
      rw [Set.mem_singleton_iff] at hr
      subst hr
      exact ⟨z.2, hy, rfl⟩
  rw [himage]
  exact isClosed_singleton.prod hs

private theorem hasCompactSupport_timeSlice {d : ℕ} (r : ℝ)
    (φ : TimeVelocity d → ℝ) (hφ : HasCompactSupport φ) :
    HasCompactSupport (fun y : PDE.Vec d => φ (r, y)) := by
  refine HasCompactSupport.of_support_subset_isCompact
    ((isClosedEmbedding_timeSlice (d := d) r).isCompact_preimage hφ) ?_
  intro y hy
  exact subset_tsupport φ hy

private theorem tsupport_timeSlice_subset {d : ℕ} {I : Set ℝ}
    {O : Set (PDE.Vec d)} (r : ℝ) (φ : TimeVelocity d → ℝ)
    (hφ : tsupport φ ⊆ I ×ˢ O) :
    tsupport (fun y : PDE.Vec d => φ (r, y)) ⊆ O := by
  intro y hy
  have hclosed : IsClosed ((Prod.mk r : PDE.Vec d → TimeVelocity d) ⁻¹' tsupport φ) :=
    (isClosed_tsupport φ).preimage (continuous_const.prodMk continuous_id)
  have hsupport : Function.support (fun y : PDE.Vec d => φ (r, y)) ⊆
      (Prod.mk r : PDE.Vec d → TimeVelocity d) ⁻¹' tsupport φ := by
    intro x hx
    exact subset_tsupport φ hx
  have hmem : y ∈ (Prod.mk r : PDE.Vec d → TimeVelocity d) ⁻¹' tsupport φ := by
    exact closure_minimal hsupport hclosed hy
  exact (hφ hmem).2

private theorem spatialPartial_timeSlice_eq_velocityGradient {d : ℕ}
    (r : ℝ) (φ : TimeVelocity d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (y : PDE.Vec d) (k : Fin d) :
    spatialPartial k (fun x => φ (r, x)) y = velocityGradient φ (r, y) k := by
  have hs := (hφ.differentiable (by simp) (r, y)).hasFDerivAt.comp y
    (hasFDerivAt_prodMk_right r y)
  unfold spatialPartial velocityGradient
  rw [show (fun x => φ (r, x)) = φ ∘ Prod.mk r by rfl, hs.fderiv]
  rfl

private theorem velocityGradient_continuous {d : ℕ} (φ : TimeVelocity d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (k : Fin d) :
    Continuous (fun z => velocityGradient φ z k) := by
  unfold velocityGradient
  simpa using (hφ.continuous_fderiv (by simp)).clm_apply continuous_const

private theorem velocityGradient_compact {d : ℕ} (φ : TimeVelocity d → ℝ)
    (hφ : HasCompactSupport φ) (k : Fin d) :
    HasCompactSupport (fun z => velocityGradient φ z k) := by
  unfold velocityGradient
  simpa using hφ.fderiv_apply (𝕜 := ℝ) ((0, Pi.single k 1) : TimeVelocity d)

private theorem integrable_bounded_mul_compact
    {d : ℕ} {S : Set (TimeVelocity d)} {f g : TimeVelocity d → ℝ} {B : ℝ}
    (hS : NullMeasurableSet S (volume : Measure (TimeVelocity d)))
    (hf : AEStronglyMeasurable f (timeVelocityVolumeOn S))
    (hB : 0 ≤ B) (hbound : ∀ z ∈ S, |f z| ≤ B)
    (hg : Continuous g) (hgcompact : HasCompactSupport g) :
    Integrable (fun z => f z * g z) (timeVelocityVolumeOn S) := by
  have hfTop : MemLp f ∞ (timeVelocityVolumeOn S) := by
    refine memLp_top_of_bound hf (max B 0) ?_
    filter_upwards [ae_restrict_mem₀ hS] with z hz
    simpa only [Real.norm_eq_abs, max_eq_left hB] using hbound z hz
  have hgOne : MemLp g 1 (timeVelocityVolumeOn S) :=
    hg.memLp_of_hasCompactSupport hgcompact
  simpa only [Pi.mul_def] using
    (memLp_one_iff_integrable.mp (hfTop.mul (p := ∞) (q := 1) (r := 1) hgOne))

private theorem integralOn_timeVelocity_prod
    {d : ℕ} (I : Set ℝ) (O : Set (PDE.Vec d))
    (f : TimeVelocity d → ℝ)
    (hf : Integrable f (timeVelocityVolumeOn (I ×ˢ O))) :
    (∫ z in I ×ˢ O, f z ∂volume) =
      ∫ r in I, ∫ y in O, f (r, y) ∂volume ∂volume := by
  change Integrable f ((volume : Measure (TimeVelocity d)).restrict (I ×ˢ O)) at hf
  rw [volume_timeVelocity_eq_prod d, ← Measure.prod_restrict] at hf ⊢
  exact integral_prod f hf

/-- A jointly measurable function whose fixed-time spatial slices are `C¹`
has its literal spatial partial as its raw weak velocity derivative on an
inner product carrier, provided the function and derivative are uniformly
bounded there. -/
theorem spatialC1_hasWeakVelocityPartialDerivOn
    {d : ℕ}
    {Iout Iin : Set ℝ}
    {O₀ O₁ : Set (PDE.Vec d)}
    (hI : Iin ⊆ Iout)
    (hIin : NullMeasurableSet Iin (volume : Measure ℝ))
    (hO₀ : IsOpen O₀)
    (hO₁ : IsOpen O₁)
    (hO₁compact : IsCompact (closure O₁))
    (hO₁O₀ : closure O₁ ⊆ O₀)
    (k : Fin d)
    (Bq Bdq : ℝ)
    (hBq : 0 ≤ Bq) (hBdq : 0 ≤ Bdq)
    (q : TimeVelocity d → ℝ)
    (hqMeas : AEStronglyMeasurable q
      (timeVelocityVolumeOn (Iout ×ˢ O₀)))
    (hqC1 : ∀ r ∈ Iout,
      ContDiffOn ℝ 1 (fun y => q (r, y)) O₀)
    (hqBound : ∀ z ∈ Iin ×ˢ O₁, |q z| ≤ Bq)
    (hdqBound : ∀ z ∈ Iin ×ˢ O₁,
      |spatialPartial k (fun y => q (z.1, y)) z.2| ≤ Bdq) :
    HasWeakVelocityPartialDerivOn (Iin ×ˢ O₁) k q
      (fun z => spatialPartial k (fun y => q (z.1, y)) z.2) := by
  let S : Set (TimeVelocity d) := Iin ×ˢ O₁
  let dq : TimeVelocity d → ℝ := fun z =>
    spatialPartial k (fun y => q (z.1, y)) z.2
  have hTarget : NullMeasurableSet S (volume : Measure (TimeVelocity d)) := by
    exact hIin.prod hO₁.measurableSet.nullMeasurableSet
  have hqInner : AEStronglyMeasurable q (timeVelocityVolumeOn S) := by
    exact hqMeas.mono_measure (Measure.restrict_mono_set volume
      (Set.prod_mono hI (fun y hy => hO₁O₀ (subset_closure hy))))
  have hdqMeas : AEStronglyMeasurable dq (timeVelocityVolumeOn S) := by
    apply aestronglyMeasurable_spatialSliceFDeriv_apply_on_prod hI hTarget
      hO₀ hO₁compact hO₁O₀ q hqMeas
    · intro r hr y hy
      exact ((hqC1 r hr).differentiableOn (by norm_num) y hy).differentiableAt
        (hO₀.mem_nhds hy)
  intro φ hφ hφcompact hφS
  have hvgCont := velocityGradient_continuous φ hφ k
  have hvgCompact := velocityGradient_compact φ hφcompact k
  have hleftInt : Integrable (fun z => q z * velocityGradient φ z k)
      (timeVelocityVolumeOn S) :=
    integrable_bounded_mul_compact hTarget hqInner hBq (by simpa only [S] using hqBound)
      hvgCont hvgCompact
  have hrightInt : Integrable (fun z => dq z * φ z)
      (timeVelocityVolumeOn S) :=
    integrable_bounded_mul_compact hTarget hdqMeas hBdq (by simpa only [dq, S] using hdqBound)
      hφ.continuous hφcompact
  have hslice (r : ℝ) (hr : r ∈ Iin) :
      (∫ y in O₁, q (r, y) * velocityGradient φ (r, y) k ∂volume) =
        -∫ y in O₁, dq (r, y) * φ (r, y) ∂volume := by
    have hqC1inner : ContDiffOn ℝ 1 (fun y => q (r, y)) O₁ :=
      (hqC1 r (hI hr)).mono (fun y hy => hO₁O₀ (subset_closure hy))
    have hφslice : ContDiffOn ℝ 1 (fun y : PDE.Vec d => φ (r, y)) O₁ :=
      (hφ.comp (contDiff_const.prodMk contDiff_id)).contDiffOn.of_le (by norm_num)
    have hφsliceCompact := hasCompactSupport_timeSlice r φ hφcompact
    have hφsliceSupport := tsupport_timeSlice_subset r φ hφS
    have hibp := setIntegral_mul_spatialPartial_eq_neg_spatialPartial_mul_of_right
      O₁ hO₁ k (fun y => q (r, y)) (fun y => φ (r, y)) hqC1inner hφslice
      hφsliceCompact hφsliceSupport
    simpa only [dq, spatialPartial_timeSlice_eq_velocityGradient r φ hφ] using hibp
  rw [integralOn_timeVelocity_prod Iin O₁ _ hleftInt,
    integralOn_timeVelocity_prod Iin O₁ _ hrightInt]
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem₀ hIin] with r hr
  exact hslice r hr

end HypoellipticAleksandrov.Parabolic
