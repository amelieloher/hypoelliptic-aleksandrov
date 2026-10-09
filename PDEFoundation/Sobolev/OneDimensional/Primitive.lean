module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# One-dimensional interval primitives

This file records the honest primitive half of the one-dimensional Sobolev
foundation.  It deliberately does **not** identify a distributional weak
derivative with the derivative of this primitive; that is a separate theorem.

The public estimates use the Lebesgue representative `t ↦ ∫_a^t g`.  Thus
they are available before any choice of a Sobolev representative.
-/

@[expose] public section

open scoped ENNReal Topology Interval

namespace PDE

open MeasureTheory Set

noncomputable section

/-- The interval primitive of a scalar function, based at `a`. -/
def intervalPrimitive (a : ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in a..t, g x

@[simp] theorem intervalPrimitive_self (a : ℝ) (g : ℝ → ℝ) :
    intervalPrimitive a g a = 0 := by
  simp [intervalPrimitive]

/-- Exact increments of an interval primitive.  The hypotheses are only the
local integrability needed to make the two displayed primitives additive. -/
theorem intervalPrimitive_sub_eq_intervalIntegral
    {a b s t : ℝ} {g : ℝ → ℝ}
    (hg : IntegrableOn g (Icc a b) volume)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    intervalPrimitive a g t - intervalPrimitive a g s = ∫ x in s..t, g x := by
  unfold intervalPrimitive
  have hgt : IntervalIntegrable g volume a t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht.1]
    exact hg.mono_set (Icc_subset_Icc le_rfl ht.2)
  have hgs : IntervalIntegrable g volume a s := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hs.1]
    exact hg.mono_set (Icc_subset_Icc le_rfl hs.2)
  exact intervalIntegral.integral_interval_sub_left
    hgt hgs

/-- A locally integrable interval primitive is continuous.  This is a
continuity theorem only; the later weak-derivative bridge must still establish
the a.e. derivative identity separately. -/
theorem continuousOn_intervalPrimitive
    {a b : ℝ} {g : ℝ → ℝ} (hab : a ≤ b)
    (hg : IntegrableOn g (Icc a b) volume) :
    ContinuousOn (intervalPrimitive a g) (Icc a b) := by
  have hg' : IntegrableOn g (uIcc a b) volume := by
    simpa [uIcc_of_le hab] using hg
  change ContinuousOn (fun t => ∫ x in a..t, g x) (Icc a b)
  rw [← uIcc_of_le hab]
  exact intervalIntegral.continuousOn_primitive_interval
    (μ := volume) (f := g) (a := a) (b := b) hg'

/-- An `L²` integrand has an `L²` left-based interval primitive on the same
closed bounded interval.  The accompanying collar estimate below retains the
explicit `(b - a)²` scale factor. -/
theorem memLp_intervalPrimitive_two_on_Icc
    {a b : ℝ} {g : ℝ → ℝ} (hab : a ≤ b)
    (hg : MemLp g 2 (volume.restrict (Icc a b))) :
    MemLp (intervalPrimitive a g) 2 (volume.restrict (Icc a b)) := by
  let : IsFiniteMeasure (volume.restrict (Icc a b)) := ⟨by simp⟩
  have hgInt : IntegrableOn g (Icc a b) volume := by
    simpa only [IntegrableOn] using hg.integrable (by norm_num)
  have hcontinuous : ContinuousOn (intervalPrimitive a g) (Icc a b) :=
    continuousOn_intervalPrimitive hab hgInt
  have hmeas : AEStronglyMeasurable (intervalPrimitive a g)
      (volume.restrict (Icc a b)) :=
    hcontinuous.aestronglyMeasurable measurableSet_Icc
  have hsq : IntegrableOn (fun x => (intervalPrimitive a g x) ^ 2)
      (Icc a b) volume :=
    (hcontinuous.pow 2).integrableOn_Icc
  exact (memLp_two_iff_integrable_sq hmeas).2 hsq

/-- The elementary endpoint estimate for the interval primitive, stated with
the exact smaller interval. -/
theorem abs_intervalPrimitive_sub_le_setIntegral_abs
    {a b s t : ℝ} {g : ℝ → ℝ}
    (hg : IntegrableOn g (Icc a b) volume)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    |intervalPrimitive a g t - intervalPrimitive a g s| ≤
      ∫ x in Icc s t, |g x| := by
  rw [intervalPrimitive_sub_eq_intervalIntegral hg hs ht]
  calc
    |∫ x in s..t, g x| ≤ ∫ x in s..t, |g x| :=
      intervalIntegral.abs_integral_le_integral_abs hst
    _ = ∫ x in Icc s t, |g x| := by
      rw [intervalIntegral.integral_of_le hst, ← integral_Icc_eq_integral_Ioc]

/-- The corresponding collar estimate on the original interval.  The
right-hand side contains no hidden domain-dependent constant. -/
theorem abs_intervalPrimitive_sub_le_setIntegral_abs_collar
    {a b s t : ℝ} {g : ℝ → ℝ}
    (hg : IntegrableOn g (Icc a b) volume)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    |intervalPrimitive a g t - intervalPrimitive a g s| ≤
      ∫ x in Icc a b, |g x| := by
  refine (abs_intervalPrimitive_sub_le_setIntegral_abs hg hs ht hst).trans ?_
  refine setIntegral_mono_set ?_ ?_ ?_
  · exact hg.norm
  · exact Filter.Eventually.of_forall fun _ => abs_nonneg _
  · exact Filter.Eventually.of_forall (Icc_subset_Icc hs.1 ht.2)

/-- The exact Cauchy--Schwarz endpoint bound, before rewriting the elementary
constant-function factor as the length of `Icc s t`.  Keeping this factor
visible avoids concealing any scale or measure normalization. -/
theorem abs_intervalPrimitive_sub_le_l2_product
    {a b s t : ℝ} {g : ℝ → ℝ}
    (hg : IntegrableOn g (Icc a b) volume)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (hg2 : MemLp g 2 (volume.restrict (Icc s t))) :
    |intervalPrimitive a g t - intervalPrimitive a g s| ≤
      (∫ x in Icc s t, |g x| ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) *
        (∫ _x in Icc s t, (1 : ℝ) ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) := by
  let : IsFiniteMeasure (volume.restrict (Icc s t)) :=
    ⟨by simp⟩
  have hone : MemLp (fun _ : ℝ => (1 : ℝ)) 2
      (volume.restrict (Icc s t)) := memLp_const 1
  have hg2' : MemLp g (ENNReal.ofReal (2 : ℝ))
      (volume.restrict (Icc s t)) := by
    simpa using hg2
  have hone' : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ))
      (volume.restrict (Icc s t)) := by
    simpa using hone
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (μ := volume.restrict (Icc s t)) Real.HolderConjugate.two_two hg2' hone'
  refine (abs_intervalPrimitive_sub_le_setIntegral_abs hg hs ht hst).trans ?_
  simpa only [Real.norm_eq_abs, abs_one, mul_one] using hholder

/-- Evaluation of the constant-function factor in the preceding
Cauchy--Schwarz estimate. -/
theorem setIntegral_one_rpow_two_eq_sub {s t : ℝ} (hst : s ≤ t) :
    ∫ _x in Icc s t, (1 : ℝ) ^ (2 : ℝ) ∂volume = t - s := by
  simp [hst]

/-- The scale-sharp `L²` endpoint estimate for an interval primitive.  The
constant is exactly one; its squared form is the usual Cauchy--Schwarz factor
`t - s`. -/
theorem abs_intervalPrimitive_sub_le_l2
    {a b s t : ℝ} {g : ℝ → ℝ}
    (hg : IntegrableOn g (Icc a b) volume)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (hg2 : MemLp g 2 (volume.restrict (Icc s t))) :
    |intervalPrimitive a g t - intervalPrimitive a g s| ≤
      (∫ x in Icc s t, |g x| ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) *
        (t - s) ^ (1 / (2 : ℝ)) := by
  calc
    |intervalPrimitive a g t - intervalPrimitive a g s| ≤
        (∫ x in Icc s t, |g x| ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) *
          (∫ _x in Icc s t, (1 : ℝ) ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) :=
      abs_intervalPrimitive_sub_le_l2_product hg hs ht hst hg2
    _ = _ := by rw [setIntegral_one_rpow_two_eq_sub hst]

/-- Squared scale-sharp endpoint estimate for an interval primitive.  This is
the form used when integrating a one-dimensional collar estimate: no square
root or implicit constant remains. -/
theorem sq_abs_intervalPrimitive_sub_le_l2
    {a b s t : ℝ} {g : ℝ → ℝ}
    (hg : IntegrableOn g (Icc a b) volume)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (hg2 : MemLp g 2 (volume.restrict (Icc s t))) :
    |intervalPrimitive a g t - intervalPrimitive a g s| ^ 2 ≤
      (t - s) * ∫ x in Icc s t, |g x| ^ (2 : ℝ) ∂volume := by
  let A : ℝ := ∫ x in Icc s t, |g x| ^ (2 : ℝ) ∂volume
  let ℓ : ℝ := t - s
  have hA : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg fun x ↦ Real.rpow_nonneg (abs_nonneg (g x)) _
  have hℓ : 0 ≤ ℓ := sub_nonneg.mpr hst
  have hroot : |intervalPrimitive a g t - intervalPrimitive a g s| ≤ √A * √ℓ := by
    simpa only [A, ℓ, Real.sqrt_eq_rpow] using
      abs_intervalPrimitive_sub_le_l2 hg hs ht hst hg2
  change |intervalPrimitive a g t - intervalPrimitive a g s| ^ 2 ≤ ℓ * A
  rw [← Real.sq_sqrt (mul_nonneg hℓ hA)]
  refine (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mpr ?_
  calc
    |intervalPrimitive a g t - intervalPrimitive a g s| ≤ √A * √ℓ := hroot
    _ = √(A * ℓ) := (Real.sqrt_mul hA ℓ).symm
    _ = √(ℓ * A) := by rw [mul_comm]

/-- A left-endpoint `L²` collar bound for an interval primitive.  Its scaling
is sharp; replacing the pointwise Cauchy--Schwarz bound by its triangular
kernel gives the factor `1 / 2` in a later refinement. -/
theorem setIntegral_sq_intervalPrimitive_le_left_collar
    {a b : ℝ} {g : ℝ → ℝ} (hab : a ≤ b)
    (hg : IntegrableOn g (Icc a b) volume)
    (hg2 : MemLp g 2 (volume.restrict (Icc a b))) :
    ∫ x in Icc a b, |intervalPrimitive a g x| ^ 2 ∂volume ≤
      (b - a) ^ 2 * ∫ x in Icc a b, |g x| ^ (2 : ℝ) ∂volume := by
  let A : ℝ := ∫ x in Icc a b, |g x| ^ (2 : ℝ) ∂volume
  have hA : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg fun x ↦ Real.rpow_nonneg (abs_nonneg (g x)) _
  have hAint : IntegrableOn (fun x ↦ |g x| ^ (2 : ℝ)) (Icc a b) volume := by
    simpa only [Real.norm_eq_abs] using!
      hg2.integrable_norm_rpow (by norm_num) (by norm_num)
  have hprim_cont : ContinuousOn (intervalPrimitive a g) (Icc a b) :=
    continuousOn_intervalPrimitive hab hg
  have hprim_sq_int : IntegrableOn (fun x ↦ |intervalPrimitive a g x| ^ 2)
      (Icc a b) volume :=
    ((hprim_cont.abs).pow 2).integrableOn_Icc
  have hconst_int : IntegrableOn (fun _x : ℝ ↦ (b - a) * A) (Icc a b) volume :=
    integrableOn_const (by rw [Real.volume_Icc]; simp)
  calc
    ∫ x in Icc a b, |intervalPrimitive a g x| ^ 2 ∂volume ≤
        ∫ _x in Icc a b, (b - a) * A ∂volume := by
      refine setIntegral_mono_ae_restrict hprim_sq_int hconst_int ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      have hg2x : MemLp g 2 (volume.restrict (Icc a x)) :=
        hg2.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl hx.2) le_rfl)
      have hpoint := sq_abs_intervalPrimitive_sub_le_l2 hg ⟨le_rfl, hab⟩ hx hx.1 hg2x
      rw [intervalPrimitive_self] at hpoint
      have hAmono : ∫ y in Icc a x, |g y| ^ (2 : ℝ) ∂volume ≤ A := by
        dsimp [A]
        exact setIntegral_mono_set hAint
          (Filter.Eventually.of_forall fun y ↦ Real.rpow_nonneg (abs_nonneg (g y)) _)
          (Filter.Eventually.of_forall fun y hy ↦ (Icc_subset_Icc le_rfl hx.2) hy)
      calc
        |intervalPrimitive a g x| ^ 2 ≤
            (x - a) * ∫ y in Icc a x, |g y| ^ (2 : ℝ) ∂volume := by
              simpa only [sub_zero] using hpoint
        _ ≤ (x - a) * A :=
          mul_le_mul_of_nonneg_left hAmono (sub_nonneg.mpr hx.1)
        _ ≤ (b - a) * A :=
          mul_le_mul_of_nonneg_right (sub_le_sub_right hx.2 a) hA
    _ = (b - a) ^ 2 * A := by
      rw [setIntegral_const, measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
      simp only [smul_eq_mul]
      ring
    _ = _ := rfl

/-- The matching right-endpoint `L²` collar bound.  The integrand is written
as an increment of the fixed left-based representative, so no change of
Sobolev representative is involved. -/
theorem setIntegral_sq_intervalPrimitive_sub_le_right_collar
    {a b : ℝ} {g : ℝ → ℝ} (hab : a ≤ b)
    (hg : IntegrableOn g (Icc a b) volume)
    (hg2 : MemLp g 2 (volume.restrict (Icc a b))) :
    ∫ x in Icc a b, |intervalPrimitive a g b - intervalPrimitive a g x| ^ 2 ∂volume ≤
      (b - a) ^ 2 * ∫ x in Icc a b, |g x| ^ (2 : ℝ) ∂volume := by
  let A : ℝ := ∫ x in Icc a b, |g x| ^ (2 : ℝ) ∂volume
  have hA : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg fun x ↦ Real.rpow_nonneg (abs_nonneg (g x)) _
  have hAint : IntegrableOn (fun x ↦ |g x| ^ (2 : ℝ)) (Icc a b) volume := by
    simpa only [Real.norm_eq_abs] using!
      hg2.integrable_norm_rpow (by norm_num) (by norm_num)
  have hprim_cont : ContinuousOn (intervalPrimitive a g) (Icc a b) :=
    continuousOn_intervalPrimitive hab hg
  have hprim_sq_int : IntegrableOn
      (fun x ↦ |intervalPrimitive a g b - intervalPrimitive a g x| ^ 2) (Icc a b) volume :=
    ((continuousOn_const.sub hprim_cont).abs.pow 2).integrableOn_Icc
  have hconst_int : IntegrableOn (fun _x : ℝ ↦ (b - a) * A) (Icc a b) volume :=
    integrableOn_const (by rw [Real.volume_Icc]; simp)
  calc
    ∫ x in Icc a b, |intervalPrimitive a g b - intervalPrimitive a g x| ^ 2 ∂volume ≤
        ∫ _x in Icc a b, (b - a) * A ∂volume := by
      refine setIntegral_mono_ae_restrict hprim_sq_int hconst_int ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      have hg2x : MemLp g 2 (volume.restrict (Icc x b)) :=
        hg2.mono_measure (Measure.restrict_mono (Icc_subset_Icc hx.1 le_rfl) le_rfl)
      have hpoint := sq_abs_intervalPrimitive_sub_le_l2 hg hx ⟨hab, le_rfl⟩ hx.2 hg2x
      have hAmono : ∫ y in Icc x b, |g y| ^ (2 : ℝ) ∂volume ≤ A := by
        dsimp [A]
        exact setIntegral_mono_set hAint
          (Filter.Eventually.of_forall fun y ↦ Real.rpow_nonneg (abs_nonneg (g y)) _)
          (Filter.Eventually.of_forall fun y hy ↦ (Icc_subset_Icc hx.1 le_rfl) hy)
      calc
        |intervalPrimitive a g b - intervalPrimitive a g x| ^ 2 ≤
            (b - x) * ∫ y in Icc x b, |g y| ^ (2 : ℝ) ∂volume := hpoint
        _ ≤ (b - x) * A :=
          mul_le_mul_of_nonneg_left hAmono (sub_nonneg.mpr hx.2)
        _ ≤ (b - a) * A :=
          mul_le_mul_of_nonneg_right (sub_le_sub_left hx.1 b) hA
    _ = (b - a) ^ 2 * A := by
      rw [setIntegral_const, measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
      simp only [smul_eq_mul]
      ring
    _ = _ := rfl

end

end PDE
