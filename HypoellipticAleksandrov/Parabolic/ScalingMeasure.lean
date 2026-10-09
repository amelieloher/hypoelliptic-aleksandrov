module

public import HypoellipticAleksandrov.Parabolic.Scaling
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Measure scaling for parabolic affine maps

This module proves the determinant, Haar-measure, and restricted `L^(d + 1)`
change-of-variables formulas for the affine map which multiplies time by
`r^2` and every velocity coordinate by `r`.  The results are stated for the
literal product Lebesgue measure on `TimeVelocity d`; no density-to-point or
higher-level parabolic estimate is imported here.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set
open scoped ENNReal

private theorem parabolicLinear_eq_prodMap (d : ℕ) (r : ℝ) :
    (parabolicLinear (d := d) r : TimeVelocity d →ₗ[ℝ] TimeVelocity d) =
      LinearMap.prodMap ((r ^ 2) • LinearMap.id) (r • LinearMap.id) := by
  apply LinearMap.ext
  rintro ⟨time, velocity⟩
  rfl

/-- The determinant of the parabolic linear scaling is `r^(d + 2)`. -/
theorem parabolicLinear_det (d : ℕ) (r : ℝ) :
    LinearMap.det (parabolicLinear (d := d) r : TimeVelocity d →ₗ[ℝ]
      TimeVelocity d) = r ^ (d + 2) := by
  rw [parabolicLinear_eq_prodMap, LinearMap.det_prodMap]
  rw [LinearMap.det_smul, LinearMap.det_smul, LinearMap.det_id,
    LinearMap.det_id, mul_one, CommSemiring.finrank_self, Module.finrank_pi,
    Fintype.card_fin, pow_one]
  simp only [mul_one]
  rw [← pow_add]
  congr 1
  omega

/-- A nonzero-radius parabolic affine map is injective. -/
theorem parabolicAffine_injective_of_ne_zero {d : ℕ} {t₀ r : ℝ} {v₀ : PDE.Vec d}
    (hr : r ≠ 0) : Function.Injective (parabolicAffine t₀ v₀ r) := by
  intro z w hzw
  apply Prod.ext
  · have htime := congrArg Prod.fst hzw
    change t₀ + r ^ 2 * z.1 = t₀ + r ^ 2 * w.1 at htime
    apply mul_left_cancel₀ (pow_ne_zero 2 hr)
    linarith
  · ext i
    have hvelocity := congrFun (congrArg Prod.snd hzw) i
    change v₀ i + r * z.2 i = v₀ i + r * w.2 i at hvelocity
    apply mul_left_cancel₀ hr
    linarith

/-- A nonzero-radius parabolic affine map is a measurable embedding. -/
theorem parabolicAffine_measurableEmbedding_of_ne_zero {d : ℕ} {t₀ r : ℝ}
    {v₀ : PDE.Vec d} (hr : r ≠ 0) :
    MeasurableEmbedding (parabolicAffine t₀ v₀ r) :=
  (contDiff_infty_parabolicAffine t₀ v₀ r).continuous.measurableEmbedding
    (parabolicAffine_injective_of_ne_zero hr)

/-- A positive-radius parabolic affine map is a measurable embedding. -/
theorem parabolicAffine_measurableEmbedding {d : ℕ} {t₀ r : ℝ} {v₀ : PDE.Vec d}
    (hr : 0 < r) :
    MeasurableEmbedding (parabolicAffine t₀ v₀ r) :=
  parabolicAffine_measurableEmbedding_of_ne_zero hr.ne'

private theorem parabolicLinear_det_ne_zero {d : ℕ} {r : ℝ} (hr : 0 < r) :
    LinearMap.det (parabolicLinear (d := d) r : TimeVelocity d →ₗ[ℝ]
      TimeVelocity d) ≠ 0 := by
  rw [parabolicLinear_det]
  exact (pow_pos hr _).ne'

private theorem parabolicAffine_eq_add_parabolicLinear {d : ℕ}
    (t₀ : ℝ) (v₀ : PDE.Vec d) (r : ℝ) :
    parabolicAffine t₀ v₀ r = fun z ↦ (t₀, v₀) + parabolicLinear r z := by
  funext z
  rfl

/-- The pushforward of product Lebesgue volume by a positive-radius parabolic
affine map has the inverse determinant factor. -/
theorem map_volume_parabolicAffine {d : ℕ} (t₀ : ℝ) (v₀ : PDE.Vec d) {r : ℝ}
    (hr : 0 < r) :
    Measure.map (parabolicAffine t₀ v₀ r) (volume : Measure (TimeVelocity d)) =
      ENNReal.ofReal ((r ^ (d + 2))⁻¹) • volume := by
  have hL_measurable : Measurable (parabolicLinear (d := d) r) :=
    (parabolicLinear (d := d) r).continuous_of_finiteDimensional.measurable
  have htranslation_measurable : Measurable (fun z : TimeVelocity d ↦ (t₀, v₀) + z) :=
    (continuous_const.add continuous_id).measurable
  let c : ℝ≥0∞ := ENNReal.ofReal ((r ^ (d + 2))⁻¹)
  have hlinear :
      Measure.map (parabolicLinear (d := d) r) (volume : Measure (TimeVelocity d)) =
        c • volume := by
    change Measure.map
        ((parabolicLinear (d := d) r : TimeVelocity d →ₗ[ℝ] TimeVelocity d) :
          TimeVelocity d → TimeVelocity d) volume = c • volume
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume
      (parabolicLinear_det_ne_zero hr)]
    rw [parabolicLinear_det, abs_inv, abs_of_pos (pow_pos hr _)]
  calc
    Measure.map (parabolicAffine t₀ v₀ r) (volume : Measure (TimeVelocity d)) =
        Measure.map (fun z : TimeVelocity d ↦ (t₀, v₀) + z)
          (Measure.map (parabolicLinear r) volume) := by
      rw [Measure.map_map htranslation_measurable hL_measurable]
      rw [parabolicAffine_eq_add_parabolicLinear]
      rfl
    _ = Measure.map (fun z : TimeVelocity d ↦ (t₀, v₀) + z) (c • volume) := by
      rw [hlinear]
    _ = c • Measure.map (fun z : TimeVelocity d ↦ (t₀, v₀) + z) volume := by
      rw [Measure.map_smul _ htranslation_measurable.aemeasurable]
    _ = c • volume := by
      rw [MeasureTheory.map_add_left_eq_self volume (t₀, v₀)]
    _ = ENNReal.ofReal ((r ^ (d + 2))⁻¹) • volume := rfl

/-- The image of a set under positive-radius parabolic affine scaling has the
direct determinant factor. -/
theorem volume_parabolicAffine_image_eq {d : ℕ} (t₀ : ℝ) (v₀ : PDE.Vec d)
    {r : ℝ} (hr : 0 < r) (s : Set (TimeVelocity d)) :
    (volume : Measure (TimeVelocity d)) (parabolicAffine t₀ v₀ r '' s) =
      ENNReal.ofReal (r ^ (d + 2)) * volume s := by
  let q : TimeVelocity d := (t₀, v₀)
  calc
    (volume : Measure (TimeVelocity d)) (parabolicAffine t₀ v₀ r '' s) =
        volume ((fun z : TimeVelocity d ↦ q + z) '' (parabolicLinear r '' s)) := by
      rw [parabolicAffine_eq_add_parabolicLinear, Set.image_image]
    _ = volume (parabolicLinear r '' s) := by
      rw [Set.image_add_left, measure_preimage_add]
    _ = ENNReal.ofReal (r ^ (d + 2)) * volume s := by
      rw [Measure.addHaar_image_continuousLinearMap, parabolicLinear_det,
        abs_of_pos (pow_pos hr _)]

private theorem map_restrict_parabolicAffine {d : ℕ} (t₀ : ℝ) (v₀ : PDE.Vec d)
    {r : ℝ} (hr : 0 < r) (s : Set (TimeVelocity d)) :
    Measure.map (parabolicAffine t₀ v₀ r) ((volume : Measure (TimeVelocity d)).restrict s) =
      (Measure.map (parabolicAffine t₀ v₀ r) volume).restrict
        (parabolicAffine t₀ v₀ r '' s) := by
  have hpreimage : parabolicAffine t₀ v₀ r ⁻¹' (parabolicAffine t₀ v₀ r '' s) = s :=
    preimage_image_eq _ (parabolicAffine_injective hr)
  calc
    Measure.map (parabolicAffine t₀ v₀ r) (volume.restrict s) =
        Measure.map (parabolicAffine t₀ v₀ r)
          (volume.restrict (parabolicAffine t₀ v₀ r ⁻¹' (parabolicAffine t₀ v₀ r '' s))) := by
      rw [hpreimage]
    _ = (Measure.map (parabolicAffine t₀ v₀ r) volume).restrict
        (parabolicAffine t₀ v₀ r '' s) :=
      ((parabolicAffine_measurableEmbedding hr).restrict_map volume
        (parabolicAffine t₀ v₀ r '' s)).symm

/-- The ENNReal restricted-norm pullback formula before its elementary real
power simplification.  It has no measurability or finiteness premise. -/
theorem parabolicELpNormOn_pullback_raw {d : ℕ} (t₀ : ℝ) (v₀ : PDE.Vec d)
    {r : ℝ} (hr : 0 < r) (f : TimeVelocity d → ℝ) (s : Set (TimeVelocity d)) :
    parabolicELpNormOn d
        (fun z ↦ r ^ 2 * f (parabolicAffine t₀ v₀ r z)) s =
      ‖r ^ 2‖ₑ *
        (ENNReal.ofReal ((r ^ (d + 2))⁻¹) ^
          (1 / parabolicExponent d).toReal) *
        parabolicELpNormOn d f (parabolicAffine t₀ v₀ r '' s) := by
  let a : TimeVelocity d → TimeVelocity d := parabolicAffine t₀ v₀ r
  let p : ℝ≥0∞ := parabolicExponent d
  let c : ℝ≥0∞ := ENNReal.ofReal ((r ^ (d + 2))⁻¹)
  have hc : c ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (pow_pos hr _))
  have hembedding : MeasurableEmbedding a := parabolicAffine_measurableEmbedding hr
  change eLpNorm (r ^ 2 • (f ∘ a)) p (volume.restrict s) =
    ‖r ^ 2‖ₑ * (c ^ (1 / p).toReal) *
      eLpNorm f p (volume.restrict (a '' s))
  rw [eLpNorm_const_smul, ← hembedding.eLpNorm_map_measure,
    map_restrict_parabolicAffine t₀ v₀ hr s, map_volume_parabolicAffine t₀ v₀ hr,
    Measure.restrict_smul, eLpNorm_smul_measure_of_ne_zero hc]
  simp only [a, smul_eq_mul, mul_assoc]

private theorem parabolicExponent_toReal (d : ℕ) :
    (parabolicExponent d).toReal = (d : ℝ) + 1 := by
  unfold parabolicExponent
  have hcast : (d : ℝ≥0∞) + 1 = ((d + 1 : ℕ) : ℝ≥0∞) := by
    norm_num
  rw [hcast, ENNReal.toReal_natCast]
  norm_num

private theorem parabolic_norm_scaling_factor (d : ℕ) {r : ℝ} (hr : 0 < r) :
    r ^ 2 * ((r ^ (d + 2))⁻¹) ^ (1 / ((d : ℝ) + 1)) =
      r ^ ((d : ℝ) / ((d : ℝ) + 1)) := by
  have hp : (d : ℝ) + 1 ≠ 0 := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_natCast]
  rw [← Real.rpow_neg hr.le]
  rw [← Real.rpow_mul hr.le, ← Real.rpow_add hr]
  congr 1
  push_cast
  field_simp [hp]
  ring

/-- Exact restricted `L^(d + 1)` scaling under positive-radius parabolic affine
pullback.  The `toReal` norm encoding makes the statement valid also when the
underlying extended norm is infinite. -/
theorem parabolicLpNormOn_pullback {d : ℕ} (t₀ : ℝ) (v₀ : PDE.Vec d) {r : ℝ}
    (hr : 0 < r) (f : TimeVelocity d → ℝ) (s : Set (TimeVelocity d)) :
    parabolicLpNormOn d
        (fun z ↦ r ^ 2 * f (parabolicAffine t₀ v₀ r z)) s =
      r ^ ((d : ℝ) / ((d : ℝ) + 1)) *
        parabolicLpNormOn d f (parabolicAffine t₀ v₀ r '' s) := by
  have hraw := parabolicELpNormOn_pullback_raw t₀ v₀ hr f s
  have hreal := congrArg ENNReal.toReal hraw
  unfold parabolicLpNormOn
  calc
    (parabolicELpNormOn d
        (fun z ↦ r ^ 2 * f (parabolicAffine t₀ v₀ r z)) s).toReal =
        ‖r ^ 2‖ₑ.toReal *
          (ENNReal.ofReal ((r ^ (d + 2))⁻¹)).toReal ^
            (1 / parabolicExponent d).toReal *
          (parabolicELpNormOn d f (parabolicAffine t₀ v₀ r '' s)).toReal := by
      rw [hreal, ENNReal.toReal_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
    _ = r ^ ((d : ℝ) / ((d : ℝ) + 1)) *
          (parabolicELpNormOn d f (parabolicAffine t₀ v₀ r '' s)).toReal := by
      rw [Real.enorm_of_nonneg (sq_nonneg r), ENNReal.toReal_ofReal (sq_nonneg r),
        ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_pos hr _).le),
        ENNReal.toReal_div, ENNReal.toReal_one,
        parabolicExponent_toReal, parabolic_norm_scaling_factor d hr]

end HypoellipticAleksandrov.Parabolic
