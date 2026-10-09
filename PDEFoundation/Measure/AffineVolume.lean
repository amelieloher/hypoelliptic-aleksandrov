module

public import PDEFoundation.Geometry.Affine
public import PDEFoundation.Measure.RestrictedVolume
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Translation and dilation of volume

Exact change-of-variable statements for native vectors. These are the
measure-level foundation of all later scale-invariant norms.
-/

@[expose] public section

open scoped Pointwise

namespace PDE

open MeasureTheory

theorem measurePreserving_subRight_restrict_translateSet {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) :
    MeasurePreserving (fun x : Vec d => x - z)
      (volumeOn (translateSet z U)) (volumeOn U) := by
  let hμ :
      MeasurePreserving (fun x : Vec d => x + -z)
        (volume : Measure (Vec d)) volume :=
    measurePreserving_add_right
      (volume : Measure (Vec d)) (-z)
  simpa [volumeOn, preimage_addNeg_eq_translateSet (z := z) U] using!
    MeasurePreserving.restrict_preimage_emb hμ
      (Homeomorph.subRight z).measurableEmbedding U

theorem measurePreserving_addRight_restrict_translateSet {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) :
    MeasurePreserving (fun x : Vec d => x + z)
      (volumeOn U) (volumeOn (translateSet z U)) := by
  let hμ :
      MeasurePreserving (fun x : Vec d => x + z)
        (volume : Measure (Vec d)) volume :=
    measurePreserving_add_right
      (volume : Measure (Vec d)) z
  simpa [volumeOn, preimage_addNeg_eq_translateSet (z := z) U,
    image_addRight_eq_translateSet (z := z) U, sub_eq_add_neg] using
    MeasurePreserving.restrict_image_emb hμ
      (Homeomorph.addRight z).measurableEmbedding U

theorem setIntegral_comp_subRight_translateSet
    {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (z : Vec d) (U : Set (Vec d)) (f : Vec d → E) :
    ∫ x in translateSet z U, f (x - z) ∂volume =
      ∫ y in U, f y ∂volume := by
  simpa using
    (measurePreserving_subRight_restrict_translateSet z U).integral_comp
      (Homeomorph.subRight z).measurableEmbedding f

theorem setIntegral_comp_addRight_translateSet
    {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (z : Vec d) (U : Set (Vec d)) (f : Vec d → E) :
    ∫ y in U, f (y + z) ∂volume =
      ∫ x in translateSet z U, f x ∂volume := by
  simpa using
    (measurePreserving_addRight_restrict_translateSet z U).integral_comp
      (Homeomorph.addRight z).measurableEmbedding f

theorem volume_translateSet_eq {d : ℕ}
    (z : Vec d) (U : Set (Vec d)) :
    volume (translateSet z U) = volume U := by
  have h :=
    MeasurePreserving.measure_preimage_emb
      (measurePreserving_add_right
        (volume : Measure (Vec d)) z)
      (Homeomorph.addRight z).measurableEmbedding
      (translateSet z U)
  simpa [preimage_addRight_translateSet_eq] using h.symm

theorem volume_smul_set_of_nonneg {d : ℕ}
    {r : ℝ} (hr : 0 ≤ r) (U : Set (Vec d)) :
    volume (r • U) =
      ENNReal.ofReal (r ^ d) * volume U := by
  simpa [Vec] using
    (Measure.addHaar_smul_of_nonneg
      (μ := volume) (E := Vec d) hr U)

theorem volume_smul_set_toReal_of_pos {d : ℕ}
    {r : ℝ} (hr : 0 < r) (U : Set (Vec d)) :
    (volume (r • U)).toReal =
      r ^ d * (volume U).toReal := by
  rw [volume_smul_set_of_nonneg hr.le U, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hr.le d)]

/-- Scaling by a positive scalar pushes restricted volume forward to the
corresponding restricted volume, with the exact Jacobian factor displayed. -/
theorem map_smul_volumeOn_of_pos {d : ℕ} {r : ℝ} (hr : 0 < r)
    (U : Set (Vec d)) :
    Measure.map (fun x : Vec d => r • x) (volumeOn U) =
      ENNReal.ofReal ((r ^ d)⁻¹) • volumeOn (r • U) := by
  have hr_ne : r ≠ 0 := hr.ne'
  let e : Homeomorph (Vec d) (Vec d) :=
    Homeomorph.smulOfNeZero r hr_ne
  have heq : (fun x : Vec d => e x) = fun x : Vec d => r • x := rfl
  have hrestrict :
      Measure.map (fun x : Vec d => r • x) (volumeOn U) =
        (Measure.map (fun x : Vec d => r • x) volume).restrict
          (r • U) := by
    have htmp :
        (volume.restrict U).map e =
          (volume.map e).restrict (e '' U) := by
      have h :=
        ((e.toMeasurableEquiv.restrict_map
          (μ := volume) (s := e '' U)).symm)
      simpa [Set.preimage_image_eq _ e.injective] using h
    simpa [volumeOn, heq] using htmp
  have hmap :
      Measure.map (fun x : Vec d => r • x) volume =
        ENNReal.ofReal ((r ^ d)⁻¹) • volume := by
    let f : Vec d →ₗ[ℝ] Vec d :=
      r • (1 : Vec d →ₗ[ℝ] Vec d)
    have hf : LinearMap.det f ≠ 0 := by
      simp [f, hr_ne]
    have hdet : LinearMap.det f = r ^ d := by
      simp [f]
    have hmapf :=
      Real.map_linearMap_volume_pi_eq_smul_volume_pi
        (ι := Fin d) (f := f) hf
    have hpowInvNonneg : 0 ≤ (r ^ d)⁻¹ := by
      positivity
    rw [hdet] at hmapf
    simpa [f, abs_of_nonneg hpowInvNonneg] using! hmapf
  rw [hrestrict, hmap, Measure.restrict_smul]

theorem setIntegral_comp_smul_of_pos
    {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {r : ℝ} (hr : 0 < r) (U : Set (Vec d))
    (f : Vec d → E) :
    ∫ x in U, f (r • x) ∂volume =
      (r ^ d)⁻¹ • ∫ y in r • U, f y ∂volume := by
  simpa [Vec] using
    (Measure.setIntegral_comp_smul_of_pos
      (μ := volume) (f := f) (s := U) hr)

/-- Pullback by inverse positive dilation displays the exact real Jacobian
factor in a set integral. -/
theorem setIntegral_comp_inv_smul_smul_set_of_pos
    {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {r : ℝ} (hr : 0 < r) (U : Set (Vec d))
    (f : Vec d → E) :
    ∫ x in r • U, f (r⁻¹ • x) ∂volume =
      (r ^ d) • ∫ y in U, f y ∂volume := by
  have hrNe : r ≠ 0 := hr.ne'
  have hpow : r ^ d ≠ 0 := (pow_pos hr d).ne'
  have hchange :=
    setIntegral_comp_smul_of_pos
      (d := d) hr U (fun x : Vec d => f (r⁻¹ • x))
  have hscaled := congrArg
    (fun v : E => (r ^ d) • v) hchange
  simpa only [smul_smul, smul_eq_mul, inv_mul_cancel₀ hrNe,
    one_smul, mul_inv_cancel₀ hpow] using hscaled.symm

end PDE
