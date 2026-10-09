module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometry
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic

/-! # The homogeneous volume factor of kinetic affine scaling -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open MeasureTheory Set
open scoped ENNReal

/-- Coordinate dilation with the kinetic exponents two, three, and one. -/
def kineticCoordinateDilation (d : ℕ) (R : ℝ) :
    (ℝ × (PDE.Vec d × PDE.Vec d)) →ₗ[ℝ] (ℝ × (PDE.Vec d × PDE.Vec d)) :=
  LinearMap.prodMap ((R ^ 2) • LinearMap.id)
    (LinearMap.prodMap ((R ^ 3) • LinearMap.id) (R • LinearMap.id))

/-- The exact homogeneous dimension is four times the spatial dimension plus two. -/
theorem kineticCoordinateDilation_det (d : ℕ) (R : ℝ) :
    LinearMap.det (kineticCoordinateDilation d R) = R ^ (4 * d + 2) := by
  simp only [kineticCoordinateDilation, LinearMap.det_prodMap, LinearMap.det_smul,
    LinearMap.det_id, mul_one, CommSemiring.finrank_self, Module.finrank_pi,
    Fintype.card_fin, pow_one]
  rw [← pow_mul, ← pow_add, ← pow_add]
  congr 1
  omega

/-- Galilean transport in coordinate space preserves unnormalised product volume. -/
theorem measurePreserving_kineticShear {d : ℕ} (v₀ : PDE.Vec d) :
    MeasurePreserving
      (fun z : ℝ × (PDE.Vec d × PDE.Vec d) =>
        (z.1, (z.2.1 + z.1 • v₀, z.2.2))) volume volume := by
  have : (volume : Measure (PDE.Vec d × PDE.Vec d)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure volume volume
  have h := (MeasurePreserving.id (volume : Measure ℝ)).skew_product
    (g := fun t (z : PDE.Vec d × PDE.Vec d) => z + (t • v₀, 0))
    (by fun_prop) (Filter.Eventually.of_forall fun t =>
      map_add_right_eq_self (volume : Measure (PDE.Vec d × PDE.Vec d)) (t • v₀, 0))
  simpa only [Prod.add_def, add_zero, id_eq, Measure.volume_eq_prod] using h

/-- Coordinate formula for the source affine map. -/
def kineticCoordinateAffine {d : ℕ} (P₀ : KineticPoint d) (R : ℝ)
    (z : ℝ × (PDE.Vec d × PDE.Vec d)) : ℝ × (PDE.Vec d × PDE.Vec d) :=
  (P₀.time + R ^ 2 * z.1,
    (P₀.position + R ^ 3 • z.2.1 + (R ^ 2 * z.1) • P₀.velocity,
      P₀.velocity + R • z.2.2))

/-- Pushforward volume under kinetic affine scaling has inverse homogeneous factor. -/
theorem map_volume_kineticCoordinateAffine {d : ℕ} (P₀ : KineticPoint d)
    {R : ℝ} (hR : 0 < R) :
    Measure.map (kineticCoordinateAffine P₀ R) volume =
      ENNReal.ofReal ((R ^ (4 * d + 2))⁻¹) • volume := by
  have : (volume : Measure (PDE.Vec d × PDE.Vec d)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure volume volume
  have : (volume : Measure (ℝ × (PDE.Vec d × PDE.Vec d))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure volume volume
  let L := kineticCoordinateDilation d R
  let S := fun z : ℝ × (PDE.Vec d × PDE.Vec d) =>
    (z.1, (z.2.1 + z.1 • P₀.velocity, z.2.2))
  let q : ℝ × (PDE.Vec d × PDE.Vec d) :=
    (P₀.time, (P₀.position, P₀.velocity))
  have hL : Measurable L := L.continuous_of_finiteDimensional.measurable
  have hS : Measurable S := (measurePreserving_kineticShear P₀.velocity).measurable
  have hT : Measurable (fun z => q + z) := by fun_prop
  have heq : kineticCoordinateAffine P₀ R = (fun z => q + z) ∘ S ∘ L := by
    funext z
    ext i
    all_goals simp [kineticCoordinateAffine, S, L, q, kineticCoordinateDilation]
    all_goals ring
  rw [heq, ← Measure.map_map hT (hS.comp hL), ← Measure.map_map hS hL]
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume
    (show LinearMap.det L ≠ 0 by
      rw [kineticCoordinateDilation_det]; exact (pow_pos hR _).ne')]
  rw [kineticCoordinateDilation_det, abs_inv, abs_of_pos (pow_pos hR _),
    Measure.map_smul _ hS.aemeasurable,
    (measurePreserving_kineticShear P₀.velocity).map_eq,
    Measure.map_smul _ hT.aemeasurable, map_add_left_eq_self]

/-- Pushforward kinetic volume uses exactly the coordinate homogeneous factor. -/
theorem map_volume_kineticAffine {d : ℕ} (P₀ : KineticPoint d)
    {R : ℝ} (hR : 0 < R) :
    Measure.map (kineticAffine P₀ R) volume =
      ENNReal.ofReal ((R ^ (4 * d + 2))⁻¹) • volume := by
  let e := (KineticPoint.homeomorphProd d).toMeasurableEquiv
  have he : MeasurePreserving e volume volume := KineticPoint.measurePreserving_equivProd d
  have hf : Measurable (kineticCoordinateAffine P₀ R) := by
    unfold kineticCoordinateAffine
    fun_prop
  have heq : kineticAffine P₀ R = e.symm ∘ kineticCoordinateAffine P₀ R ∘ e := rfl
  rw [heq, ← Measure.map_map e.symm.measurable (hf.comp e.measurable),
    ← Measure.map_map hf e.measurable, he.map_eq, map_volume_kineticCoordinateAffine P₀ hR,
    Measure.map_smul _ e.symm.measurable.aemeasurable, (he.symm e).map_eq]

/-- Images under kinetic scaling have the direct homogeneous volume factor. -/
theorem volume_kineticAffine_image {d : ℕ} (P₀ : KineticPoint d)
    {R : ℝ} (hR : 0 < R) (E : Set (KineticPoint d)) :
    volume (kineticAffine P₀ R '' E) =
      ENNReal.ofReal (R ^ (4 * d + 2)) * volume E := by
  let e := (kineticAffineHomeomorph P₀ R hR.ne').toMeasurableEquiv
  have h := e.measurableEmbedding.map_apply (μ := volume) (e '' E)
  rw [e.injective.preimage_image] at h
  change (Measure.map (kineticAffine P₀ R) volume) (kineticAffine P₀ R '' E) =
    volume E at h
  rw [map_volume_kineticAffine P₀ hR, Measure.smul_apply, smul_eq_mul,
    ENNReal.ofReal_inv_of_pos (pow_pos hR _)] at h
  have hc : ENNReal.ofReal (R ^ (4 * d + 2)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (pow_pos hR _)).ne'
  calc
    volume (kineticAffine P₀ R '' E) =
        ENNReal.ofReal (R ^ (4 * d + 2)) *
          ((ENNReal.ofReal (R ^ (4 * d + 2)))⁻¹ *
            volume (kineticAffine P₀ R '' E)) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel hc ENNReal.ofReal_ne_top, one_mul]
    _ = _ := by rw [h]

end HypoellipticAleksandrov.KineticAleksandrov.Holder
