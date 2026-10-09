module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.LevelMeasurability
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-! # Boundedness and exact set transport for affine level sets -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

open Set MeasureTheory

/-- Every bounded kinetic set has a compact coordinate envelope. -/
theorem bounded_kinetic_compact_envelope {d : ℕ} {E : Set (KineticPoint d)}
    (hE : Bornology.IsBounded E) : ∃ K : Set (KineticPoint d), IsCompact K ∧ E ⊆ K := by
  let e := KineticPoint.isometryEquivProd d
  have hb := e.isometry.lipschitzWith.isBounded_image hE
  refine ⟨(KineticPoint.homeomorphProd d).symm '' closure (e '' E),
    hb.isCompact_closure.image (KineticPoint.homeomorphProd d).symm.continuous, ?_⟩
  intro P hP
  exact ⟨e P, subset_closure ⟨P, hP, rfl⟩, e.symm_apply_apply P⟩

/-- A nonzero affine preimage of a bounded kinetic set remains bounded. -/
theorem isBounded_kineticAffine_preimage {d : ℕ} (P0 : KineticPoint d) {R : ℝ}
    (hR : R ≠ 0) {E : Set (KineticPoint d)} (hE : Bornology.IsBounded E) :
    Bornology.IsBounded (kineticAffine P0 R ⁻¹' E) := by
  obtain ⟨K, hK, hEK⟩ := bounded_kinetic_compact_envelope hE
  exact ((kineticAffineHomeomorph P0 R hR).isCompact_preimage.mpr hK).isBounded.subset
    (preimage_mono hEK)

/-- Affine images of bounded kinetic sets have compact coordinate envelopes. -/
theorem isBounded_kineticAffine_image {d : ℕ} (P0 : KineticPoint d) (R : ℝ)
    {E : Set (KineticPoint d)} (hE : Bornology.IsBounded E) :
    Bornology.IsBounded (kineticAffine P0 R '' E) := by
  obtain ⟨K, hK, hEK⟩ := bounded_kinetic_compact_envelope hE
  exact (hK.image (continuous_kineticAffine P0 R)).isBounded.subset (image_mono hEK)

/-- Homeomorphic affine transport exactly recovers every level intersection. -/
theorem kineticAffine_image_preimage_inter {d : ℕ} (P0 : KineticPoint d) {R : ℝ}
    (hR : R ≠ 0) (E F : Set (KineticPoint d)) :
    kineticAffine P0 R '' ((kineticAffine P0 R ⁻¹' E) ∩
      (kineticAffine P0 R ⁻¹' F)) = E ∩ F := by
  rw [← preimage_inter]
  exact (kineticAffineHomeomorph P0 R hR).toEquiv.image_preimage _

/-- Affine pullbacks of measurable levels are measurable in the same Lebesgue space. -/
theorem measurableSet_kineticAffine_preimage {d : ℕ} (P0 : KineticPoint d) (R : ℝ)
    {E : Set (KineticPoint d)} (hE : MeasurableSet E) :
    MeasurableSet (kineticAffine P0 R ⁻¹' E) :=
  hE.preimage (continuous_kineticAffine P0 R).measurable

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
