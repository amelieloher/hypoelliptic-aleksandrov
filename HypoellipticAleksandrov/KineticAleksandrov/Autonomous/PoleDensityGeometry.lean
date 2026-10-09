module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockPushforward
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Exact Lebesgue normalization between Green carrier and physical clock coordinates -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution Green
open scoped ENNReal NNReal

/-- Native product coordinates become physical coordinates by exchanging the spatial fields. -/
def poleDensityPhysicalHomeomorph : (ℝ × PDE.Vec 1 × PDE.Vec 1) ≃ₜ Point :=
  ((Homeomorph.refl ℝ).prodCongr (Homeomorph.prodComm (PDE.Vec 1) (PDE.Vec 1))).trans
    (KineticPoint.homeomorphProd 1).symm

/-- The native-to-physical product coordinate map preserves the literal kinetic volume. -/
theorem poleDensityPhysical_volumePreserving :
    MeasurePreserving poleDensityPhysicalHomeomorph volume volume := by
  have hs : MeasurePreserving (Prod.map (id : ℝ → ℝ) Prod.swap)
      (volume : Measure (ℝ × PDE.Vec 1 × PDE.Vec 1)) volume :=
    (MeasurePreserving.id volume).prod Measure.measurePreserving_swap
  have hp : MeasurePreserving (KineticPoint.equivProd 1).symm volume volume :=
    ⟨KineticPoint.measurable_equivProd_symm 1, rfl⟩
  exact hp.comp hs

/-- The established Green elapsed-to-physical map is a measurable embedding at clock time zero. -/
theorem poleDensityElapsed_measurableEmbedding :
    MeasurableEmbedding (elapsedPhysicalPoint 0 (R := ⊤)) := by
  have he := (MeasurableEmbedding.subtype_coe (measurableSet_elapsedTime ⊤)).prodMap
    (MeasurableEmbedding.id : MeasurableEmbedding (id : EvolutionAmbientState 1 → _))
  have hc := poleDensityPhysicalHomeomorph.measurableEmbedding.comp he
  have heq : (poleDensityPhysicalHomeomorph ∘
      Prod.map (Subtype.val : ElapsedTime ⊤ → ℝ) id) = elapsedPhysicalPoint 0 := by
    funext q
    apply (KineticPoint.equivProd 1).injective
    change (q.1.1, q.2.2, q.2.1) = (0 + q.1.1, q.2.2, q.2.1)
    rw [zero_add]
  exact heq ▸ hc

/-- Positive physical time is the exact range of the normalized Green carrier embedding. -/
theorem poleDensityElapsed_range :
    range (elapsedPhysicalPoint 0 (R := ⊤)) = {p : Point | 0 < p.time} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    change 0 < 0 + q.1.1
    simpa only [zero_add] using q.1.2.1
  · intro hp
    refine ⟨(⟨p.time, hp, ENNReal.ofReal_lt_top⟩, p.velocity, p.position), ?_⟩
    ext i <;> simp [elapsedPhysicalPoint]

/-- The Green Lebesgue reference maps to the literal positive-time physical Lebesgue restriction. -/
theorem poleDensityElapsed_map_volume :
    (greenLebesgue 1).map (elapsedPhysicalPoint 0) =
      (volume : Measure Point).restrict {p | 0 < p.time} := by
  have heq : elapsedPhysicalPoint 0 (R := ⊤) = poleDensityPhysicalHomeomorph ∘
      Prod.map (Subtype.val : ElapsedTime ⊤ → ℝ) id := by
    funext q
    apply (KineticPoint.equivProd 1).injective
    change (0 + q.1.1, q.2.2, q.2.1) = (q.1.1, q.2.2, q.2.1)
    rw [zero_add]
  have ht : (elapsedVolume ⊤).map (Subtype.val : ElapsedTime ⊤ → ℝ) =
      (volume : Measure ℝ).restrict (Ioi 0) := by
    have h := map_comap_subtype_coe (measurableSet_elapsedTime ⊤) (volume : Measure ℝ)
    have hs : {t : ℝ | 0 < t ∧ ENNReal.ofReal t < (⊤ : ℝ≥0∞)} = Ioi 0 := by
      ext t
      simp only [ENNReal.ofReal_lt_top, and_true, mem_Ioi, mem_ofPred_eq]
    exact h.trans (congrArg (fun S : Set ℝ => volume.restrict S) hs)

  rw [heq, greenLebesgue, ← Measure.map_map poleDensityPhysicalHomeomorph.continuous.measurable
    (measurable_subtype_coe.prodMap measurable_id), ← Measure.map_prod_map _ _
      measurable_subtype_coe measurable_id, ht, Measure.map_id,
    Measure.restrict_prod_eq_prod_univ]
  have hr := poleDensityPhysicalHomeomorph.measurableEmbedding.restrict_map
    (volume : Measure (ℝ × PDE.Vec 1 × PDE.Vec 1)) {p | 0 < p.time}
  have hpre : poleDensityPhysicalHomeomorph ⁻¹' {p | 0 < p.time} =
      Ioi 0 ×ˢ (univ : Set (EvolutionAmbientState 1)) := by
    ext q
    change (0 < q.1) ↔ (0 < q.1 ∧ q.2 ∈ univ)
    simp only [mem_univ, and_true]
  exact (congrArg (fun s : Set (ℝ × EvolutionAmbientState 1) =>
    (volume.restrict s).map poleDensityPhysicalHomeomorph) hpre).symm.trans
      (hr.symm.trans (congrArg (fun μ : Measure Point => μ.restrict {p | 0 < p.time})
        poleDensityPhysical_volumePreserving.map_eq))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
