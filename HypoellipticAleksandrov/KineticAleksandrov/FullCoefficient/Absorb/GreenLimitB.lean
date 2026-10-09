module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Absorb.GreenLimitA
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Absorb.DatumMain
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Absorb.Arith

/-!
# The absorption bound for the mollified Green densities, in lower integrals

The absorption estimate for the Green measure with the time mollifier
`η_n`, expressed as a bound on `∫⁻` over `{x : τ(x) ∈ (τ₁, τ₂)}` of `ρ^q`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory ProbabilityTheory Filter Topology
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal

variable {d : ℕ} {lam Lam T q : ℝ}

/-- Lower integral over a time slab of the elapsed-time product, as an iterated integral on `ℝ`. -/
theorem lintegral_elapsed_slab {a b : ℝ} (hT : 0 < T) (hab : Set.Ioo a b ⊆ Set.Ioo 0 T)
    (G : ℝ × EvolutionAmbientState d → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ x in (fun x : ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d => x.1.1) ⁻¹'
        Set.Ioo a b, G (x.1.1, x.2)
      ∂((elapsedVolume (ENNReal.ofReal T)).prod (volume : Measure (EvolutionAmbientState d))) =
      ∫⁻ t in Set.Ioo a b, ∫⁻ y, G (t, y) := by
  have hemb : MeasurableEmbedding (Subtype.val : ElapsedTime (ENNReal.ofReal T) → ℝ) :=
    MeasurableEmbedding.subtype_coe (measurableSet_elapsedTime (ENNReal.ofReal T))
  have hmap : (elapsedVolume (ENNReal.ofReal T)).map Subtype.val =
      volume.restrict {τ : ℝ | 0 < τ ∧ ENNReal.ofReal τ < ENNReal.ofReal T} :=
    map_comap_subtype_coe (measurableSet_elapsedTime _) volume
  have hcar : Set.Ioo a b ⊆ {τ : ℝ | 0 < τ ∧ ENNReal.ofReal τ < ENNReal.ofReal T} := fun s hs =>
    ⟨(hab hs).1, (ENNReal.ofReal_lt_ofReal_iff hT).2 (hab hs).2⟩
  have hset : (fun x : ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d => x.1.1) ⁻¹'
      Set.Ioo a b =
        (Subtype.val ⁻¹' Set.Ioo a b) ×ˢ (Set.univ : Set (EvolutionAmbientState d)) := by
    ext x; simp
  have hs : MeasurableSet (Subtype.val ⁻¹' Set.Ioo a b : Set (ElapsedTime (ENNReal.ofReal T))) :=
    measurable_subtype_coe measurableSet_Ioo
  rw [hset, ← Measure.prod_restrict, Measure.restrict_univ]
  have hGm : Measurable fun x : ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d =>
      G (x.1.1, x.2) := hG.comp ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
  rw [lintegral_prod _ hGm.aemeasurable]
  set H : ℝ → ℝ≥0∞ := fun t => ∫⁻ y, G (t, y) with hHdef
  change ∫⁻ x in Subtype.val ⁻¹' Set.Ioo a b, H x.1 ∂(elapsedVolume (ENNReal.ofReal T)) = _
  calc ∫⁻ x in Subtype.val ⁻¹' Set.Ioo a b, H x.1 ∂(elapsedVolume (ENNReal.ofReal T))
      = ∫⁻ t, H t ∂(((elapsedVolume (ENNReal.ofReal T)).restrict
          (Subtype.val ⁻¹' Set.Ioo a b)).map Subtype.val) := (hemb.lintegral_map H).symm
    _ = ∫⁻ t, H t ∂(((elapsedVolume (ENNReal.ofReal T)).map Subtype.val).restrict
          (Set.Ioo a b)) := by
        rw [← hemb.restrict_map (elapsedVolume (ENNReal.ofReal T)) (Set.Ioo a b)]
    _ = ∫⁻ t in Set.Ioo a b, H t := by
        rw [hmap, Measure.restrict_restrict measurableSet_Ioo, Set.inter_eq_left.2 hcar]

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
