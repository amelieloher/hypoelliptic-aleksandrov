module

public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabSetting

/-!
# Transport of the slab to the real line

`SlabBase d = ElapsedTime ⊤ × ℝ^d` carries Lebesgue measure on `(T,2T) × ℝ^d`
(`Green.slabBase`).  The occupation densities of Proposition 4.2 live on `ℝ × ℝ^d`.  The measurable
embedding `slabShift d s : (τ, w) ↦ (τ - s, w)` identifies the two; it maps `slabBase d T` to
Lebesgue measure on `(T - s, 2T - s) × ℝ^d`.  Also: elapsed-time integrals as ordinary integrals.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Green

open MeasureTheory Set
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal NNReal

/-- The time-shifted real-line image of a slab point: `(τ, w) ↦ (τ - s, w)`. -/
def slabShift (d : ℕ) (s : ℝ) (y : SlabBase d) : ℝ × PDE.Vec d := (y.1.1 - s, y.2)

lemma measurableEmbedding_elapsed_sub (s : ℝ) :
    MeasurableEmbedding (fun τ : ElapsedTime ⊤ => τ.1 - s) := by
  have h1 : MeasurableEmbedding (Subtype.val : ElapsedTime ⊤ → ℝ) :=
    MeasurableEmbedding.subtype_coe (measurableSet_elapsedTime ⊤)
  have h2 : MeasurableEmbedding (fun t : ℝ => t - s) :=
    (Homeomorph.subRight s).measurableEmbedding
  exact h2.comp h1

lemma measurableEmbedding_slabShift (d : ℕ) (s : ℝ) :
    MeasurableEmbedding (slabShift d s) :=
  (measurableEmbedding_elapsed_sub s).prodMap MeasurableEmbedding.id

lemma measurable_slabShift (d : ℕ) (s : ℝ) : Measurable (slabShift d s) :=
  (measurableEmbedding_slabShift d s).measurable

/-- Translating Lebesgue measure on an interval. -/
lemma map_sub_restrict_Ioo (a b s : ℝ) :
    (volume.restrict (Ioo a b)).map (fun t : ℝ => t - s) =
      volume.restrict (Ioo (a - s) (b - s)) := by
  have hf : Measurable (fun t : ℝ => t - s) := measurable_id.sub_const s
  have h := Measure.restrict_map (μ := (volume : Measure ℝ)) hf
    (measurableSet_Ioo (a := a - s) (b := b - s))
  have hpre : (fun t : ℝ => t - s) ⁻¹' Ioo (a - s) (b - s) = Ioo a b := by
    ext t; simp
  have hm : (volume : Measure ℝ).map (fun t : ℝ => t - s) = volume := by
    have := map_add_right_eq_self (volume : Measure ℝ) (-s)
    simpa only [sub_eq_add_neg] using this
  rw [hpre, hm] at h
  exact h.symm

/-- The slab time measure, as a measure on the real line. -/
lemma map_slabTime (T : ℝ) (hT : 0 ≤ T) :
    ((elapsedVolume ⊤).restrict (slabTimeSet T)).map (Subtype.val : ElapsedTime ⊤ → ℝ) =
      volume.restrict (Ioo T (2 * T)) := by
  have hset : slabTimeSet T = (Subtype.val : ElapsedTime ⊤ → ℝ) ⁻¹' Ioo T (2 * T) := by
    ext τ; simp [slabTimeSet]
  rw [hset, ← Measure.restrict_map measurable_subtype_coe measurableSet_Ioo]
  have key : (elapsedVolume ⊤).map (Subtype.val : ElapsedTime ⊤ → ℝ) =
      volume.restrict {τ : ℝ | 0 < τ ∧ ENNReal.ofReal τ < ⊤} :=
    map_comap_subtype_coe (measurableSet_elapsedTime ⊤) volume
  rw [key, Measure.restrict_restrict measurableSet_Ioo]
  congr 1
  apply inter_eq_left.2
  intro t ht
  exact ⟨by linarith [ht.1], ENNReal.ofReal_lt_top⟩

/-- The slab base measure is Lebesgue measure on `(T - s, 2T - s) × ℝ^d` under `slabShift`. -/
lemma map_slabBase_slabShift (d : ℕ) (T s : ℝ) (hT : 0 ≤ T) :
    (slabBase d T).map (slabShift d s) =
      volume.restrict (Ioo (T - s) (2 * T - s) ×ˢ (univ : Set (PDE.Vec d))) := by
  have h1 : slabShift d s =
      Prod.map (fun τ : ElapsedTime ⊤ => τ.1 - s) (id : PDE.Vec d → PDE.Vec d) := rfl
  have hmeas : Measurable (fun τ : ElapsedTime ⊤ => τ.1 - s) :=
    (measurableEmbedding_elapsed_sub s).measurable
  unfold slabBase
  rw [h1, ← Measure.map_prod_map _ _ hmeas measurable_id, Measure.map_id]
  have h2 : ((elapsedVolume ⊤).restrict (slabTimeSet T)).map (fun τ : ElapsedTime ⊤ => τ.1 - s) =
      volume.restrict (Ioo (T - s) (2 * T - s)) := by
    have hg : Measurable (fun t : ℝ => t - s) := measurable_id.sub_const s
    have := Measure.map_map (μ := (elapsedVolume ⊤).restrict (slabTimeSet T)) hg
      (measurable_subtype_coe (p := fun τ : ℝ => 0 < τ ∧ ENNReal.ofReal τ < ⊤))
    refine this.symm.trans ?_
    rw [map_slabTime T hT, map_sub_restrict_Ioo]
  rw [h2, Measure.volume_eq_prod]
  have := Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure (PDE.Vec d)))
    (Ioo (T - s) (2 * T - s)) univ
  rw [Measure.restrict_univ] at this
  exact this

/-- Elapsed-time integrals are ordinary integrals over `(0, ∞)`. -/
lemma lintegral_elapsed_top (F : ℝ → ℝ≥0∞) :
    ∫⁻ τ : ElapsedTime ⊤, F τ.1 ∂elapsedVolume ⊤ = ∫⁻ t in Ioi (0 : ℝ), F t := by
  have h := lintegral_subtype_comap (μ := (volume : Measure ℝ))
    (measurableSet_elapsedTime ⊤) F
  have hs : {τ : ℝ | 0 < τ ∧ ENNReal.ofReal τ < ⊤} = Ioi 0 := by
    ext t; simp
  refine Eq.trans h ?_
  rw [hs]

end HypoellipticAleksandrov.KineticAleksandrov.Green
