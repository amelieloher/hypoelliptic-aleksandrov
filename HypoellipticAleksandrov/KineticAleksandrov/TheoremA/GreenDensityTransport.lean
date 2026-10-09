module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Green
public import HypoellipticAleksandrov.Geometry.KineticPointMeasure
import Mathlib.MeasureTheory.Group.Prod

/-!
# Writing a Green measure in absolute time on kinetic space

The Green measure `Γ_μ^S` of (2.6) lives on `ElapsedTime S × (ℝ^d × ℝ^d)` with
coordinates `(τ,(w,z))`, elapsed time `τ`, velocity `w` and transported coordinate `z = X`.
Started at time `σ₀` it is written in absolute time on kinetic points by
`greenKineticPoint d σ₀ (τ,(w,z)) = (σ₀ + τ, z, w)`.  This module proves that this map is a
measurable embedding which pushes `elapsedVolume S ⊗ Leb` to Lebesgue measure restricted to the
slab `σ₀ < t < σ₀ + S`, and transports densities and `L^q` norms to Lebesgue measure of kinetic
space restricted to any measurable subset of the slab.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.TheoremA

open MeasureTheory Set
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal

/-- A Green-carrier point `(τ,(w,z))` started at time `σ₀`, as the kinetic point
`(σ₀ + τ, X = z, v = w)` in absolute time. -/
def greenKineticPoint (d : ℕ) (σ₀ : ℝ) {S : ℝ≥0∞}
    (q : ElapsedTime S × EvolutionAmbientState d) : KineticPoint d :=
  ⟨σ₀ + q.1.1, q.2.2, q.2.1⟩

/-- The kinetic points whose absolute time lies strictly between `σ₀` and `σ₀ + S`. -/
def elapsedSlab (d : ℕ) (σ₀ : ℝ) (S : ℝ≥0∞) : Set (KineticPoint d) :=
  {P | σ₀ < P.time ∧ ENNReal.ofReal (P.time - σ₀) < S}

/-- The coordinate change `(t,(w,z)) ↦ (σ₀ + t, X = z, v = w)` as a measurable equivalence. -/
def absoluteTimeEquiv (d : ℕ) (σ₀ : ℝ) : ℝ × EvolutionAmbientState d ≃ᵐ KineticPoint d :=
  ((MeasurableEquiv.addLeft σ₀).prodCongr MeasurableEquiv.prodComm).trans
    (KineticPoint.homeomorphProd d).symm.toMeasurableEquiv

theorem absoluteTimeEquiv_apply (d : ℕ) (σ₀ : ℝ) (q : ℝ × EvolutionAmbientState d) :
    absoluteTimeEquiv d σ₀ q = ⟨σ₀ + q.1, q.2.2, q.2.1⟩ := rfl

/-- The absolute-time coordinate change preserves Lebesgue measure. -/
theorem measurePreserving_absoluteTimeEquiv (d : ℕ) (σ₀ : ℝ) :
    MeasurePreserving (absoluteTimeEquiv d σ₀) volume volume := by
  let e := (KineticPoint.homeomorphProd d).toMeasurableEquiv
  have he : MeasurePreserving e volume volume := KineticPoint.measurePreserving_equivProd d
  have h1 : MeasurePreserving (MeasurableEquiv.addLeft σ₀) (volume : Measure ℝ) volume :=
    measurePreserving_add_left volume σ₀
  have h2 : MeasurePreserving (MeasurableEquiv.prodComm :
      EvolutionAmbientState d ≃ᵐ EvolutionAmbientState d)
      (volume : Measure (EvolutionAmbientState d)) volume :=
    Measure.measurePreserving_swap
  exact (he.symm e).comp (h1.prod h2)

theorem greenKineticPoint_eq (d : ℕ) (σ₀ : ℝ) (S : ℝ≥0∞) :
    greenKineticPoint d σ₀ (S := S) =
      absoluteTimeEquiv d σ₀ ∘ Prod.map (Subtype.val : ElapsedTime S → ℝ) id := rfl

/-- Absolute-time writing is a measurable embedding. -/
theorem measurableEmbedding_greenKineticPoint (d : ℕ) (σ₀ : ℝ) (S : ℝ≥0∞) :
    MeasurableEmbedding (greenKineticPoint d σ₀ (S := S)) := by
  rw [greenKineticPoint_eq]
  exact (absoluteTimeEquiv d σ₀).measurableEmbedding.comp
    ((MeasurableEmbedding.subtype_coe (measurableSet_elapsedTime S)).prodMap
      MeasurableEmbedding.id)

/-- Elapsed-time Lebesgue measure times Lebesgue measure is pushed to the slab Lebesgue measure. -/
theorem map_greenKineticPoint (d : ℕ) (σ₀ : ℝ) (S : ℝ≥0∞) :
    ((elapsedVolume S).prod (volume : Measure (EvolutionAmbientState d))).map
        (greenKineticPoint d σ₀) = volume.restrict (elapsedSlab d σ₀ S) := by
  have hj : Measurable (Prod.map (Subtype.val : ElapsedTime S → ℝ)
      (id : EvolutionAmbientState d → EvolutionAmbientState d)) :=
    measurable_subtype_coe.prodMap measurable_id
  have h1 : ((elapsedVolume S).prod (volume : Measure (EvolutionAmbientState d))).map
      (Prod.map (Subtype.val : ElapsedTime S → ℝ)
        (id : EvolutionAmbientState d → EvolutionAmbientState d)) =
      (volume : Measure (ℝ × EvolutionAmbientState d)).restrict
        ({τ : ℝ | 0 < τ ∧ ENNReal.ofReal τ < S} ×ˢ univ) := by
    have h := Measure.map_prod_map (elapsedVolume S)
      (volume : Measure (EvolutionAmbientState d)) measurable_subtype_coe
      (measurable_id : Measurable (id : EvolutionAmbientState d → EvolutionAmbientState d))
    rw [Measure.map_id] at h
    rw [← h]
    have h2 : (elapsedVolume S).map (Subtype.val : ElapsedTime S → ℝ) =
        volume.restrict {τ : ℝ | 0 < τ ∧ ENNReal.ofReal τ < S} :=
      map_comap_subtype_coe (measurableSet_elapsedTime S) volume
    rw [h2]
    have h3 := Measure.prod_restrict (μ := (volume : Measure ℝ))
      (ν := (volume : Measure (EvolutionAmbientState d)))
      {τ : ℝ | 0 < τ ∧ ENNReal.ofReal τ < S} univ
    rw [Measure.restrict_univ] at h3
    exact h3
  rw [greenKineticPoint_eq, ← Measure.map_map (absoluteTimeEquiv d σ₀).measurable hj, h1,
    ((measurePreserving_absoluteTimeEquiv d σ₀).restrict_image_emb
      (absoluteTimeEquiv d σ₀).measurableEmbedding _).map_eq]
  congr 1
  ext P
  constructor
  · rintro ⟨⟨t, w, z⟩, ⟨ht, -⟩, rfl⟩
    refine ⟨by simpa [absoluteTimeEquiv_apply] using ht.1, ?_⟩
    simpa [absoluteTimeEquiv_apply] using ht.2
  · rintro ⟨h0, hS⟩
    refine ⟨(P.time - σ₀, P.velocity, P.position), ⟨⟨sub_pos.2 h0, hS⟩, mem_univ _⟩, ?_⟩
    ext <;> simp [absoluteTimeEquiv_apply]

/-- The absolute-time slab is a measurable subset of kinetic space. -/
theorem measurableSet_elapsedSlab (d : ℕ) (σ₀ : ℝ) (S : ℝ≥0∞) :
    MeasurableSet (elapsedSlab d σ₀ S) := by
  have ht : Measurable (@KineticPoint.time d) := continuous_time.measurable
  exact (measurableSet_lt measurable_const ht).inter
    ((ENNReal.measurable_ofReal.comp (ht.sub_const σ₀)) measurableSet_Iio)

/-- Transport of a Green density and its `L^q` norm to Lebesgue measure on kinetic space.

If `Γ = (elapsedVolume S ⊗ Leb).withDensity G`, then on every measurable `Q` the absolute-time
pushforward of `Γ`, restricted to `Q`, has the density `extend ι G 0` (zero off the slab) with
respect to Lebesgue measure restricted to `Q`, and its `L^q(Q)` norm is at most that of `G`. -/
theorem greenKineticPoint_density {d : ℕ} (σ₀ : ℝ) (S : ℝ≥0∞)
    (Γ : Measure (ElapsedTime S × EvolutionAmbientState d))
    (G : ElapsedTime S × EvolutionAmbientState d → ℝ≥0∞) (hG : Measurable G)
    (hΓ : Γ = ((elapsedVolume S).prod (volume : Measure (EvolutionAmbientState d))).withDensity G)
    {Q : Set (KineticPoint d)} (hQ : MeasurableSet Q) :
    Measurable (Function.extend (greenKineticPoint d σ₀ (S := S)) G 0) ∧
      (Γ.map (greenKineticPoint d σ₀)).restrict Q =
        (volume.restrict Q).withDensity
          (Function.extend (greenKineticPoint d σ₀ (S := S)) G 0) ∧
      ∀ q : ℝ≥0∞, eLpNorm (Function.extend (greenKineticPoint d σ₀ (S := S)) G 0) q
          (volume.restrict Q) ≤
        eLpNorm G q ((elapsedVolume S).prod (volume : Measure (EvolutionAmbientState d))) := by
  set ν := (elapsedVolume S).prod (volume : Measure (EvolutionAmbientState d)) with hν
  set ι := greenKineticPoint d σ₀ (S := S) with hι
  have hemb : MeasurableEmbedding ι := measurableEmbedding_greenKineticPoint d σ₀ S
  set Gx := Function.extend ι G 0 with hGx
  have hGxm : Measurable Gx := hemb.measurable_extend hG measurable_const
  have hGxι : Gx ∘ ι = G := by
    funext x
    exact hemb.injective.extend_apply G 0 x
  have hslab := measurableSet_elapsedSlab d σ₀ S
  have hGxs : Gx = (elapsedSlab d σ₀ S).indicator Gx := by
    funext P
    by_cases hP : P ∈ elapsedSlab d σ₀ S
    · rw [indicator_of_mem hP]
    · rw [indicator_of_notMem hP]
      refine (Function.extend_apply' G (0 : KineticPoint d → ℝ≥0∞) P ?_).trans rfl
      rintro ⟨x, rfl⟩
      exact hP ⟨by simpa [hι, greenKineticPoint] using x.1.2.1,
        by simpa [hι, greenKineticPoint] using x.1.2.2⟩
  have hmap : Γ.map ι = (ν.map ι).withDensity Gx := by
    ext B hB
    rw [Measure.map_apply hemb.measurable hB, hΓ, withDensity_apply _ (hemb.measurable hB),
      withDensity_apply _ hB]
    calc ∫⁻ x in ι ⁻¹' B, G x ∂ν
        = ∫⁻ x, (ι ⁻¹' B).indicator G x ∂ν := (lintegral_indicator (hemb.measurable hB) _).symm
      _ = ∫⁻ x, B.indicator Gx (ι x) ∂ν := by
          refine lintegral_congr fun x => ?_
          by_cases hx : ι x ∈ B
          · simp only [indicator_of_mem (show x ∈ ι ⁻¹' B from hx),
              indicator_of_mem hx, ← hGxι]
            rfl
          · simp only [indicator_of_notMem (show x ∉ ι ⁻¹' B from hx),
              indicator_of_notMem hx]
      _ = ∫⁻ b, B.indicator Gx b ∂(ν.map ι) := (hemb.lintegral_map _).symm
      _ = ∫⁻ b in B, Gx b ∂(ν.map ι) := lintegral_indicator hB _
  have hvol : Γ.map ι = volume.withDensity Gx := by
    rw [hmap, hν, hι, map_greenKineticPoint, ← withDensity_indicator hslab, ← hGxs]
  refine ⟨hGxm, ?_, fun q => ?_⟩
  · rw [hvol, restrict_withDensity hQ]
  · have hnorm : eLpNorm Gx q (volume.restrict Q) =
        eLpNorm Gx q ((volume.restrict Q).restrict (elapsedSlab d σ₀ S)) := by
      conv_lhs => rw [hGxs]
      exact eLpNorm_indicator_eq_eLpNorm_restrict hslab
    calc eLpNorm Gx q (volume.restrict Q)
        = eLpNorm Gx q ((volume.restrict Q).restrict (elapsedSlab d σ₀ S)) := hnorm
      _ ≤ eLpNorm Gx q (volume.restrict (elapsedSlab d σ₀ S)) :=
          eLpNorm_mono_measure _ (by
            rw [Measure.restrict_restrict hslab, inter_comm, ← Measure.restrict_restrict hQ]
            exact Measure.restrict_le_self)
      _ = eLpNorm Gx q (ν.map ι) := by rw [hν, hι, map_greenKineticPoint]
      _ = eLpNorm (Gx ∘ ι) q ν :=
          eLpNorm_map_measure hGxm.aestronglyMeasurable hemb.measurable.aemeasurable
      _ = eLpNorm G q ν := by rw [hGxι]

end HypoellipticAleksandrov.KineticAleksandrov.TheoremA
