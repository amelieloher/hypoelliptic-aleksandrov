module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Elapsed
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Absorb.DensityLimit
import Mathlib.MeasureTheory.Measure.Prod

/-!
# The elapsed-time carrier inside `ℝ × ℝ^{2d}`

The carrier `ElapsedTime S × ℝ^{2d}` of a Green measure embeds into the vector space
`ℝ × ℝ^{2d}` as the open set `U = {t | 0 < t, ofReal t < S} × ℝ^{2d}`, and the product of the
elapsed Lebesgue measure with Lebesgue measure on phase space is Lebesgue measure restricted to
`U`.  This transfers the sharp density theorem for smooth tests in a vector space
(`exists_density_of_smooth_tests`) to the carrier.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal

variable {d : ℕ}

/-- The embedding of the carrier into `ℝ × ℝ^{2d}`. -/
def carrierEmbedding (d : ℕ) (S : ℝ≥0∞) :
    ElapsedTime S × EvolutionAmbientState d → ℝ × EvolutionAmbientState d :=
  Prod.map Subtype.val id

/-- The open slab `{t | 0 < t < S} × ℝ^{2d}` in `ℝ × ℝ^{2d}`. -/
def carrierSlab (d : ℕ) (S : ℝ≥0∞) : Set (ℝ × EvolutionAmbientState d) :=
  {p | 0 < p.1 ∧ ENNReal.ofReal p.1 < S}

theorem isOpen_carrierSlab (d : ℕ) (S : ℝ≥0∞) : IsOpen (carrierSlab d S) :=
  (isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt (ENNReal.continuous_ofReal.comp continuous_fst) continuous_const)

theorem measurableEmbedding_carrierEmbedding (d : ℕ) (S : ℝ≥0∞) :
    MeasurableEmbedding (carrierEmbedding d S) :=
  (MeasurableEmbedding.subtype_coe (measurableSet_elapsedTime S)).prodMap
    MeasurableEmbedding.id

theorem carrierEmbedding_mem (d : ℕ) (S : ℝ≥0∞) (x : ElapsedTime S × EvolutionAmbientState d) :
    carrierEmbedding d S x ∈ carrierSlab d S :=
  ⟨x.1.2.1, x.1.2.2⟩

theorem continuous_carrierEmbedding (d : ℕ) (S : ℝ≥0∞) :
    Continuous (carrierEmbedding d S) :=
  continuous_subtype_val.prodMap continuous_id

/-- The product of elapsed Lebesgue measure and phase-space Lebesgue measure is Lebesgue measure
on the slab. -/
theorem map_carrierEmbedding_volume (d : ℕ) (S : ℝ≥0∞) :
    ((elapsedVolume S).prod (volume : Measure (EvolutionAmbientState d))).map
        (carrierEmbedding d S) =
      (volume : Measure (ℝ × EvolutionAmbientState d)).restrict (carrierSlab d S) := by
  have h1 := Measure.map_prod_map (elapsedVolume S) (volume : Measure (EvolutionAmbientState d))
    (measurable_subtype_coe : Measurable (Subtype.val : ElapsedTime S → ℝ)) measurable_id
  have h2 : (elapsedVolume S).map (Subtype.val : ElapsedTime S → ℝ) =
      volume.restrict {τ : ℝ | 0 < τ ∧ ENNReal.ofReal τ < S} :=
    map_comap_subtype_coe (measurableSet_elapsedTime S) volume
  rw [Measure.map_id, h2] at h1
  have h3 := Measure.prod_restrict (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (EvolutionAmbientState d)))
    {τ : ℝ | 0 < τ ∧ ENNReal.ofReal τ < S} Set.univ
  rw [Measure.restrict_univ, Set.prod_univ] at h3
  have h4 : (volume : Measure (ℝ × EvolutionAmbientState d)).restrict (carrierSlab d S) =
      (volume.restrict {τ : ℝ | 0 < τ ∧ ENNReal.ofReal τ < S}).prod
        (volume : Measure (EvolutionAmbientState d)) := h3.symm
  rw [h4]
  exact h1.symm

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
