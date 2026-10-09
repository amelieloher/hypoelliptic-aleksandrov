module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Absorb.DensityCarrier
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.DensityFromTests
import HypoellipticAleksandrov.KineticAleksandrov.Green.Horizon
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# The density from smoothed `L^q` bounds (abstract duality lemma)

Let
`Γ = elapsedVolume ⊗ₘ κ` be a finite measure on the carrier `ElapsedTime S × ℝ^{2d}` and suppose
the smoothed slice densities `ρ_ε(τ, y) = ∫ Φ_ε(y - y') dκ_τ(y')` satisfy
`∫∫ ρ_ε^q ≤ K^q` for every `ε > 0`, for an approximate identity `Φ`.  Then `Γ` has a Lebesgue
density `G` on the carrier with `‖G‖_{L^q} ≤ K`.  The proof pairs `Γ` with smooth compactly
supported tests (`integral_le_of_smoothed_bound`), applies the sharp density theorem
`exists_density_of_smooth_tests` on `ℝ × ℝ^{2d}`, and transports the density back.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory ProbabilityTheory
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal

variable {d : ℕ} {lam : ℝ}

/-- Local instance: Lebesgue measure on phase space is an additive Haar measure. -/
local instance absorbVolumeIsAddHaar''' (d : ℕ) :
    (volume : Measure (EvolutionAmbientState d)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure volume volume

/-- Local instance: Lebesgue measure on time-phase space is an additive Haar measure. -/
local instance absorbVolumeIsAddHaarTime (d : ℕ) :
    (volume : Measure (ℝ × EvolutionAmbientState d)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure volume volume

/-- The test inequality on the slab: smooth compactly supported nonnegative tests pair with `Γ`
at most `K` times their `L^{q'}` norm. -/
theorem integral_le_of_smoothed_bound_slab {Φ : SmoothingKernelFamily d lam}
    (hΦ : IsApproxIdentity Φ) {S : ℝ≥0∞} (κ : Kernel (ElapsedTime S) (EvolutionAmbientState d))
    [IsFiniteKernel κ] [IsFiniteMeasure (elapsedVolume S ⊗ₘ κ)] {q K : ℝ} (hq : 1 < q)
    (hK : 0 ≤ K)
    (hρ : ∀ ε : ℝ, 0 < ε →
      ∫⁻ x, ENNReal.ofReal (smoothDensity Φ ε (κ x.1) x.2 ^ q)
          ∂((elapsedVolume S).prod (volume : Measure (EvolutionAmbientState d))) ≤
        ENNReal.ofReal (K ^ q))
    (f : ℝ × EvolutionAmbientState d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) (hf0 : ∀ x, 0 ≤ f x) :
    ∫ x, f x ∂((elapsedVolume S ⊗ₘ κ).map (carrierEmbedding d S)) ≤
      K * (eLpNorm f (ENNReal.ofReal (q / (q - 1)))
        ((volume : Measure (ℝ × EvolutionAmbientState d)).restrict (carrierSlab d S))).toReal := by
  have hpq : (q / (q - 1)).HolderConjugate q :=
    (Real.HolderConjugate.conjExponent hq).symm
  have hp0 : 0 < q / (q - 1) := by have := hpq.lt; linarith
  have hfcont : Continuous f := hf.continuous
  have hemb := measurableEmbedding_carrierEmbedding d S
  set μ0 := (elapsedVolume S).prod (volume : Measure (EvolutionAmbientState d)) with hμ0
  obtain ⟨B, hB⟩ := hfcont.bounded_above_of_compact_support hfc
  have hmem : MemLp f (ENNReal.ofReal (q / (q - 1)))
      ((volume : Measure (ℝ × EvolutionAmbientState d)).restrict (carrierSlab d S)) :=
    hfcont.memLp_of_hasCompactSupport hfc
  have hnorm : eLpNorm f (ENNReal.ofReal (q / (q - 1)))
      ((volume : Measure (ℝ × EvolutionAmbientState d)).restrict (carrierSlab d S)) =
      (∫⁻ x, ENNReal.ofReal (f (carrierEmbedding d S x)) ^ (q / (q - 1)) ∂μ0) ^
        (1 / (q / (q - 1))) := by
    rw [← map_carrierEmbedding_volume d S, hemb.eLpNorm_map_measure,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hp0).ne' ENNReal.ofReal_ne_top
      ((hfcont.comp (continuous_carrierEmbedding d S)).measurable.aestronglyMeasurable),
      ENNReal.toReal_ofReal hp0.le]
    simp_rw [Function.comp_apply, Real.enorm_eq_ofReal (hf0 _)]
    rfl
  have hfin : (∫⁻ x, ENNReal.ofReal (f (carrierEmbedding d S x)) ^ (q / (q - 1)) ∂μ0) ≠ ⊤ := by
    intro htop
    have := hmem.eLpNorm_lt_top
    rw [hnorm, htop, ENNReal.top_rpow_of_pos (by have := hpq.lt; positivity)] at this
    exact lt_irrefl _ this
  have key := integral_le_of_smoothed_bound hΦ (elapsedVolume S) κ hpq hK hρ
    (ψ := fun x => f (carrierEmbedding d S x))
    (hfcont.comp (continuous_carrierEmbedding d S)).measurable
    (fun τ => hfcont.comp (continuous_const.prodMk continuous_id))
    (fun x => hf0 _) (B := B) (fun x => (Real.le_norm_self _).trans (hB _)) hfin
  rw [hemb.integral_map, hnorm]
  exact key

/-- **Abstract duality lemma**.
If `Γ = elapsedVolume ⊗ₘ κ` is finite and the smoothed slice densities satisfy
`∫∫ ρ_ε^q ≤ K^q` for every `ε > 0`, for an approximate identity `Φ`, then `Γ` has a Lebesgue
density `G` on the carrier with `‖G‖_{L^q} ≤ K`. -/
theorem exists_density_of_smoothed_bounds {Φ : SmoothingKernelFamily d lam}
    (hΦ : IsApproxIdentity Φ) {S : ℝ≥0∞} (κ : Kernel (ElapsedTime S) (EvolutionAmbientState d))
    [IsFiniteKernel κ] (Γ : Measure (ElapsedTime S × EvolutionAmbientState d))
    [IsFiniteMeasure Γ] (hΓ : Γ = elapsedVolume S ⊗ₘ κ) {q K : ℝ} (hq : 1 < q) (hK : 0 ≤ K)
    (hρ : ∀ ε : ℝ, 0 < ε →
      ∫⁻ x, ENNReal.ofReal (smoothDensity Φ ε (κ x.1) x.2 ^ q)
          ∂((elapsedVolume S).prod (volume : Measure (EvolutionAmbientState d))) ≤
        ENNReal.ofReal (K ^ q)) :
    ∃ G : ElapsedTime S × EvolutionAmbientState d → ℝ≥0∞, Measurable G ∧
      Γ = ((elapsedVolume S).prod (volume : Measure (EvolutionAmbientState d))).withDensity G ∧
      eLpNorm G (ENNReal.ofReal q)
        ((elapsedVolume S).prod (volume : Measure (EvolutionAmbientState d))) ≤
          ENNReal.ofReal K := by
  subst hΓ
  have hq0 : 0 < q := by linarith
  have hemb := measurableEmbedding_carrierEmbedding d S
  set ν : Measure (ℝ × EvolutionAmbientState d) := volume with hν
  set U := carrierSlab d S with hU
  set Γ' := (elapsedVolume S ⊗ₘ κ).map (carrierEmbedding d S) with hΓ'
  have hμU : Γ' Uᶜ = 0 := by
    rw [hΓ', Measure.map_apply hemb.measurable (isOpen_carrierSlab d S).measurableSet.compl]
    have : carrierEmbedding d S ⁻¹' Uᶜ = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false,
        not_not]
      exact carrierEmbedding_mem d S x
    rw [this, measure_empty]
  obtain ⟨-, g, hgm, hg0, hgi, hgLp, hgn, -, hrep⟩ :=
    HypoellipticAleksandrov.KineticAleksandrov.Occupation.exists_density_of_smooth_tests ν Γ'
      (isOpen_carrierSlab d S) hμU hq hK
      (fun f hf hfc _ hf0 => integral_le_of_smoothed_bound_slab hΦ κ hq hK hρ f hf hfc hf0)
  -- the density on the slab
  have hden : Γ' = (ν.restrict U).withDensity (fun e => ENNReal.ofReal (g e)) := by
    ext B hB
    have h1 := hrep (B.indicator 1)
    have h2 : ∫ x, B.indicator (1 : ℝ × EvolutionAmbientState d → ℝ) x * g x ∂ν.restrict U =
        ∫ x in B, g x ∂ν.restrict U := by
      rw [← integral_indicator hB]
      congr 1
      funext x
      by_cases hx : x ∈ B <;> simp [hx]
    rw [h2, integral_indicator_one hB] at h1
    rw [withDensity_apply _ hB, ← ofReal_integral_eq_lintegral_ofReal hgi.integrableOn
      (Filter.Eventually.of_forall fun x => hg0 x), h1, ofReal_measureReal]
  have hmapμ0 := map_carrierEmbedding_volume d S
  refine ⟨fun x => ENNReal.ofReal (g (carrierEmbedding d S x)),
    (ENNReal.measurable_ofReal.comp hgm).comp hemb.measurable, ?_, ?_⟩
  · refine HypoellipticAleksandrov.KineticAleksandrov.Green.eq_withDensity_of_map_eq_emb hemb
      (G' := fun e => ENNReal.ofReal (g e)) ?_
    rw [hmapμ0]
    exact hden
  · have hn : eLpNorm (fun e => ENNReal.ofReal (g e)) (ENNReal.ofReal q) (ν.restrict U) =
        eLpNorm g (ENNReal.ofReal q) (ν.restrict U) :=
      eLpNorm_congr_enorm_ae (ENNReal.measurable_ofReal.comp hgm).aestronglyMeasurable
        hgm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
          rw [Real.enorm_eq_ofReal (hg0 x)]; exact enorm_eq_self _)
    have h3 : eLpNorm (fun x => ENNReal.ofReal (g (carrierEmbedding d S x))) (ENNReal.ofReal q)
        ((elapsedVolume S).prod (volume : Measure (EvolutionAmbientState d))) =
        eLpNorm g (ENNReal.ofReal q) (ν.restrict U) := by
      rw [← hn, ← hmapμ0, hemb.eLpNorm_map_measure]
      rfl
    rw [h3, ← ENNReal.ofReal_toReal hgLp.eLpNorm_ne_top]
    exact ENNReal.ofReal_le_ofReal hgn

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
