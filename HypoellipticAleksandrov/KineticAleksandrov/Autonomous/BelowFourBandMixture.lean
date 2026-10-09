module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionDensitySumReal
import Mathlib.MeasureTheory.Integral.Prod

/-! # Minkowski for actual subprobability restart measures with canonical joint densities -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

/-- Convert a finite positive density norm bound to its real measurable representative. -/
theorem belowFour_real_density_of_positive_bound {X : Type*} [MeasurableSpace X]
    (m mu : Measure X) [IsFiniteMeasure mu] (F : X → ℝ≥0∞) (hF : Measurable F)
    (hd : m.withDensity F = mu) (q K : ℝ) (hq : 0 < q) (hK : 0 ≤ K)
    (hn : positionPositiveNorm m q F ≤ ENNReal.ofReal K) :
    ∃ G : X → ℝ, Measurable G ∧ (∀ x, 0 ≤ G x) ∧
      mu = m.withDensity (fun x => ENNReal.ofReal (G x)) ∧
      MemLp G (ENNReal.ofReal q) m ∧ (eLpNorm G (ENNReal.ofReal q) m).toReal ≤ K := by
  obtain ⟨hG, hG0, hGd, hGi⟩ := position_density_real m mu F hF hd q
  have he : eLpNorm (fun x => (F x).toReal) (ENNReal.ofReal q) m =
      positionPositiveNorm m q F := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ne_of_gt (ENNReal.ofReal_pos.mpr hq)) ENNReal.ofReal_ne_top hG.aestronglyMeasurable,
      ENNReal.toReal_ofReal hq.le, hGi]
    rfl
  refine ⟨fun x => (F x).toReal, hG, hG0, hGd, ?_, ?_⟩
  · change eLpNorm _ _ _ < ⊤
    rw [he]
    exact hn.trans_lt ENNReal.ofReal_lt_top
  · rw [he]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hn).trans_eq
      (ENNReal.toReal_ofReal hK)

/-- Actual kernel mixtures preserve a uniform real Lq density bound under mass at most one. -/
theorem belowFour_density_subprobability_mixture {X : Type*} [MeasurableSpace X]
    [MeasurableSpace.CountableOrCountablyGenerated X Point]
    (nu : Measure X) [IsFiniteMeasure nu] (k : Kernel X Point) [IsFiniteKernel k]
    (q K : ℝ) (hq : 1 < q) (hK : 0 ≤ K) (hnu : nu univ ≤ 1)
    (hbound : ∀ᵐ x ∂nu, ∃ G : Point → ℝ,
      Measurable G ∧ (∀ z, 0 ≤ G z) ∧
      k x = volume.withDensity (fun z => ENNReal.ofReal (G z)) ∧
      MemLp G (ENNReal.ofReal q) volume ∧ (eLpNorm G (ENNReal.ofReal q) volume).toReal ≤ K) :
    ∃ G : Point → ℝ, Measurable G ∧ (∀ z, 0 ≤ G z) ∧
      k ∘ₘ nu = volume.withDensity (fun z => ENNReal.ofReal (G z)) ∧
      MemLp G (ENNReal.ofReal q) volume ∧ (eLpNorm G (ENNReal.ofReal q) volume).toReal ≤ K := by
  have : SigmaFinite (volume : Measure Point) := density_volume_sigmaFinite
  let F := positionKernelDensity k (volume : Measure Point)
  have hF := measurable_positionKernelDensity k (volume : Measure Point)
  have hd : ∀ᵐ x ∂nu, volume.withDensity (F x) = k x := by
    filter_upwards [hbound] with x hx
    obtain ⟨G, _, _, hGd, _, _⟩ := hx
    apply withDensity_positionKernelDensity
    rw [hGd]
    exact withDensity_absolutelyContinuous _ _
  have hp : ∀ᵐ x ∂nu, positionPositiveNorm volume q (F x) ≤ ENNReal.ofReal K := by
    filter_upwards [hbound, hd] with x hx hdx
    obtain ⟨G, hG, hG0, hGd, hGp, hGn⟩ := hx
    have h := positionPositiveNorm_of_density_le volume (F x)
      (hF.comp (measurable_const.prodMk measurable_id)) univ univ MeasurableSet.univ
      G hG hG0 (by simpa only [Measure.restrict_univ] using hdx.trans hGd)
      q K (by linarith) hK (by simpa only [Measure.restrict_univ] using hGp)
      (by simpa only [Measure.restrict_univ] using hGn)
    simpa only [Measure.restrict_univ] using h
  let M := fun z => ∫⁻ x, F x z ∂nu
  have hM : Measurable M := hF.lintegral_prod_left'
  have hm : volume.withDensity M = k ∘ₘ nu := by
    ext B hB
    rw [withDensity_apply _ hB, Measure.bind_apply hB k.aemeasurable]
    change (∫⁻ z in B, ∫⁻ x, F x z ∂nu ∂volume) = ∫⁻ x, k x B ∂nu
    rw [← lintegral_lintegral_swap (μ := nu) (ν := volume.restrict B)
      (f := F) hF.aemeasurable]
    apply lintegral_congr_ae
    filter_upwards [hd] with x hx
    rw [← withDensity_apply _ hB, hx]
  have hn := positionPositiveNorm_mixture_le nu volume F hF q hq (ENNReal.ofReal K) hp
  have hn' : positionPositiveNorm volume q M ≤ ENNReal.ofReal K :=
    hn.trans ((mul_le_mul_left hnu _).trans_eq (one_mul _))
  exact belowFour_real_density_of_positive_bound volume (k ∘ₘ nu) M hM hm q K
    (by linarith) hK hn'

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
