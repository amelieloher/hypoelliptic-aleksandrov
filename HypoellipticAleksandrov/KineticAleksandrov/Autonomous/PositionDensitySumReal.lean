module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionDensitySumPower
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionDensitySumFinite
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GeometricCoreCoverSeries
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! # Real representatives of the actual positive Green density -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter
open scoped ENNReal

/-- A finite measure's positive density is finite almost everywhere. -/
theorem position_density_finite {X : Type*} [MeasurableSpace X]
    (m mu : Measure X) [IsFiniteMeasure mu] (F : X → ℝ≥0∞) (hF : Measurable F)
    (hd : m.withDensity F = mu) : ∀ᵐ x ∂m, F x ≠ ⊤ := by
  have hi : (∫⁻ x, F x ∂m) ≠ ⊤ := by
    have he : (m.withDensity F) univ = ∫⁻ x, F x ∂m := by
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [← he, hd]
    exact measure_ne_top _ _
  exact (ae_lt_top hF hi).mono (fun _ h => h.ne)

/-- The real representative has exactly the original positive density and power integral. -/
theorem position_density_real {X : Type*} [MeasurableSpace X]
    (m mu : Measure X) [IsFiniteMeasure mu] (F : X → ℝ≥0∞) (hF : Measurable F)
    (hd : m.withDensity F = mu) (q : ℝ) :
    Measurable (fun x => (F x).toReal) ∧ (∀ x, 0 ≤ (F x).toReal) ∧
      mu = m.withDensity (fun x => ENNReal.ofReal (F x).toReal) ∧
      (∫⁻ x, ‖(F x).toReal‖ₑ ^ q ∂m) = ∫⁻ x, F x ^ q ∂m := by
  have hf := position_density_finite m mu F hF hd
  refine ⟨hF.ennreal_toReal, fun _ => ENNReal.toReal_nonneg, ?_, ?_⟩
  · rw [← hd]
    apply withDensity_congr_ae
    exact hf.mono (fun _ h => (ENNReal.ofReal_toReal h).symm)
  · apply lintegral_congr_ae
    filter_upwards [hf] with x hx
    rw [Real.enorm_toReal hx]

/-- The actual active mixture has a real density with precisely the source power bound. -/
theorem position_density_sum (hpush : PushforwardStatement) (htail : RestartTailStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (q : ℝ) (hq : 1 < q ∧ q < 3 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam)
      (c : Clock) (_hc : |c.vbar| = 2 * c.r) (s x : ℝ)
      (nu : Measure Point) [IsFiniteMeasure nu],
      (∀ᵐ e ∂nu, s ≤ e.time ∧ e.velocity 0 ∈ c.active) →
      ∃ G : Point → ℝ, Measurable G ∧ (∀ z, 0 ≤ G z) ∧
        enlargedActiveGreen hH hLE hlam hLam A c nu =
          volume.withDensity (fun z => ENNReal.ofReal (G z)) ∧
        MemLp G (ENNReal.ofReal q) volume ∧
        (∫⁻ z, ‖G z‖ₑ ^ q ∂volume) ≤ ENNReal.ofReal (C * c.r ^ (6 - 4 * q)) *
          ∑' a : ℕ × ℤ, nu (enlargedStartCell c s x a.1 a.2) ^ q := by
  obtain ⟨C, hC, hd⟩ := position_density_power_sum hpush htail hH hLE hlam hLam q hq
  refine ⟨C, hC, ?_⟩
  intro A c hc s x nu hfinite hnu
  have hq0 : 0 < q := by linarith [hq.1]
  let F := positionMixtureDensity hH hLE hlam hLam A c nu
  have hF := measurable_positionMixtureDensity hH hLE hlam hLam A c nu
  have hm := withDensity_positionMixtureDensity hpush hH hLE hlam hLam A c nu
  have : IsFiniteMeasure (enlargedActiveGreen hH hLE hlam hLam A c nu) := by
    unfold enlargedActiveGreen
    infer_instance
  obtain ⟨hG, hG0, hGd, hGi⟩ := position_density_real volume
    (enlargedActiveGreen hH hLE hlam hLam A c nu) F hF hm q
  have hbound := hd A c hc s x nu hnu
  have hsum := enlargedStartCell_power_sum_le nu c s x q hq.1.le
    (hnu.mono (fun _ h => h.1))
  have hsumfinite : (∑' a : ℕ × ℤ, nu (enlargedStartCell c s x a.1 a.2) ^ q) < ⊤ :=
    hsum.trans_lt (ENNReal.rpow_lt_top_of_nonneg (by linarith [hq.1]) (measure_ne_top _ _))
  have hi : (∫⁻ z, ‖(F z).toReal‖ₑ ^ q ∂volume) < ⊤ := by
    rw [hGi]
    exact hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsumfinite)
  refine ⟨fun z => (F z).toReal, hG, hG0, hGd, ?_, ?_⟩
  · change eLpNorm (fun z => (F z).toReal) (ENNReal.ofReal q) volume < ⊤
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal 
      (ne_of_gt (ENNReal.ofReal_pos.mpr hq0)) ENNReal.ofReal_ne_top
      hG.aestronglyMeasurable, ENNReal.toReal_ofReal (by linarith : 0 ≤ q)]
    exact ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.mpr hq0.le) hi.ne
  · rwa [hGi]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
