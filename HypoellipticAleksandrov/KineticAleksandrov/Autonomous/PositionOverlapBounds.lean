module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapMixture
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.Tactic

/-! # Transferring source real density bounds to the canonical positive density -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter
open scoped ENNReal

/-- A chosen positive density has no greater norm than any nonnegative representative. -/
theorem positionPositiveNorm_of_density_le {X : Type*} [MeasurableSpace X]
    (m : Measure X) [SigmaFinite m] (F : X → ℝ≥0∞) (hF : Measurable F)
    (S E : Set X) (hS : MeasurableSet S) (G : X → ℝ)
    (hG : Measurable G) (hG0 : ∀ x, 0 ≤ G x)
    (hd : m.withDensity F = (m.restrict S).withDensity (fun x => ENNReal.ofReal (G x)))
    (q K : ℝ) (hq : 0 < q) (hK : 0 ≤ K)
    (hp : MemLp G (ENNReal.ofReal q) (m.restrict E))
    (hn : (eLpNorm G (ENNReal.ofReal q) (m.restrict E)).toReal ≤ K) :
    positionPositiveNorm (m.restrict E) q F ≤ ENNReal.ofReal K := by
  have heq : m.withDensity F =
      m.withDensity (S.indicator (fun x => ENNReal.ofReal (G x))) := by
    rwa [withDensity_indicator hS]
  have he := (withDensity_eq_iff_of_sigmaFinite hF.aemeasurable
    (hG.ennreal_ofReal.indicator hS).aemeasurable).mp heq
  have hle : ∀ᵐ x ∂m.restrict E, F x ≤ ENNReal.ofReal (G x) := by
    filter_upwards [ae_restrict_of_ae he] with x hx
    rw [hx]
    by_cases hxS : x ∈ S
    · rw [indicator_of_mem hxS]
    · rw [indicator_of_notMem hxS]
      exact zero_le
  have hnorm : positionPositiveNorm (m.restrict E) q F ≤
      eLpNorm G (ENNReal.ofReal q) (m.restrict E) := by
    rw [eLpNorm_eq_eLpNorm' (by positivity) ENNReal.ofReal_ne_top
      hp.aestronglyMeasurable, ENNReal.toReal_ofReal hq.le,
      eLpNorm'_eq_lintegral_enorm]
    unfold positionPositiveNorm
    apply ENNReal.rpow_le_rpow _ (one_div_nonneg.mpr hq.le)
    apply lintegral_mono_ae
    filter_upwards [hle] with x hx
    have he : ‖G x‖ₑ = ENNReal.ofReal (G x) := by
      simp only [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hG0 x)]
    rw [he]
    exact ENNReal.rpow_le_rpow hx hq.le
  exact hnorm.trans ((ENNReal.le_ofReal_iff_toReal_le hp.ne hK).2 hn)

/-- The canonical active density obeys precisely the source restarted tail estimate. -/
theorem positionActiveDensity_tail (hpush : PushforwardStatement)
    (htail : RestartTailStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (q : ℝ) (hq : 1 < q ∧ q < 3 / 2) :
    ∃ C c₀ : ℝ, 0 < C ∧ 0 < c₀ ∧ ∀ (A : SmoothAutonomous lam Lam)
      (c : Clock) (e : Point) (_he : e.velocity 0 ∈ c.active) (t : ℝ),
      0 ≤ t →
      positionPositiveNorm
        (volume.restrict {p | e.time + t ≤ p.time ∧ p.velocity 0 ∈ c.active}) q
        (positionActiveDensity hH hLE hlam hLam A c e) ≤
          ENNReal.ofReal (C * Real.exp (-c₀ * t / c.r ^ 2) * c.r ^ (6 / q - 4)) := by
  have : SigmaFinite (volume : Measure Point) := density_volume_sigmaFinite
  obtain ⟨C, c₀, hC, hc, hd⟩ := htail hH hLE lam Lam hlam hLam q hq
  refine ⟨C, c₀, hC, hc, ?_⟩
  intro A c e he t ht
  obtain ⟨G, hG, hGt⟩ := hd A c e he
  have hdens := (withDensity_positionActiveDensity hpush hH hLE hlam hLam A c e).trans
    ((enlargedActiveGreenKernel_apply hH hLE hlam hLam A c e he).trans hG.2.2)
  apply positionPositiveNorm_of_density_le volume _
    ((measurable_positionActiveDensity hH hLE hlam hLam A c).comp
      (measurable_const.prodMk measurable_id)) (densityClockStrip c e) _
      (by
        exact (isOpen_lt continuous_const continuous_time).measurableSet.inter
          (isOpen_Ioo.measurableSet.preimage
            ((continuous_apply 0).comp continuous_velocity).measurable))
      G hG.1 hG.2.1 hdens q _ (by linarith [hq.1])
      (mul_nonneg (mul_nonneg hC.le (Real.exp_pos _).le)
        (Real.rpow_nonneg c.positive.le _))
      (hGt t ht).1 (hGt t ht).2

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
