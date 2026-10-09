module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.GreenIntegrals
public import HypoellipticAleksandrov.KineticAleksandrov.Green.Gluing

/-! # Uniform infinite-horizon norm from killed slab estimates -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory
open HypoellipticAleksandrov.KineticAleksandrov.Green
open scoped ENNReal

/-- The uniform constant obtained by logarithmic averaging of the killed moment. -/
def killedGreenConstant (A δ k q : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal A * (∫⁻ T in Ioi (0 : ℝ), ENNReal.ofReal
    (T ^ (δ - 1) * Real.exp (-k * T))) *
      (ENNReal.ofReal (Real.log 2))⁻¹) ^ (1 / q)

/-- The averaging constant is finite. -/
theorem killedGreenConstant_ne_top {A δ k q : ℝ}
    (hδ : 0 < δ) (hk : 0 < k) (hq : 0 < q) :
    killedGreenConstant A δ k q ≠ ⊤ := by
  unfold killedGreenConstant
  apply ENNReal.rpow_ne_top_of_nonneg (by positivity)
  apply ENNReal.mul_ne_top
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (killed_power_moment_finite hδ hk).ne
  · exact ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr
      (Real.log_pos one_lt_two)).ne'

/-- Killed local bounds imply the global norm, with no finite horizon factor. -/
theorem killed_green_norm_bound {d : ℕ} (G : GreenCarrier d → ℝ≥0∞)
    (hGm : Measurable G) (A δ k q : ℝ) (M : ℝ≥0∞) (hq : 0 < q)
    (hslab : ∀ T : ℝ, 0 < T →
      ∫⁻ p in slabSet T, G p ^ q ∂greenLebesgue d ≤
        ENNReal.ofReal A * M ^ q *
          ENNReal.ofReal (T ^ δ * Real.exp (-k * T))) :
    eLpNorm G (ENNReal.ofReal q) (greenLebesgue d) ≤
      killedGreenConstant A δ k q * M := by
  let ν := (greenLebesgue d).withDensity (fun p => G p ^ q)
  have hlog := log_mul_measure_univ_le ν
    (measurable_subtype_coe.comp measurable_fst) (fun p => p.1.2.1)
  have hν : ∀ T : ℝ, 0 < T → ν (slabSet T) ≤
      ENNReal.ofReal A * M ^ q *
        ENNReal.ofReal (T ^ δ * Real.exp (-k * T)) := by
    intro T hT
    dsimp only [ν]
    rw [withDensity_apply _ (measurableSet_slabSet T)]
    exact hslab T hT
  have hint : ENNReal.ofReal (Real.log 2) * ν univ ≤
      (ENNReal.ofReal A * M ^ q) * (∫⁻ T in Ioi (0 : ℝ), ENNReal.ofReal
        (T ^ (δ - 1) * Real.exp (-k * T))) := by
    refine hlog.trans ?_
    rw [← lintegral_inv_killed_power]
    refine setLIntegral_mono' measurableSet_Ioi fun T hT => ?_
    exact mul_le_mul_right (hν T hT) _
  have hL0 : ENNReal.ofReal (Real.log 2) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.log_pos one_lt_two)).ne'
  have hbound := (ENNReal.mul_le_iff_le_inv hL0 ENNReal.ofReal_ne_top).mp hint
  have hp0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr hq).ne'
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top
    hGm.aestronglyMeasurable, ENNReal.toReal_ofReal hq.le]
  simp only [enorm_eq_self]
  have hmass : (∫⁻ p, G p ^ q ∂greenLebesgue d) = ν univ := by
    dsimp only [ν]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [hmass]
  refine (ENNReal.rpow_le_rpow hbound (by positivity : 0 ≤ 1 / q)).trans (le_of_eq ?_)
  unfold killedGreenConstant
  rw [show (ENNReal.ofReal (Real.log 2))⁻¹ *
      ((ENNReal.ofReal A * M ^ q) * (∫⁻ T in Ioi (0 : ℝ), ENNReal.ofReal
        (T ^ (δ - 1) * Real.exp (-k * T)))) =
      (ENNReal.ofReal A * (∫⁻ T in Ioi (0 : ℝ), ENNReal.ofReal
        (T ^ (δ - 1) * Real.exp (-k * T))) *
        (ENNReal.ofReal (Real.log 2))⁻¹) * M ^ q by ring]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1 / q),
    ← ENNReal.rpow_mul, mul_one_div_cancel hq.ne', ENNReal.rpow_one]

end HypoellipticAleksandrov.KineticAleksandrov.Interval
