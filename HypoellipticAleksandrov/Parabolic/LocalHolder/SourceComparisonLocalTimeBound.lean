module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalTimeEnergy
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalCutoff
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Bounding the time term in localized value energy

Quadratic testing bounds the time pairing using only the square of the solution, rather
than any derivative bound on the approximation sequence.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open MeasureTheory Set

/-- Quadratic testing bounds time energy by the value integral and a cutoff derivative bound. -/
theorem integral_local_time_energy_le {d : ℕ}
    {U : Set (TimeVelocity d)} (hU : IsOpen U)
    (u ρ : TimeVelocity d → ℝ) (hu : IsScalarC12On u U)
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hc : HasCompactSupport ρ)
    (hsub : tsupport ρ ⊆ U) (K : ℝ)
    (hq : IntegrableOn (fun z => u z ^ 2) U)
    (hK : ∀ z ∈ U, |timeDerivative (fun y => ρ y ^ 2) z| ≤ K) :
    (∫ z in U, scalarTimeDerivative u z * u z * ρ z ^ 2) ≤
      (K / 2) * ∫ z in U, u z ^ 2 := by
  have hχ : ContDiff ℝ (⊤ : ℕ∞) (fun z => ρ z ^ 2) := hρ.pow 2
  have hχeq : (fun z => ρ z ^ 2) = ρ * ρ := by
    funext z
    exact pow_two _
  have hcχ : HasCompactSupport (fun z => ρ z ^ 2) := by
    rw [hχeq]
    exact HasCompactSupport.mul_left hc
  have hsχ : tsupport (fun z => ρ z ^ 2) ⊆ U := by
    simpa only [pow_two] using
      (tsupport_mul_subset_left (f := ρ) (g := ρ)).trans hsub
  have hw : IntegrableOn
      (fun z => scalarTimeDerivative u z * u z * ρ z ^ 2) U :=
    (integrable_local_cutoff_square_mul hU
      (fun z => scalarTimeDerivative u z * u z) ρ
      (hu.continuousOn_scalarTimeDerivative.mul hu.continuousOn)
      hρ.continuous hc hsub).restrict
  have htest := integral_square_mul_timeDerivative_eq hu
    (fun z => ρ z ^ 2) hχ hcχ hsχ
  have hdt : IntegrableOn
      (fun z => u z ^ 2 * timeDerivative (fun y => ρ y ^ 2) z) U := by
    have hdcont := hχ.continuous_fderiv (by simp)
    have hd : Continuous (timeDerivative (fun y => ρ y ^ 2)) :=
      hdcont.clm_apply continuous_const
    exact hq.mul_bdd hd.aestronglyMeasurable.restrict
      (ae_restrict_of_forall_mem hU.measurableSet
        (fun z hz => by simpa only [Real.norm_eq_abs] using hK z hz))
  have hpoint : ∀ᵐ z ∂volume.restrict U,
      -(u z ^ 2 * timeDerivative (fun y => ρ y ^ 2) z) ≤ K * u z ^ 2 := by
    apply ae_restrict_of_forall_mem hU.measurableSet
    intro z hz
    have hd := (neg_le_abs (timeDerivative (fun y => ρ y ^ 2) z)).trans (hK z hz)
    convert mul_le_mul_of_nonneg_right hd (sq_nonneg (u z)) using 1
    ring
  have hb := integral_mono_ae hdt.neg (hq.const_mul K) hpoint
  have htval : (∫ z in U, 2 * u z * scalarTimeDerivative u z * ρ z ^ 2) =
      2 * ∫ z in U, scalarTimeDerivative u z * u z * ρ z ^ 2 := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z => by ring)
  simp only [Pi.neg_apply] at hb
  rw [integral_neg, integral_const_mul, htest, htval] at hb
  linarith only [hb]

end HypoellipticAleksandrov.Parabolic.LocalHolder
