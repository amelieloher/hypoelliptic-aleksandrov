module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AxisAnnihilationJets
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureFubini
import Mathlib.Tactic

/-! # Axis-supported stationarity tested with a normal position factor -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- Ellipticity passes zero off-axis mass from the first measure to the second. -/
theorem bellman_axis_support_comparison (R : ℝ) (μ η : Measure BellmanPuncturedPlane)
    (hhi : η ≤ ENNReal.ofReal R • μ) (haxis : μ {q | q.val.1 ≠ 0} = 0) :
    η {q | q.val.1 ≠ 0} = 0 := by
  have he := hhi {q | q.val.1 ≠ 0}
  rw [Measure.smul_apply, smul_eq_mul, haxis, mul_zero] at he
  exact le_antisymm he bot_le

/-- A normal-factor test isolates the nonnegative velocity-weighted first measure on the axis. -/
theorem bellman_axis_velocity_test_zero (μ η : Measure BellmanPuncturedPlane)
    (hstationary : IsBellmanStationaryAdjointPair μ η)
    (haxisμ : μ {q | q.val.1 ≠ 0} = 0) (haxisη : η {q | q.val.1 ≠ 0} = 0)
    (χ : ℝ × ℝ → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ {q : ℝ × ℝ | q ≠ (0, 0)}) :
    (∫ q : BellmanPuncturedPlane, q.val.2 ^ 2 * χ q.val ∂μ) = 0 := by
  let g := fun q : ℝ × ℝ => q.2 * χ q
  let φ := fun q : ℝ × ℝ => q.1 * g q
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := contDiff_snd.mul hχ
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := contDiff_fst.mul hg
  have hcφ : HasCompactSupport φ := (hc.mul_left).mul_left
  have hsφ : tsupport φ ⊆ {q : ℝ × ℝ | q ≠ (0, 0)} :=
    tsupport_mul_subset_right.trans (tsupport_mul_subset_right.trans hs)
  have he := hstationary φ hφ hcφ hsφ
  have haμ : ∀ᵐ q ∂μ, q.val.1 = 0 := by simpa only [ae_iff] using haxisμ
  have haη : ∀ᵐ q ∂η, q.val.1 = 0 := by simpa only [ae_iff] using haxisη
  have h1 : (∫ q : BellmanPuncturedPlane,
      q.val.2 * fderiv ℝ φ q.val (1, 0) ∂μ) =
      ∫ q : BellmanPuncturedPlane, q.val.2 ^ 2 * χ q.val ∂μ := by
    apply integral_congr_ae
    filter_upwards [haμ] with q hq
    change q.val.2 * fderiv ℝ (fun z => z.1 * g z) q.val (1, 0) = _
    rw [bellman_position_mul_fderiv g hg, hq]
    dsimp [g]
    ring
  have h2 : (∫ q : BellmanPuncturedPlane,
      fderiv ℝ (fun z => fderiv ℝ φ z (0, 1)) q.val (0, 1) ∂η) = 0 := by
    calc
      _ = ∫ _q : BellmanPuncturedPlane, (0 : ℝ) ∂η := by
        apply integral_congr_ae
        filter_upwards [haη] with q hq
        change fderiv ℝ (fun z => fderiv ℝ (fun w => w.1 * g w) z (0, 1))
          q.val (0, 1) = 0
        rw [bellman_position_mul_second_velocity g hg, hq, zero_mul]
      _ = 0 := integral_zero _ _
  rw [h1, h2, add_zero] at he
  exact he

end HypoellipticAleksandrov.KineticAleksandrov
