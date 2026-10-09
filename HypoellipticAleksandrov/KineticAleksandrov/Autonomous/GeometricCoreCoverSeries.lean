module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GeometricCoreCover
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GeometricCoreCoverMeasure
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-! # Summation and scaling of the improved geometric band bounds -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory
open scoped ENNReal

/-- The positive geometric power appearing in the source cover. -/
def geometricBandPower (delta : ℝ) (j : ℕ) : ℝ :=
  (4 * (7 / 8 : ℝ) ^ j) ^ delta

/-- The geometric band powers are summable exactly in the positive-exponent regime. -/
theorem geometricBandPower_summable (delta : ℝ) (hd : 0 < delta) :
    Summable (geometricBandPower delta) := by
  have he (j : ℕ) : geometricBandPower delta j =
      (4 : ℝ) ^ delta * ((7 / 8 : ℝ) ^ delta) ^ j := by
    unfold geometricBandPower
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num), mul_comm (j : ℝ) delta,
      Real.rpow_mul (by norm_num), Real.rpow_natCast]
  have hefun := funext he
  rw [hefun]
  apply Summable.mul_left
  apply summable_geometric_of_lt_one
  · positivity
  · exact Real.rpow_lt_one (by norm_num) (by norm_num) hd

/-- The geometric band sum is strictly positive. -/
theorem geometricBandPower_tsum_pos (delta : ℝ) (hd : 0 < delta) :
    0 < ∑' j, geometricBandPower delta j := by
  exact (geometricBandPower_summable delta hd).tsum_pos
    (fun j => by unfold geometricBandPower; positivity) 0
    (by unfold geometricBandPower; positivity)

/-- Sum both velocity signs, retaining the source uniform power of R. -/
theorem geometricBandPower_sum (C R delta k : ℝ) (hC : 0 ≤ C) (hR : 0 < R)
    (hd : 0 < delta) :
    (∑' i : Bool × ℕ, ENNReal.ofReal (C * R ^ k * geometricBandPower delta i.2)) =
      ENNReal.ofReal (2 * C * (∑' j, geometricBandPower delta j) * R ^ k) := by
  have hs := (geometricBandPower_summable delta hd).mul_left (C * R ^ k)
  have hn (j : ℕ) : 0 ≤ C * R ^ k * geometricBandPower delta j := by
    unfold geometricBandPower; positivity
  rw [ENNReal.tsum_prod']
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_bool, two_nsmul]
  rw [← ENNReal.ofReal_tsum_of_nonneg hn hs, ← ENNReal.ofReal_add (tsum_nonneg hn)
    (tsum_nonneg hn), tsum_mul_left]
  congr 1
  ring

/-- A finite q-power integral bound yields the source real Lq norm bound. -/
theorem density_norm_of_power_bound {X : Type*} [MeasurableSpace X]
    (m : Measure X) (g : X → ℝ) (hgm : Measurable g)
    (q K : ℝ) (hq : 0 < q) (hK : 0 ≤ K)
    (hint : ∫⁻ x, ‖g x‖ₑ ^ q ∂m ≤ ENNReal.ofReal K) :
    MemLp g (ENNReal.ofReal q) m ∧
      (eLpNorm g (ENNReal.ofReal q) m).toReal ≤ K ^ (1 / q) := by
  have he : eLpNorm g (ENNReal.ofReal q) m =
      (∫⁻ x, ‖g x‖ₑ ^ q ∂m) ^ (1 / q) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top
      hgm.aestronglyMeasurable, ENNReal.toReal_ofReal hq.le]
  have hn : eLpNorm g (ENNReal.ofReal q) m ≤ ENNReal.ofReal (K ^ (1 / q)) := by
    rw [he]
    exact (ENNReal.rpow_le_rpow hint (by positivity)).trans_eq
      (ENNReal.ofReal_rpow_of_nonneg hK (by positivity))
  refine ⟨hn.trans_lt ENNReal.ofReal_lt_top, ?_⟩
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hn).trans_eq
    (ENNReal.toReal_ofReal (Real.rpow_nonneg hK _))

/-- Taking the q-th root gives exactly the homogeneous source power 6/q-4. -/
theorem geometricBandPower_root (C R delta q : ℝ) (hC : 0 ≤ C) (hR : 0 < R)
    (hd : 0 < delta) (hq : 0 < q) :
    (2 * C * (∑' j, geometricBandPower delta j) * R ^ (6 - 4 * q)) ^ (1 / q) =
      (2 * C * (∑' j, geometricBandPower delta j)) ^ (1 / q) * R ^ (6 / q - 4) := by
  have hs := (geometricBandPower_tsum_pos delta hd).le
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hR.le]
  congr 2
  field_simp

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
