module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoxConcentrationHeadline
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionPowerSum
import Mathlib.Tactic

/-! # Applying box concentration to a truncated source time slab -/

public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- A short slab beginning in bin `j` retains the bin's concentration decay. -/
theorem position_concentration_slab_le
    (f : ℝ → ℝ) (B g r b : ℝ) (j : ℕ) (hB : 0 ≤ B) (hg : 0 ≤ g) (hr : 0 < r)
    (hab : (j : ℝ) * r ^ 2 ≤ b) (hlen : b - (j : ℝ) * r ^ 2 ≤ r ^ 2)
    (hi : Integrable f (volume.restrict (Ioc ((j : ℝ) * r ^ 2) b)))
    (hf : ∀ t : ℝ, 0 ≤ t → f t ≤ B * (1 + t / r ^ 2) ^ (-g / 2)) :
    f b + r ^ (-2 : ℤ) * (∫ t in Ioc ((j : ℝ) * r ^ 2) b, f t) ≤
      2 * B * (1 + (j : ℝ)) ^ (-g / 2) := by
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have ha : 0 ≤ (j : ℝ) * r ^ 2 := mul_nonneg (Nat.cast_nonneg j) hr2.le
  let D := B * (1 + (j : ℝ)) ^ (-g / 2)
  have hD : 0 ≤ D := mul_nonneg hB (Real.rpow_nonneg (by positivity) _)
  have hbound (t : ℝ) (ht : (j : ℝ) * r ^ 2 ≤ t) : f t ≤ D := by
    apply (hf t (ha.trans ht)).trans
    apply mul_le_mul_of_nonneg_left _ hB
    have hratio : (j : ℝ) ≤ t / r ^ 2 := (le_div_iff₀ hr2).mpr ht
    exact Real.rpow_le_rpow_of_nonpos (by positivity : 0 < 1 + (j : ℝ))
      (by linarith) (by linarith)
  have hb := hbound b hab
  have hiBound : (∫ t in Ioc ((j : ℝ) * r ^ 2) b, f t) ≤
      D * (b - (j : ℝ) * r ^ 2) := by
    have h := integral_mono_ae hi (integrable_const D)
      ((ae_restrict_mem measurableSet_Ioc).mono fun t ht => hbound t ht.1.le)
    simpa only [integral_const, smul_eq_mul, Measure.real,
      Measure.restrict_apply_univ, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab),
      mul_comm] using h
  have hlenBound := mul_le_mul_of_nonneg_left hlen hD
  have hz : 0 ≤ r ^ (-2 : ℤ) := zpow_nonneg hr.le _
  have hnum := mul_le_mul_of_nonneg_left (hiBound.trans hlenBound) hz
  have he : r ^ (-2 : ℤ) * (D * r ^ 2) = D := by
    simp only [zpow_neg, zpow_ofNat]
    field_simp
  rw [he] at hnum
  calc
    _ ≤ D + D := add_le_add hb hnum
    _ = _ := by dsimp only [D]; ring

/-- Real full-space box probabilities are integrable on every finite time slab. -/
theorem position_box_probability_integrable (E : FullSpaceEvolution) (z : Z)
    (A0 r Y a b : ℝ) :
    Integrable (fun t => (kernelXV E (Real.toNNReal t) z (box A0 r Y)).toReal)
      (volume.restrict (Ioc a b)) := by
  have hm := (kernelXV_realTime_measurable E z _ (box_measurable A0 r Y)).ennreal_toReal
  apply Integrable.mono' (integrable_const (1 : ℝ)) hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
  have h : kernelXV E (Real.toNNReal t) z (box A0 r Y) ≤ 1 :=
    (measure_mono (subset_univ (box A0 r Y))).trans
      (kernelXV_mass_le_one E (Real.toNNReal t) z)
  simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top h

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
