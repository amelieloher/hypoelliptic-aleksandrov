module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AnnularNormalizationAnnuli
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AnnularNormalizationCutoff
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureFubini
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.Tactic

/-! # Strictly positive annular normalization of homogeneous Radon measures -/

@[expose] public section
noncomputable section
open Set MeasureTheory
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- A compact ambient cutoff away from the origin remains compact on the punctured carrier. -/
theorem bellman_annular_test_compact (chi : (ℝ × ℝ) → ℝ) (hc : HasCompactSupport chi)
    (hs : tsupport chi ⊆ {q | 1 / 2 < bellmanGauge q ∧ bellmanGauge q < 4}) :
    HasCompactSupport (fun q : BellmanPuncturedPlane => chi q.val) := by
  apply bellman_test_compact_subtype hc
  intro q hq he
  have h := (hs hq).1
  rw [he] at h
  norm_num [bellmanGauge, bellmanGaugePower] at h

/-- The common cutoff has a finite strictly positive normalizing integral. -/
theorem bellman_annular_integral_pos (beta : ℝ) (mu : Measure BellmanPuncturedPlane)
    (hmu : IsBellmanRadon mu) (hn : mu ≠ 0) (hd : HasBellmanDensityDegree beta mu)
    (chi : (ℝ × ℝ) → ℝ) (hc : Continuous chi) (hcompact : HasCompactSupport chi)
    (hs : tsupport chi ⊆ {q | 1 / 2 < bellmanGauge q ∧ bellmanGauge q < 4})
    (hpos : ∀ q, 0 ≤ chi q) (hone : ∀ q, 1 ≤ bellmanGauge q →
      bellmanGauge q ≤ 2 → chi q = 1) :
    0 < ∫ q, chi q.val ∂mu := by
  let := hmu.1
  have hi : Integrable (fun q : BellmanPuncturedPlane => chi q.val) mu :=
    (hc.comp continuous_subtype_val).integrable_of_hasCompactSupport
    (bellman_annular_test_compact chi hcompact hs)
  apply (integral_pos_iff_support_of_nonneg
    (fun q : BellmanPuncturedPlane => hpos q.val) hi).mpr
  have hm := bellmanUnitAnnulus_measure_ne_zero beta mu hn hd
  have hsupp : bellmanUnitAnnulus ⊆ Function.support
      (fun q : BellmanPuncturedPlane => chi q.val) := by
    intro q hq
    exact Function.mem_support.mpr (by rw [hone _ hq.1 hq.2]; norm_num)
  exact lt_of_lt_of_le (pos_iff_ne_zero.mpr hm) (measure_mono hsupp)

/-- Dividing by the proved positive annular mass gives integral one. -/
theorem bellman_annular_normalize (mu : Measure BellmanPuncturedPlane)
    (chi : (ℝ × ℝ) → ℝ) (hp : 0 < ∫ q, chi q.val ∂mu) :
    ∃ c : ℝ, 0 < c ∧ ∫ q, chi q.val ∂(ENNReal.ofReal c • mu) = 1 := by
  refine ⟨(∫ q, chi q.val ∂mu)⁻¹, inv_pos.mpr hp, ?_⟩
  rw [integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr hp.le), smul_eq_mul,
    inv_mul_cancel₀ hp.ne']

end HypoellipticAleksandrov.KineticAleksandrov
