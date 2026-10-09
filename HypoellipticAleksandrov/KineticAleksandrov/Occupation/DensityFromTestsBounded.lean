module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.DensityFromTestsTruncation
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Sharp density norm bounds from bounded conjugate tests

This is the finite-measure restriction step of smooth-test duality. The density is
already given here; existence and absolute continuity are separate steps.
Adapted from `PDEFoundation.Measure.LpConjugateBoundFromTests`.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A sharp bound against every bounded measurable conjugate test forces the
tested function to belong to `Lʳ`, with the same norm bound. -/
theorem memLp_and_eLpNorm_le_of_bounded_conjugate_tests
    [IsFiniteMeasure μ] {r M : ℝ} (hr : 1 < r) (hM : 0 ≤ M)
    {g : α → ℝ} (hgMeas : Measurable g) (_hgInt : Integrable g μ)
    (htest : ∀ φ : α → ℝ, Measurable φ →
      (∃ C : ℝ, 0 ≤ C ∧ ∀ x, |φ x| ≤ C) →
      |∫ x, φ x * g x ∂μ| ≤
        M * (eLpNorm φ (ENNReal.ofReal (r / (r - 1))) μ).toReal) :
    MemLp g (ENNReal.ofReal r) μ ∧
      (eLpNorm g (ENNReal.ofReal r) μ).toReal ≤ M := by
  have hnormTrunc (n : ℕ) :
      (eLpNorm (truncatedAbs g n) (ENNReal.ofReal r) μ).toReal ≤ M := by
    let N := (eLpNorm (truncatedAbs g n) (ENNReal.ofReal r) μ).toReal
    have htestn := htest (signedTruncatedDualPower g r n)
      (signedTruncatedDualPower_measurable_bounded hgMeas hr n).1
      ⟨(n + 1 : ℝ) ^ (r - 1),
        Real.rpow_nonneg (by positivity) _,
        signedTruncatedDualPower_measurable_bounded hgMeas hr n |>.2⟩
    rw [integral_signedTruncatedDualPower_mul hgMeas hr n,
      eLpNorm_signedTruncatedDualPower hgMeas hr n] at htestn
    rw [← ENNReal.toReal_rpow] at htestn
    change |N ^ r| ≤ M * N ^ (r - 1) at htestn
    have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
    rw [abs_of_nonneg (Real.rpow_nonneg hN0 _)] at htestn
    by_cases hNz : N = 0
    · simpa [N, hNz] using hM
    · have hNpos : 0 < N := lt_of_le_of_ne hN0 (Ne.symm hNz)
      have hsplit : N ^ r = N * N ^ (r - 1) := by
        calc
          N ^ r = N ^ (1 + (r - 1)) := by
            congr 1
            ring
          _ = N ^ (1 : ℝ) * N ^ (r - 1) := Real.rpow_add hNpos _ _
          _ = N * N ^ (r - 1) := by rw [Real.rpow_one]
      rw [hsplit] at htestn
      exact le_of_mul_le_mul_right htestn (Real.rpow_pos_of_pos hNpos _)
  have htruncNormENN (n : ℕ) :
      eLpNorm (truncatedAbs g n) (ENNReal.ofReal r) μ ≤ ENNReal.ofReal M := by
    apply (ENNReal.toReal_le_toReal
      (memLp_truncatedAbs hgMeas n _).eLpNorm_ne_top ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal hM]
    exact hnormTrunc n
  have hlim (x : α) :
      Tendsto (fun n => truncatedAbs g n x) atTop (𝓝 |g x|) := by
    apply tendsto_atTop_of_eventually_const
      (i₀ := Nat.ceil |g x|)
    intro n hn
    rw [truncatedAbs, Set.indicator_of_mem]
    have hceil : |g x| ≤ Nat.ceil |g x| := Nat.le_ceil _
    exact hceil.trans (by exact_mod_cast (hn.trans (Nat.le_add_right n 1)))
  have habsNorm : eLpNorm (fun x => |g x|) (ENNReal.ofReal r) μ ≤
      ENNReal.ofReal M := by
    refine (Lp.eLpNorm_lim_le_liminf_eLpNorm
      (fun n => (measurable_truncatedAbs hgMeas n).aestronglyMeasurable)
      (fun x => |g x|) (continuous_abs.measurable.comp hgMeas).aestronglyMeasurable
      (ae_of_all _ hlim)).trans ?_
    exact liminf_le_of_frequently_le (Frequently.of_forall htruncNormENN)
  have habsLp : MemLp (fun x => |g x|) (ENNReal.ofReal r) μ := by
    exact habsNorm.trans_lt ENNReal.ofReal_lt_top
  have hnormEq : eLpNorm g (ENNReal.ofReal r) μ =
      eLpNorm (fun x => |g x|) (ENNReal.ofReal r) μ := by
    apply eLpNorm_congr_norm_ae hgMeas.aestronglyMeasurable
      (continuous_abs.measurable.comp hgMeas).aestronglyMeasurable
    exact ae_of_all _ fun x => by simp [Real.norm_eq_abs]
  have hgLp : MemLp g (ENNReal.ofReal r) μ := by
    rw [memLp_iff, hnormEq]
    exact habsLp.eLpNorm_lt_top
  refine ⟨hgLp, ?_⟩
  rw [hnormEq]
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top habsNorm
  simpa [ENNReal.toReal_ofReal hM] using hreal

end

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
