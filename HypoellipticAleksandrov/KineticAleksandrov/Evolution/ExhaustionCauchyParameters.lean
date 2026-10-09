module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCauchy
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Choosing the comparison parameters

The growth-face and collar errors tend to zero together. This numerical lemma
chooses the common inner cylinder before choosing approximation indices.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open Filter Set
open scoped Topology

/-- The concrete growth/collar error can be made arbitrarily small, with any prescribed
inner-radius tolerance and transported cutoff. -/
theorem exists_small_dirichlet_comparison_parameters
    {κ d δ0 r0 C M e : ℝ} (_hκ : 0 < κ) (hd : 0 < d) (hδ0 : 0 < δ0)
    (hr0 : 0 < r0) (hC : 0 ≤ C) (hM : 0 ≤ M) (he : 0 < e) (S0 : ℝ) :
    ∃ δ A S : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ < r0 ∧ 0 < A ∧ A ≤ d ∧
      3 / 2 * A < δ ∧ S0 ^ 2 ≤ S ^ 2 ∧
      2 * C * (M / (1 + S ^ 2) + barrierW κ (δ + 3 / 2 * A) / barrierW κ d) < e := by
  let q (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
  have hq : Tendsto q atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hw : Continuous (barrierW κ) := by unfold barrierW; fun_prop
  have harg : Tendsto (fun j => q j + 3 / 2 * (q j / 4)) atTop (𝓝 0) := by
    convert hq.add (tendsto_const_nhds.mul (hq.div_const 4)) using 1
    norm_num
  have herr : Tendsto (fun j =>
      2 * C * (M * q j + barrierW κ (q j + 3 / 2 * (q j / 4)) / barrierW κ d))
      atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := 2 * C)).mul
      (((tendsto_const_nhds (x := M)).mul hq).add ((hw.tendsto 0).comp harg |>.div_const
        (barrierW κ d)))
    simpa only [Function.comp_def, barrierW, mul_zero, Real.exp_zero, sub_self,
      zero_div, add_zero] using h
  have hjS : ∀ᶠ j : ℕ in atTop, |S0| < (j : ℝ) + 1 :=
    (tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop |S0|)).mono
      fun j hj => by linarith
  obtain ⟨j, hjδ, hjr, hjd, hjS, hje⟩ :=
    (hq.eventually (gt_mem_nhds hδ0)).and
      ((hq.eventually (gt_mem_nhds hr0)).and
        ((hq.eventually (gt_mem_nhds hd)).and (hjS.and
          (herr.eventually (gt_mem_nhds he))))) |>.exists
  have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hqpos : 0 < q j := by dsimp [q]; positivity
  have hden : (j : ℝ) + 1 ≤ 1 + ((j : ℝ) + 1) ^ 2 := by nlinarith
  have hsmall : M / (1 + ((j : ℝ) + 1) ^ 2) ≤ M * q j := by
    dsimp only [q]
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left hM (by positivity) hden
  refine ⟨q j, q j / 4, (j : ℝ) + 1, hqpos, hjδ.le, hjr,
    (by positivity), (by linarith), (by linarith), ?_, ?_⟩
  · nlinarith [sq_abs S0, abs_nonneg S0]
  · exact (mul_le_mul_of_nonneg_left (add_le_add hsmall (le_refl _))
      (by positivity)).trans_lt hje

end HypoellipticAleksandrov.KineticAleksandrov
