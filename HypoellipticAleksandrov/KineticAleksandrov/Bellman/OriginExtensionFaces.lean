module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.OriginExtensionWeak
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # The literal kinetic inner rectangle and its normal surface weights -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set MeasureTheory

/-- Reference parametrizations of the two position faces and two velocity faces. -/
def bellmanOriginFace (i : Fin 4) (w : ℝ) : ℝ × ℝ :=
  if i.val < 2 then (if i.val = 0 then -1 else 1, w)
  else (w, if i.val = 2 then -1 else 1)

/-- The reference face never passes through the origin. -/
theorem bellmanOriginFace_ne_zero (i : Fin 4) (w : ℝ) :
    bellmanOriginFace i w ≠ (0, 0) := by
  fin_cases i <;> simp [bellmanOriginFace]

/-- Each reference parametrization is continuous. -/
theorem bellmanOriginFace_continuous (i : Fin 4) : Continuous (bellmanOriginFace i) := by
  change Continuous (fun w => bellmanOriginFace i w)
  unfold bellmanOriginFace
  split_ifs <;> fun_prop

/-- Reference faces lie in a fixed gauge annulus; their dilates excise the kinetic origin. -/
theorem bellmanOriginFace_gauge (i : Fin 4) (w : ℝ) (hw : w ∈ Icc (-1 : ℝ) 1) :
    1 ≤ bellmanGauge (bellmanOriginFace i w) ∧
      bellmanGauge (bellmanOriginFace i w) ≤ 2 := by
  have he := bellmanGauge_pow_six (bellmanOriginFace i w)
  have hr := bellmanGauge_nonneg (bellmanOriginFace i w)
  have hwabs : |w| ≤ 1 := abs_le.mpr hw
  have hw2 : w ^ 2 ≤ 1 := by
    have hh := pow_le_pow_left₀ (abs_nonneg w) hwabs 2
    simpa only [sq_abs, one_pow] using hh
  have hw6 : w ^ 6 ≤ 1 := by
    have hh := pow_le_pow_left₀ (abs_nonneg w) hwabs 6
    simpa only [pow_abs, abs_of_nonneg (by positivity : 0 ≤ w ^ 6), one_pow] using hh
  have hlo : 1 ≤ bellmanGauge (bellmanOriginFace i w) ^ 6 := by
    fin_cases i <;> norm_num [bellmanOriginFace, bellmanGaugePower] at he ⊢ <;>
      nlinarith [sq_nonneg w, show 0 ≤ w ^ 6 by positivity]
  have hhi : bellmanGauge (bellmanOriginFace i w) ^ 6 ≤ 2 := by
    fin_cases i <;> norm_num [bellmanOriginFace, bellmanGaugePower] at he ⊢ <;> linarith
  constructor
  · apply (pow_le_pow_iff_left₀ zero_le_one hr (by decide : 6 ≠ 0)).mp
    simpa only [one_pow] using hlo
  · apply (pow_le_pow_iff_left₀ hr (by norm_num : (0 : ℝ) ≤ 2)
      (by decide : 6 ≠ 0)).mp
    norm_num only
    linarith

/-- A radius-δ rectangle boundary is contained between gauge radii δ and 2δ. -/
theorem bellmanOriginFace_dilation_gauge (delta : ℝ) (hd : 0 < delta)
    (i : Fin 4) (w : ℝ) (hw : w ∈ Icc (-1 : ℝ) 1) :
    delta ≤ bellmanGauge (bellmanPlaneDilation delta (bellmanOriginFace i w)) ∧
      bellmanGauge (bellmanPlaneDilation delta (bellmanOriginFace i w)) ≤ 2 * delta := by
  rw [bellmanGauge_dilation delta hd]
  obtain ⟨hlo, hhi⟩ := bellmanOriginFace_gauge i w hw
  constructor
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left hlo hd.le
  · simpa only [mul_comm delta 2] using mul_le_mul_of_nonneg_left hhi hd.le

/-- Compact reference faces give a single bound for any continuous punctured function. -/
theorem bellmanOriginFace_bound (f : (ℝ × ℝ) → ℝ)
    (hc : ContinuousOn f bellmanPuncturedSet) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i : Fin 4, ∀ w ∈ Icc (-1 : ℝ) 1,
      |f (bellmanOriginFace i w)| ≤ C := by
  have hb (i : Fin 4) : ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ Icc (-1 : ℝ) 1,
      |f (bellmanOriginFace i w)| ≤ C := by
    have hi := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).image (bellmanOriginFace_continuous i)
    have hu : bellmanOriginFace i '' Icc (-1 : ℝ) 1 ⊆ bellmanPuncturedSet := by
      rintro q ⟨w, _, rfl⟩
      exact bellmanOriginFace_ne_zero i w
    obtain ⟨C, hC⟩ := hi.bddAbove_image (hc.mono hu).abs
    refine ⟨max C 0, le_max_right _ _, fun w hw => ?_⟩
    exact (hC (mem_image_of_mem _ (mem_image_of_mem _ hw))).trans (le_max_left _ _)
  choose C hC hbC using hb
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), fun i w hw => ?_⟩
  exact (hbC i w hw).trans (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i))

/-- A parametrized boundary integral includes the actual normal surface Jacobian δᵏ. -/
def bellmanOriginFaceError (k : ℕ) (delta : ℝ) (i : Fin 4)
    (f test : (ℝ × ℝ) → ℝ) : ℝ :=
  delta ^ k * ∫ w in (-1 : ℝ)..1,
    f (bellmanPlaneDilation delta (bellmanOriginFace i w)) *
      test (bellmanPlaneDilation delta (bellmanOriginFace i w))

/-- The position face error is literally its normal one-dimensional boundary integral. -/
theorem bellmanOriginFaceError_position (delta : ℝ) (i : Fin 4) (hi : i.val < 2)
    (f test : (ℝ × ℝ) → ℝ) :
    bellmanOriginFaceError 1 delta i f test =
      ∫ v in (-delta)..delta,
        f (delta ^ 3 * (if i.val = 0 then -1 else 1), v) *
          test (delta ^ 3 * (if i.val = 0 then -1 else 1), v) := by
  have hh := intervalIntegral.smul_integral_comp_mul_left
    (a := (-1 : ℝ)) (b := 1)
    (fun v => f (delta ^ 3 * (if i.val = 0 then -1 else 1), v) *
      test (delta ^ 3 * (if i.val = 0 then -1 else 1), v)) delta
  simpa only [bellmanOriginFaceError, bellmanOriginFace, ite_eq_left hi,
    bellmanPlaneDilation, pow_one, smul_eq_mul, mul_neg_one, mul_one] using hh

/-- The velocity face error has normal surface Jacobian δ³, not a Euclidean δ. -/
theorem bellmanOriginFaceError_velocity (delta : ℝ) (i : Fin 4) (hi : ¬i.val < 2)
    (f test : (ℝ × ℝ) → ℝ) :
    bellmanOriginFaceError 3 delta i f test =
      ∫ X in (-(delta ^ 3))..delta ^ 3,
        f (X, delta * (if i.val = 2 then -1 else 1)) *
          test (X, delta * (if i.val = 2 then -1 else 1)) := by
  have hh := intervalIntegral.smul_integral_comp_mul_left
    (a := (-1 : ℝ)) (b := 1)
    (fun X => f (X, delta * (if i.val = 2 then -1 else 1)) *
      test (X, delta * (if i.val = 2 then -1 else 1))) (delta ^ 3)
  simpa only [bellmanOriginFaceError, bellmanOriginFace, ite_eq_right hi,
    bellmanPlaneDilation, smul_eq_mul, mul_neg_one, mul_one] using hh

/-- Homogeneity gives the exact degree plus normal surface weight of a face error. -/
theorem bellmanOriginFaceError_bound (beta : ℝ) (f : (ℝ × ℝ) → ℝ)
    (hscale : ∀ r : ℝ, 0 < r → ∀ q ∈ bellmanPuncturedSet,
      f (bellmanPlaneDilation r q) = r ^ beta * f q)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ i : Fin 4, ∀ w ∈ Icc (-1 : ℝ) 1, |f (bellmanOriginFace i w)| ≤ C)
    (test : (ℝ × ℝ) → ℝ) (M : ℝ) (_hM : 0 ≤ M) (hMt : ∀ q, |test q| ≤ M)
    (k : ℕ) (delta : ℝ) (hd : 0 < delta) (i : Fin 4) :
    |bellmanOriginFaceError k delta i f test| ≤ 2 * C * M * delta ^ (beta + k) := by
  have hi : |∫ w in (-1 : ℝ)..1,
      f (bellmanPlaneDilation delta (bellmanOriginFace i w)) *
        test (bellmanPlaneDilation delta (bellmanOriginFace i w))| ≤
      (delta ^ beta * C * M) * 2 := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (-1 : ℝ)) (b := 1) (C := delta ^ beta * C * M)
      (f := fun w => f (bellmanPlaneDilation delta (bellmanOriginFace i w)) *
        test (bellmanPlaneDilation delta (bellmanOriginFace i w))) (fun w hw => ?_)
    · simpa only [Real.norm_eq_abs, sub_neg_eq_add, one_add_one_eq_two, abs_of_pos
        (by norm_num : (0 : ℝ) < 2)] using hh
    · have hw' : -1 < w ∧ w ≤ 1 := by simpa using hw
      rw [Real.norm_eq_abs, abs_mul,
        hscale delta hd _ (bellmanOriginFace_ne_zero i w), abs_mul,
        abs_of_pos (Real.rpow_pos_of_pos hd beta)]
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (hb i w ⟨hw'.1.le, hw'.2⟩)
          (Real.rpow_nonneg hd.le _)
      · exact hMt _
      · exact abs_nonneg _
      · exact mul_nonneg (Real.rpow_nonneg hd.le _) hC
  unfold bellmanOriginFaceError
  rw [abs_mul, abs_of_nonneg (pow_nonneg hd.le k)]
  calc
    delta ^ k * |∫ w in (-1 : ℝ)..1,
        f (bellmanPlaneDilation delta (bellmanOriginFace i w)) *
          test (bellmanPlaneDilation delta (bellmanOriginFace i w))| ≤
        delta ^ k * ((delta ^ beta * C * M) * 2) :=
      mul_le_mul_of_nonneg_left hi (pow_nonneg hd.le k)
    _ = 2 * C * M * delta ^ (beta + k) := by
      rw [Real.rpow_add hd, Real.rpow_natCast]
      ring

end HypoellipticAleksandrov.KineticAleksandrov
