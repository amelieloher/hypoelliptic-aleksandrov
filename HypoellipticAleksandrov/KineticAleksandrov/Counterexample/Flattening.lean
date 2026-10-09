module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Geometry
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Linarith

/-!
# A fixed convex flattening function

Integrating the smooth transition constructs the source's flattening function.
The function and its eventual affine offset are independent of the dilation scale.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Set
open scoped ContDiff

/-- The fixed slope interpolating between zero and one on the source interval. -/
noncomputable def flatteningSlope (s : ℝ) : ℝ := Real.smoothTransition (s - 1)

/-- The convex primitive used to flatten the singular profile. -/
noncomputable def flatteningPsi (s : ℝ) : ℝ := ∫ t in (1 : ℝ)..s, flatteningSlope t

/-- The offset in the eventual affine formula for the flattening function. -/
noncomputable def flatteningOffset : ℝ := 2 - flatteningPsi 2

/-- The slope is infinitely differentiable. -/
theorem contDiff_flatteningSlope : ContDiff ℝ ∞ flatteningSlope :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

/-- The slope is nondecreasing. -/
theorem monotone_flatteningSlope : Monotone flatteningSlope := by
  intro s t h
  exact Real.smoothTransition.monotone (sub_le_sub_right h 1)

/-- The flattening primitive has the specified derivative. -/
theorem deriv_flatteningPsi (s : ℝ) : deriv flatteningPsi s = flatteningSlope s :=
  contDiff_flatteningSlope.continuous.deriv_integral flatteningSlope 1 s

/-- The flattening function is smooth of every finite order. -/
theorem contDiff_flatteningPsi : ContDiff ℝ ∞ flatteningPsi := by
  apply contDiff_infty_iff_deriv.2
  constructor
  · intro s
    exact (contDiff_flatteningSlope.continuous.integral_hasStrictDerivAt 1 s)
      |>.hasDerivAt.differentiableAt
  · simpa only [funext deriv_flatteningPsi] using contDiff_flatteningSlope

/-- The flattening primitive is convex. -/
theorem convexOn_flatteningPsi : ConvexOn ℝ univ flatteningPsi := by
  apply Monotone.convexOn_univ_of_deriv
    (contDiff_flatteningPsi.differentiable (by simp))
  simpa only [funext deriv_flatteningPsi] using monotone_flatteningSlope

/-- The slope lies between zero and one everywhere. -/
theorem flatteningPsi_deriv_bounds (s : ℝ) :
    0 ≤ deriv flatteningPsi s ∧ deriv flatteningPsi s ≤ 1 := by
  rw [deriv_flatteningPsi]
  exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- The primitive is zero to the left of the flattening threshold. -/
theorem flatteningPsi_eq_zero (s : ℝ) (hs : s ≤ 1) : flatteningPsi s = 0 := by
  unfold flatteningPsi
  rw [intervalIntegral.integral_symm (a := s) (b := (1 : ℝ))]
  have he : (∫ t in s..(1 : ℝ), flatteningSlope t) = ∫ t in s..(1 : ℝ), (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hs]
    intro t ht
    exact Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr ht.2)
  rw [he]
  simp only [intervalIntegral.integral_zero, neg_zero]

/-- The primitive is affine past the transition region. -/
theorem flatteningPsi_eq_affine (s : ℝ) (hs : 2 ≤ s) :
    flatteningPsi s = s - flatteningOffset := by
  have hi := contDiff_flatteningSlope.continuous
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hi.intervalIntegrable (μ := volume) 1 2) (hi.intervalIntegrable (μ := volume) 2 s)
  have he : (∫ t in (2 : ℝ)..s, flatteningSlope t) = ∫ t in (2 : ℝ)..s, (1 : ℝ) := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hs]
    intro t ht
    exact Real.smoothTransition.one_of_one_le (by linarith only [ht.1])
  unfold flatteningOffset
  simp only [flatteningPsi]
  rw [← hadd, he, intervalIntegral.integral_const]
  simp only [smul_eq_mul, mul_one]
  ring

/-- The transition primitive has strictly intermediate height at the upper threshold. -/
theorem flatteningPsi_two_bounds : 0 < flatteningPsi 2 ∧ flatteningPsi 2 < 1 := by
  have hc := contDiff_flatteningSlope.continuous
  have hpos := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by norm_num : (1 : ℝ) < 2) continuous_const.continuousOn hc.continuousOn
    (fun t _ => Real.smoothTransition.nonneg (t - 1))
    (show ∃ t ∈ Icc (1 : ℝ) 2, (0 : ℝ) < flatteningSlope t from
      ⟨3 / 2, by norm_num,
        Real.smoothTransition.pos_of_pos (by norm_num : 0 < (3 / 2 : ℝ) - 1)⟩)
  have hlt := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by norm_num : (1 : ℝ) < 2) hc.continuousOn continuous_const.continuousOn
    (fun t _ => Real.smoothTransition.le_one (t - 1))
    (show ∃ t ∈ Icc (1 : ℝ) 2, flatteningSlope t < (1 : ℝ) from
      ⟨3 / 2, by norm_num,
        Real.smoothTransition.lt_one_of_lt_one (by norm_num : (3 / 2 : ℝ) - 1 < 1)⟩)
  simpa only [intervalIntegral.integral_zero, intervalIntegral.integral_const,
    smul_eq_mul, sub_self, sub_zero, mul_one, flatteningPsi, show (2 - 1 : ℝ) = 1 by ring]
    using And.intro hpos hlt

/-- The affine offset lies strictly between the source's two thresholds. -/
theorem flatteningOffset_bounds : 1 < flatteningOffset ∧ flatteningOffset < 2 := by
  have hb := flatteningPsi_two_bounds
  unfold flatteningOffset
  constructor <;> linarith only [hb.1, hb.2]

/-- The second derivative of the convex primitive is nonnegative. -/
theorem flatteningPsi_deriv2_nonneg (s : ℝ) : 0 ≤ deriv (deriv flatteningPsi) s := by
  rw [funext deriv_flatteningPsi]
  exact monotone_flatteningSlope.deriv_nonneg

/-- The second derivative vanishes below the transition interval. -/
theorem flatteningPsi_deriv2_eq_zero_of_lt (s : ℝ) (hs : s < 1) :
    deriv (deriv flatteningPsi) s = 0 := by
  rw [funext deriv_flatteningPsi]
  apply HasDerivAt.deriv
  apply (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hs] with t ht
  exact Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr ht.le)

/-- The second derivative vanishes above the transition interval. -/
theorem flatteningPsi_deriv2_eq_zero_of_gt (s : ℝ) (hs : 2 < s) :
    deriv (deriv flatteningPsi) s = 0 := by
  rw [funext deriv_flatteningPsi]
  apply HasDerivAt.deriv
  apply (hasDerivAt_const s (1 : ℝ)).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hs] with t ht
  exact Real.smoothTransition.one_of_one_le (by linarith only [ht.out])

/-- The second derivative has compact support in the fixed closed transition interval. -/
theorem hasCompactSupport_flatteningPsi_deriv2 :
    HasCompactSupport (deriv (deriv flatteningPsi)) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (1 : ℝ)) (b := 2))
  intro s hs
  by_contra h
  have hor : s < 1 ∨ 2 < s := by simpa only [mem_Icc, not_and_or, not_le] using h
  rcases hor with hlt | hgt
  · exact hs (flatteningPsi_deriv2_eq_zero_of_lt s hlt)
  · exact hs (flatteningPsi_deriv2_eq_zero_of_gt s hgt)

/-- A single constant bounds the second derivative independently of the scale. -/
theorem flatteningPsi_deriv2_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ s, deriv (deriv flatteningPsi) s ≤ K := by
  have hc : Continuous (deriv (deriv flatteningPsi)) := by
    rw [funext deriv_flatteningPsi]
    exact contDiff_flatteningSlope.continuous_deriv (by simp)
  obtain ⟨K, hK⟩ := hasCompactSupport_flatteningPsi_deriv2.exists_bound_of_continuous hc
  refine ⟨max K 0 + 1, by positivity, ?_⟩
  intro s
  exact (le_abs_self _).trans ((hK s).trans
    ((le_max_left K 0).trans (le_add_of_nonneg_right zero_le_one)))

/-- The primitive is nonnegative at every nonnegative argument. -/
theorem flatteningPsi_nonneg (s : ℝ) : 0 ≤ flatteningPsi s := by
  by_cases h : s ≤ 1
  · rw [flatteningPsi_eq_zero s h]
  · exact intervalIntegral.integral_nonneg_of_forall (le_of_not_ge h)
      (fun t => Real.smoothTransition.nonneg (t - 1))

/-- The primitive is nondecreasing. -/
theorem monotone_flatteningPsi : Monotone flatteningPsi :=
  monotone_of_deriv_nonneg (contDiff_flatteningPsi.differentiable (by simp))
    (fun s => (flatteningPsi_deriv_bounds s).1)

/-- A single fixed smooth convex function has all the prescribed flattening properties. -/
theorem exists_flattening_function :
    ∃ Psi : ℝ → ℝ, ∃ cPsi K : ℝ,
      ContDiff ℝ ∞ Psi ∧ ConvexOn ℝ univ Psi ∧ 1 < cPsi ∧ cPsi < 2 ∧ 0 < K ∧
      (∀ s, s ≤ 1 → Psi s = 0) ∧
      (∀ s, 0 ≤ deriv Psi s ∧ deriv Psi s ≤ 1) ∧
      (∀ s, 2 ≤ s → Psi s = s - cPsi) ∧
      (∀ s, 0 ≤ deriv (deriv Psi) s ∧ deriv (deriv Psi) s ≤ K) ∧
      HasCompactSupport (deriv (deriv Psi)) := by
  obtain ⟨K, hK, hb⟩ := flatteningPsi_deriv2_bound
  exact ⟨flatteningPsi, flatteningOffset, K, contDiff_flatteningPsi,
    convexOn_flatteningPsi, flatteningOffset_bounds.1, flatteningOffset_bounds.2, hK,
    flatteningPsi_eq_zero, flatteningPsi_deriv_bounds, flatteningPsi_eq_affine,
    fun s => ⟨flatteningPsi_deriv2_nonneg s, hb s⟩, hasCompactSupport_flatteningPsi_deriv2⟩

/-- The literal flattened profile in Appendix C. -/
noncomputable def flatProfile {d : ℕ} (H : XV d → ℝ) (Psi : ℝ → ℝ)
    (cPsi alpha r : ℝ) (q : XV d) : ℝ :=
  1 - cPsi * Real.rpow r alpha - Real.rpow r alpha * Psi (H q / Real.rpow r alpha)

/-- On the plateau the flattened function is constant. -/
theorem flatProfile_eq_constant {d : ℕ} (H : XV d → ℝ) (alpha r : ℝ)
    (hr : 0 < r) (q : XV d) (hq : H q ≤ Real.rpow r alpha) :
    flatProfile H flatteningPsi flatteningOffset alpha r q =
      1 - flatteningOffset * Real.rpow r alpha := by
  unfold flatProfile
  simp only [Real.rpow_eq_pow] at hq ⊢
  rw [flatteningPsi_eq_zero _ ((div_le_one (Real.rpow_pos_of_pos hr alpha)).2 hq)]
  ring

/-- Beyond the transition shell the flattened function equals `1 - H`. -/
theorem flatProfile_eq_one_sub {d : ℕ} (H : XV d → ℝ) (alpha r : ℝ)
    (hr : 0 < r) (q : XV d) (hq : 2 * Real.rpow r alpha ≤ H q) :
    flatProfile H flatteningPsi flatteningOffset alpha r q = 1 - H q := by
  unfold flatProfile
  simp only [Real.rpow_eq_pow] at hq ⊢
  rw [flatteningPsi_eq_affine _ ((le_div_iff₀ (Real.rpow_pos_of_pos hr alpha)).2 hq)]
  have hn := (Real.rpow_pos_of_pos hr alpha).ne'
  field_simp [hn]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
