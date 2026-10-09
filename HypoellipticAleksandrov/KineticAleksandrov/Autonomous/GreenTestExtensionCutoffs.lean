module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitMeasureFuture
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsScaling
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Support

/-! # Compact product cutoffs for the bounded smooth Green identity -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter Metric
open SectionTwo TheoremA Evolution
open scoped Topology

/-- A fixed smooth scalar cutoff equal to one on the unit interval. -/
def reconstructionUnitBump : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, by norm_num⟩

/-- Rescaled position cutoffs are globally smooth, between zero and one. -/
theorem reconstructionUnitBump_properties :
    ContDiff ℝ (⊤ : ℕ∞) reconstructionUnitBump ∧
      HasCompactSupport reconstructionUnitBump ∧
      (∀ x, 0 ≤ reconstructionUnitBump x ∧ reconstructionUnitBump x ≤ 1) ∧
      ∃ D : ℝ, 0 ≤ D ∧ ∀ x, |deriv reconstructionUnitBump x| ≤ D := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) reconstructionUnitBump := reconstructionUnitBump.contDiff
  obtain ⟨D, hD⟩ := reconstructionUnitBump.hasCompactSupport.deriv.exists_bound_of_continuous
    (hs.continuous_deriv (by simp))
  exact ⟨hs, reconstructionUnitBump.hasCompactSupport,
    fun x => ⟨reconstructionUnitBump.nonneg, reconstructionUnitBump.le_one⟩,
    max D 0, le_max_right _ _, fun x => (hD x).trans (le_max_left _ _)⟩

/-- A position cutoff with radius `R` and outer radius `2R`. -/
def reconstructionPositionBump (R : ℝ) (hR : 0 < R) : ContDiffBump (0 : ℝ) :=
  ⟨R, 2 * R, hR, by linarith⟩

/-- Radius rescaling agrees with the previously verified scalar cutoff calculus. -/
theorem reconstructionPositionBump_eq_scaled (R : ℝ) (hR : 0 < R) :
    (reconstructionPositionBump R hR : ℝ → ℝ) =
      scaledScalarCutoff reconstructionUnitBump R := by
  funext x
  simp only [ContDiffBump.apply, reconstructionPositionBump, reconstructionUnitBump,
    scaledScalarCutoff, sub_zero, smul_eq_mul]
  congr 1
  · field_simp
  · simp only [inv_one, one_mul, div_eq_mul_inv]
    ring

/-- The cutoff derivative has a uniform inverse-radius bound. -/
theorem reconstructionPositionBump_deriv_bound (R : ℝ) (hR : 0 < R) (D : ℝ)
    (hD : ∀ x, |deriv reconstructionUnitBump x| ≤ D) (x : ℝ) :
    |deriv (reconstructionPositionBump R hR) x| ≤ D / R := by
  rw [reconstructionPositionBump_eq_scaled]
  exact scaledScalarCutoff_deriv_bound _
    (reconstructionUnitBump_properties.1.of_le (by simp)) hR D hD x

/-- Expanding position cutoffs eventually equal one at every fixed position. -/
theorem reconstructionPositionBump_tendsto (x : ℝ) :
    Tendsto (fun n : ℕ => reconstructionPositionBump ((n : ℝ) + 1) (by positivity) x)
      atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  have hn := (tendsto_natCast_atTop_atTop.eventually_ge_atTop (|x| : ℝ))
  filter_upwards [hn] with n hn
  symm
  apply (reconstructionPositionBump ((n : ℝ) + 1) (by positivity)).one_of_mem_closedBall
  rw [mem_closedBall, Real.dist_eq, sub_zero]
  change |x| ≤ (n : ℝ) + 1
  linarith

/-- The expanding position cutoff derivative converges to zero. -/
theorem reconstructionPositionBump_deriv_tendsto (x : ℝ) :
    Tendsto (fun n : ℕ => deriv
      (reconstructionPositionBump ((n : ℝ) + 1) (by positivity)) x) atTop (𝓝 0) := by
  obtain ⟨D, _, hD⟩ := reconstructionUnitBump_properties.2.2.2
  apply squeeze_zero_norm (fun n => ?_)
    (show Tendsto (fun n : ℕ => D / ((n : ℝ) + 1)) atTop (𝓝 0) from by
      simpa only [div_eq_mul_inv, one_mul, mul_zero] using
        tendsto_one_div_add_atTop_nhds_zero_nat.const_mul D)
  rw [Real.norm_eq_abs]
  exact reconstructionPositionBump_deriv_bound _ (by positivity) D hD x

/-- Coordinatewise smooth cutoffs make an arbitrary smooth test compact. -/
theorem reconstruction_product_cutoff_compact
    (bt bv bx : ContDiffBump (0 : ℝ)) (f : EvolutionVec 1 → ℝ) :
    HasCompactSupport (fun x => bt (timeCoord 1 x) * bv (diffusedCoord 1 x 0) *
      bx (transportedCoord 1 x 0) * f x) := by
  let R := max bt.rOut (max bv.rOut bx.rOut)
  have hR : 0 ≤ R := bt.rOut_pos.le.trans (le_max_left _ _)
  apply IsCompact.of_isClosed_subset (isCompact_closedBall (0 : EvolutionVec 1) R)
    (isClosed_tsupport _)
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  have hn : bt (timeCoord 1 x) ≠ 0 ∧ bv (diffusedCoord 1 x 0) ≠ 0 ∧
      bx (transportedCoord 1 x 0) ≠ 0 := by
    have hh := mul_ne_zero_iff.mp hx
    have hh' := mul_ne_zero_iff.mp hh.1
    exact ⟨(mul_ne_zero_iff.mp hh'.1).1, (mul_ne_zero_iff.mp hh'.1).2, hh'.2⟩
  have ht : |timeCoord 1 x| < bt.rOut := by
    have hh : timeCoord 1 x ∈ Function.support bt := hn.1
    rw [bt.support_eq] at hh
    simpa only [mem_ball, Real.dist_eq, sub_zero] using hh
  have hv : |diffusedCoord 1 x 0| < bv.rOut := by
    have hh : diffusedCoord 1 x 0 ∈ Function.support bv := hn.2.1
    rw [bv.support_eq] at hh
    simpa only [mem_ball, Real.dist_eq, sub_zero] using hh
  have hz : |transportedCoord 1 x 0| < bx.rOut := by
    have hh : transportedCoord 1 x 0 ∈ Function.support bx := hn.2.2
    rw [bx.support_eq] at hh
    simpa only [mem_ball, Real.dist_eq, sub_zero] using hh
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR]
  intro i
  fin_cases i
  · exact ht.le.trans (le_max_left _ _)
  · exact hv.le.trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact hz.le.trans ((le_max_right _ _).trans (le_max_right _ _))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
