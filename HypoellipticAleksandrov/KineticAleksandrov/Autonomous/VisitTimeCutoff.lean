module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionCutoffs
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic

/-! # Uniform smooth time cutoffs for intervals of length r squared -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory

/-- A translated cutoff with inner radius three quarters of the interval length. -/
def visitTimeCutoff (a r : ℝ) (hr : 0 < r) (t : ℝ) : ℝ :=
  reconstructionPositionBump (3 * r ^ 2 / 4) (by positivity) (t - (a + r ^ 2 / 2))

/-- The time cutoff is smooth and lies between zero and one. -/
theorem visitTimeCutoff_properties (a r : ℝ) (hr : 0 < r) :
    ContDiff ℝ (⊤ : ℕ∞) (visitTimeCutoff a r hr) ∧
      (∀ t, 0 ≤ visitTimeCutoff a r hr t ∧ visitTimeCutoff a r hr t ≤ 1) :=
  ⟨(reconstructionPositionBump _ _).contDiff.comp (contDiff_id.sub contDiff_const),
    fun _ => ⟨(reconstructionPositionBump _ _).nonneg,
      (reconstructionPositionBump _ _).le_one⟩⟩

/-- It equals one on the whole closed interval, including a possible initial atom. -/
theorem visitTimeCutoff_eq_one (a r : ℝ) (hr : 0 < r) {t : ℝ}
    (ht : t ∈ Icc a (a + r ^ 2)) : visitTimeCutoff a r hr t = 1 := by
  apply (reconstructionPositionBump _ _).one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
  change |t - (a + r ^ 2 / 2)| ≤ 3 * r ^ 2 / 4
  apply abs_le.mpr
  constructor <;> nlinarith [ht.1, ht.2, sq_nonneg r]

/-- Its nonzero support is confined to an interval of length three r squared. -/
theorem visitTimeCutoff_support (a r : ℝ) (hr : 0 < r) :
    Function.support (visitTimeCutoff a r hr) ⊆ Ioo (a - r ^ 2) (a + 2 * r ^ 2) := by
  intro t ht
  have hb : t - (a + r ^ 2 / 2) ∈
      Function.support (reconstructionPositionBump (3 * r ^ 2 / 4) (by positivity)) := ht
  rw [ContDiffBump.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hb
  change |t - (a + r ^ 2 / 2)| < 2 * (3 * r ^ 2 / 4) at hb
  obtain ⟨hl, hu⟩ := abs_lt.mp hb
  constructor <;> linarith

/-- A single constant controls the derivative of every rescaled time cutoff. -/
theorem visitTimeCutoff_deriv_bound : ∃ D : ℝ, 0 ≤ D ∧
    ∀ (a r : ℝ) (hr : 0 < r) (t : ℝ),
      |deriv (visitTimeCutoff a r hr) t| ≤ D / r ^ 2 := by
  obtain ⟨D, hD, hd⟩ := reconstructionUnitBump_properties.2.2.2
  refine ⟨4 * D / 3, by positivity, ?_⟩
  intro a r hr t
  have hs : ContDiff ℝ (⊤ : ℕ∞)
      (reconstructionPositionBump (3 * r ^ 2 / 4) (by positivity) : ℝ → ℝ) :=
    (reconstructionPositionBump _ _).contDiff
  have hc := (hs.differentiable (by norm_num) (t - (a + r ^ 2 / 2))).hasDerivAt.comp t
    ((hasDerivAt_id t).sub_const (a + r ^ 2 / 2))
  have he : deriv (visitTimeCutoff a r hr) t =
      deriv (reconstructionPositionBump (3 * r ^ 2 / 4) (by positivity))
        (t - (a + r ^ 2 / 2)) := by
    have hf : visitTimeCutoff a r hr = fun x =>
        reconstructionPositionBump (3 * r ^ 2 / 4) (by positivity)
          (x - (a + r ^ 2 / 2)) := rfl
    rw [hf]
    simpa only [id_eq, mul_one, Function.comp_def] using hc.deriv
  rw [he]
  have hb := reconstructionPositionBump_deriv_bound (3 * r ^ 2 / 4) (by positivity)
    D hd (t - (a + r ^ 2 / 2))
  convert hb using 1
  field_simp

/-- The closed support has the same length-three bounding interval. -/
theorem visitTimeCutoff_tsupport (a r : ℝ) (hr : 0 < r) :
    tsupport (visitTimeCutoff a r hr) ⊆ Icc (a - r ^ 2) (a + 2 * r ^ 2) := by
  have h := closure_mono (visitTimeCutoff_support a r hr)
  have ho : a - r ^ 2 < a + 2 * r ^ 2 := by nlinarith [sq_pos_of_pos hr]
  rwa [closure_Ioo ho.ne] at h

/-- Compactness of the translated time cutoff. -/
theorem visitTimeCutoff_hasCompactSupport (a r : ℝ) (hr : 0 < r) :
    HasCompactSupport (visitTimeCutoff a r hr) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (visitTimeCutoff_tsupport a r hr)

/-- The cutoff derivative vanishes outside the same closed time window. -/
theorem visitTimeCutoff_deriv_tsupport (a r : ℝ) (hr : 0 < r) :
    tsupport (deriv (visitTimeCutoff a r hr)) ⊆ Icc (a - r ^ 2) (a + 2 * r ^ 2) :=
  tsupport_deriv_subset.trans (visitTimeCutoff_tsupport a r hr)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
