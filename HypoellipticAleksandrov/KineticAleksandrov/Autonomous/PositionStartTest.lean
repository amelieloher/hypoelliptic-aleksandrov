module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionCutoffs
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitsCells
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic

/-! # Uniform smooth position cutoffs for cells of width r cubed -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory

/-- A translated cutoff with inner radius three quarters of the cell width. -/
def positionStartCutoff (Y r : ℝ) (hr : 0 < r) (X : ℝ) : ℝ :=
  reconstructionPositionBump (3 * r ^ 3 / 4) (by positivity) (X - Y)

/-- The position cutoff is smooth and lies between zero and one. -/
theorem positionStartCutoff_properties (Y r : ℝ) (hr : 0 < r) :
    ContDiff ℝ (⊤ : ℕ∞) (positionStartCutoff Y r hr) ∧
      (∀ X, 0 ≤ positionStartCutoff Y r hr X ∧ positionStartCutoff Y r hr X ≤ 1) :=
  ⟨(reconstructionPositionBump _ _).contDiff.comp (contDiff_id.sub contDiff_const),
    fun _ => ⟨(reconstructionPositionBump _ _).nonneg,
      (reconstructionPositionBump _ _).le_one⟩⟩

/-- It equals one within half a cell width of its centre. -/
theorem positionStartCutoff_eq_one (Y r : ℝ) (hr : 0 < r) {X : ℝ}
    (ht : |X - Y| ≤ r ^ 3 / 2) : positionStartCutoff Y r hr X = 1 := by
  apply (reconstructionPositionBump _ _).one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
  change |X - Y| ≤ 3 * r ^ 3 / 4
  apply abs_le.mpr
  constructor <;> linarith [pow_pos hr 3, (abs_le.mp ht).1, (abs_le.mp ht).2]

/-- Its nonzero support is confined to an interval of length three r cubed. -/
theorem positionStartCutoff_support (Y r : ℝ) (hr : 0 < r) :
    Function.support (positionStartCutoff Y r hr) ⊆
      Ioo (Y - 3 * r ^ 3 / 2) (Y + 3 * r ^ 3 / 2) := by
  intro X ht
  have hb : X - Y ∈
      Function.support (reconstructionPositionBump (3 * r ^ 3 / 4) (by positivity)) := ht
  rw [ContDiffBump.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hb
  change |X - Y| < 2 * (3 * r ^ 3 / 4) at hb
  obtain ⟨hl, hu⟩ := abs_lt.mp hb
  constructor <;> linarith

/-- A single constant controls the derivative of every rescaled position cutoff. -/
theorem positionStartCutoff_deriv_bound : ∃ D : ℝ, 0 ≤ D ∧
    ∀ (Y r : ℝ) (hr : 0 < r) (X : ℝ),
      |deriv (positionStartCutoff Y r hr) X| ≤ D / r ^ 3 := by
  obtain ⟨D, hD, hd⟩ := reconstructionUnitBump_properties.2.2.2
  refine ⟨4 * D / 3, by positivity, ?_⟩
  intro Y r hr X
  have hs : ContDiff ℝ (⊤ : ℕ∞)
      (reconstructionPositionBump (3 * r ^ 3 / 4) (by positivity) : ℝ → ℝ) :=
    (reconstructionPositionBump _ _).contDiff
  have hc := (hs.differentiable (by norm_num) (X - Y)).hasDerivAt.comp X
    ((hasDerivAt_id X).sub_const Y)
  have he : deriv (positionStartCutoff Y r hr) X =
      deriv (reconstructionPositionBump (3 * r ^ 3 / 4) (by positivity))
        (X - Y) := by
    have hf : positionStartCutoff Y r hr = fun x =>
        reconstructionPositionBump (3 * r ^ 3 / 4) (by positivity)
          (x - Y) := rfl
    rw [hf]
    simpa only [id_eq, mul_one, Function.comp_def] using hc.deriv
  rw [he]
  have hb := reconstructionPositionBump_deriv_bound (3 * r ^ 3 / 4) (by positivity)
    D hd (X - Y)
  convert hb using 1
  field_simp

/-- The literal source cell is contained in the one region of its centred cutoff. -/
theorem positionStartCutoff_eq_one_on_cell (r x : ℝ) (hr : 0 < r) (k : ℤ) {X : ℝ}
    (hX : X ∈ enlargedPositionCell r x k) :
    positionStartCutoff (x + ((k : ℝ) + 1 / 2) * r ^ 3) r hr X = 1 := by
  apply positionStartCutoff_eq_one
  change x + (k : ℝ) * r ^ 3 ≤ X ∧ X < x + ((k : ℝ) + 1) * r ^ 3 at hX
  rw [abs_le]
  constructor <;> linarith only [hX.1, hX.2]

/-- The closed support stays within the same length-three position interval. -/
theorem positionStartCutoff_tsupport (Y r : ℝ) (hr : 0 < r) :
    tsupport (positionStartCutoff Y r hr) ⊆
      Icc (Y - 3 * r ^ 3 / 2) (Y + 3 * r ^ 3 / 2) := by
  have h := closure_mono (positionStartCutoff_support Y r hr)
  rw [closure_Ioo (by linarith [pow_pos hr 3])] at h
  exact h

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
