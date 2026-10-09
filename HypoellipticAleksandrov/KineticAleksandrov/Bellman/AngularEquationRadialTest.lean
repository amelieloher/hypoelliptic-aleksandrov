module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationRadialIntegrals
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationTestIntegrability
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! # A genuine nonzero radial multiplier for the separated adjoint test -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- An explicit smooth radial test makes the common angular multiplier strictly positive. -/
theorem exists_bellmanAngularRadialTest (β : ℝ) :
    ∃ ζ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ ∧ HasCompactSupport ζ ∧
      tsupport ζ ⊆ Ioo (1 : ℝ) 3 ∧
      0 < (∫ s, ζ s.val / s.val ^ 2 ∂bellmanRadialWeight β) ∧
      (∫ s, deriv ζ s.val / s.val ∂bellmanRadialWeight β) =
        (β - 2) * (∫ s, ζ s.val / s.val ^ 2 ∂bellmanRadialWeight β) := by
  let ζ : ContDiffBump (2 : ℝ) :=
    { rIn := 1 / 4
      rOut := 1 / 2
      rIn_pos := by norm_num
      rIn_lt_rOut := by norm_num }
  have hs : tsupport (ζ : ℝ → ℝ) ⊆ Ioo (1 : ℝ) 3 := by
    rw [ζ.tsupport_eq]
    intro s hs
    rw [Metric.mem_closedBall, Real.dist_eq] at hs
    change |s - 2| ≤ 1 / 2 at hs
    constructor <;> linarith [abs_le.mp hs]
  have hsp : tsupport (ζ : ℝ → ℝ) ⊆ Ioi (0 : ℝ) :=
    fun s hsζ => lt_trans (by norm_num : (0 : ℝ) < 1) (hs hsζ).1
  have hc : HasCompactSupport (fun s : BellmanPositiveTime => ζ s.val / s.val ^ 2) := by
    convert! (bellmanRadialTest_compact ζ ζ.hasCompactSupport hsp).mul_right
      (f' := fun s : BellmanPositiveTime => (s.val ^ 2)⁻¹) using 1
  have hcont : Continuous (fun s : BellmanPositiveTime => ζ s.val / s.val ^ 2) :=
    (ζ.continuous.comp continuous_subtype_val).div (continuous_subtype_val.pow 2)
      (fun s => pow_ne_zero 2 s.property.ne')
  have hn : ∀ s : BellmanPositiveTime, 0 ≤ ζ s.val / s.val ^ 2 :=
    fun s => div_nonneg ζ.nonneg (sq_nonneg _)
  have hself : ζ (2 : ℝ) = 1 := ζ.one_of_mem_closedBall (Metric.mem_closedBall_self
    (by norm_num : (0 : ℝ) ≤ 1 / 4))
  have hp : 0 < (∫ s, ζ s.val / s.val ^ 2 ∂bellmanRadialWeight β) := by
    apply hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hc hn
      (x := ⟨2, by norm_num⟩)
    change ζ (2 : ℝ) / 2 ^ 2 ≠ 0
    rw [hself]
    norm_num
  exact ⟨ζ, ζ.contDiff, ζ.hasCompactSupport, hs, hp,
    bellmanRadialWeight_deriv_relation β 1 3 (by norm_num) (by norm_num) ζ ζ.contDiff hs⟩

end HypoellipticAleksandrov.KineticAleksandrov
