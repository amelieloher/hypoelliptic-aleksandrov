module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Topology.MetricSpace.Algebra

/-! # Strong L2 convergence from uniform scalar error bounds

On a finite measure carrier, a vanishing uniform error controls the actual quotient L2 norm.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory
open scoped Topology ENNReal

/-- Vanishing uniform errors give strong convergence of the selected L2 quotient classes. -/
theorem tendsto_toLp_two_of_ae_sub_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (u : ℕ → X → ℝ) (hu : ∀ n, MemLp (u n) 2 μ)
    (v : X → ℝ) (hv : MemLp v 2 μ) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 ≤ ε n) (hlim : Tendsto ε atTop (𝓝 0))
    (hb : ∀ n, ∀ᵐ x ∂μ, |u n x - v x| ≤ ε n) :
    Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 (hv.toLp v)) := by
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let K : ℝ := (measureUnivNNReal μ : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹
  have hnorm (n : ℕ) : ‖(hu n).toLp (u n) - hv.toLp v‖ ≤ K * ε n := by
    rw [← MemLp.toLp_sub (hu n) hv]
    apply Lp.norm_le_of_ae_bound (hε n)
    filter_upwards [((hu n).sub hv).coeFn_toLp, hb n] with x hx hbx
    rw [hx, Real.norm_eq_abs]
    exact hbx
  have hzero : Tendsto (fun n => K * ε n) atTop (𝓝 0) := by
    simpa only [mul_zero] using hlim.const_mul K
  exact tendsto_iff_norm_sub_tendsto_zero.2
    (squeeze_zero (fun _ => norm_nonneg _) hnorm hzero)

end HypoellipticAleksandrov.Parabolic.LocalHolder
