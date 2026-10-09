module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Group.Integral

/-!
# A smooth terminal-layer cutoff

`layerStep` is a smooth step, `0` on `(-∞,1]` and `1` on `[2,∞)`; `layerKernel` is its
derivative, a continuous function supported in `[1,2]` with total mass `1`.  The rescaled kernels
`t ↦ h⁻¹ layerKernel ((r - t)/h)` approximate the point mass at `t = r` from the left.  We prove
the affine substitution identity used to pass to the limit `h → 0`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set Filter
open scoped Topology

/-- A smooth step: `0` on `(-∞, 1]`, `1` on `[2, ∞)`. -/
def layerStep (s : ℝ) : ℝ := Real.smoothTransition (s - 1)

/-- The derivative of the smooth step, supported in `[1,2]` with total mass one. -/
def layerKernel : ℝ → ℝ := deriv layerStep

theorem contDiff_layerStep : ContDiff ℝ (⊤ : ℕ∞) layerStep :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

theorem layerStep_of_le {s : ℝ} (h : s ≤ 1) : layerStep s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem layerStep_of_ge {s : ℝ} (h : 2 ≤ s) : layerStep s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem hasDerivAt_layerStep (s : ℝ) : HasDerivAt layerStep (layerKernel s) s :=
  ((contDiff_layerStep.differentiable (by simp)) s).hasDerivAt

theorem continuous_layerKernel : Continuous layerKernel :=
  contDiff_layerStep.continuous_deriv (by simp)

theorem layerKernel_eq_zero_of_le {s : ℝ} (h : s ≤ 1) : layerKernel s = 0 := by
  have hz : ∀ x ∈ Iio (1 : ℝ), layerKernel x = 0 := by
    intro x hx
    have hev : layerStep =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hx] with y hy using layerStep_of_le (le_of_lt hy)
    exact (hev.deriv_eq).trans (deriv_const _ _)
  have hcl : IsClosed {x | layerKernel x = 0} := isClosed_eq continuous_layerKernel continuous_const
  have := closure_minimal (fun x hx => hz x hx) hcl
  rw [closure_Iio] at this
  exact this h

theorem layerKernel_eq_zero_of_ge {s : ℝ} (h : 2 ≤ s) : layerKernel s = 0 := by
  have hz : ∀ x ∈ Ioi (2 : ℝ), layerKernel x = 0 := by
    intro x hx
    have hev : layerStep =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy using layerStep_of_ge (le_of_lt hy)
    exact (hev.deriv_eq).trans (deriv_const _ _)
  have hcl : IsClosed {x | layerKernel x = 0} := isClosed_eq continuous_layerKernel continuous_const
  have := closure_minimal (fun x hx => hz x hx) hcl
  rw [closure_Ioi] at this
  exact this h

theorem hasCompactSupport_layerKernel : HasCompactSupport layerKernel := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (1 : ℝ)) (b := 2))
  intro x hx
  by_cases h : x ≤ 1
  · exact layerKernel_eq_zero_of_le h
  · exact layerKernel_eq_zero_of_ge (by
      by_contra h2
      exact hx ⟨le_of_lt (not_le.1 h), le_of_lt (not_le.1 h2)⟩)

theorem integrable_layerKernel : Integrable layerKernel :=
  continuous_layerKernel.integrable_of_hasCompactSupport hasCompactSupport_layerKernel

/-- The smooth step has total derivative mass one. -/
theorem integral_layerKernel : ∫ s, layerKernel s = 1 := by
  have h0 : Tendsto layerStep atBot (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Iic_mem_atBot (1 : ℝ)] with y hy using (layerStep_of_le hy).symm
  have h1 : Tendsto layerStep atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Ici_mem_atTop (2 : ℝ)] with y hy using (layerStep_of_ge hy).symm
  have := integral_of_hasDerivAt_of_tendsto hasDerivAt_layerStep integrable_layerKernel h0 h1
  simpa using this

/-- The kernel is bounded. -/
theorem exists_bound_layerKernel : ∃ M : ℝ, 0 ≤ M ∧ ∀ s, |layerKernel s| ≤ M := by
  obtain ⟨M, hM⟩ := continuous_layerKernel.bounded_above_of_compact_support
    hasCompactSupport_layerKernel
  exact ⟨max M 0, le_max_right _ _, fun s => by
    simpa only [Real.norm_eq_abs] using (hM s).trans (le_max_left _ _)⟩

/-- The affine substitution `t = r - h s` against the rescaled kernel. -/
theorem integral_layer_substitution (r h : ℝ) (hh : 0 < h) (F : ℝ → ℝ) :
    ∫ t, h⁻¹ * layerKernel ((r - t) / h) * F t =
      ∫ s, layerKernel s * F (r - h * s) := by
  set g : ℝ → ℝ := fun t => h⁻¹ * layerKernel ((r - t) / h) * F t with hg
  have h1 : ∫ t, g t = ∫ x, g (r - x) := (integral_sub_left_eq_self g volume r).symm
  have h2 : ∫ x, g (r - x) = h • ∫ s, g (r - h * s) := by
    have := Measure.integral_comp_mul_left (fun x => g (r - x)) h
    simp only [abs_inv, abs_of_pos hh] at this
    rw [this, smul_smul, mul_inv_cancel₀ hh.ne', one_smul]
  have h3 : ∀ s, g (r - h * s) = h⁻¹ * (layerKernel s * F (r - h * s)) := by
    intro s
    simp only [hg, sub_sub_cancel]
    rw [mul_div_cancel_left₀ _ hh.ne']
    ring
  rw [h1, h2]
  simp_rw [h3]
  rw [integral_const_mul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul]

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
