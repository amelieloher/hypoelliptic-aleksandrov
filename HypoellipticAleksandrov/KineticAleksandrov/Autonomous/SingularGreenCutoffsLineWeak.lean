module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsFiber
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Position-fiber integration by parts without a hidden origin mass -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Set MeasureTheory Filter
open scoped Topology

/-- A continuous function with a locally integrable derivative off zero has no point defect. -/
theorem singular_line_weak_derivative (f g : ℝ → ℝ) (hf : Continuous f)
    (hg : LocallyIntegrable g volume) (hd : ∀ x : ℝ, x ≠ 0 → HasDerivAt f (g x) x)
    (test : ℝ → ℝ) (ht : ContDiff ℝ 1 test) (hs : HasCompactSupport test) :
    (∫ x, f x * deriv test x) = -(∫ x, g x * test x) := by
  have h1 := hg.integrable_smul_right_of_hasCompactSupport ht.continuous hs
  have h2 := (hf.locallyIntegrable (μ := volume)).integrable_smul_right_of_hasCompactSupport
    (ht.continuous_deriv (by norm_num)) hs.deriv
  simp only [smul_eq_mul] at h1 h2
  let H := fun x => f x * test x
  let D := fun x => g x * test x + f x * deriv test x
  have hD : Integrable D volume := h1.add h2
  have hH : Continuous H := hf.mul ht.continuous
  have hHk : HasCompactSupport H := hs.mul_left
  have hdH (x : ℝ) (hx : x ≠ 0) : HasDerivAt H (D x) x :=
    (hd x hx).mul ((ht.differentiable (by norm_num) x).hasDerivAt)
  have hneg := integral_Iic_of_hasDerivAt_of_tendsto
    (hH.continuousAt.continuousWithinAt (x := (0 : ℝ)))
    (fun x hx => hdH x hx.ne) hD.integrableOn
    (hHk.is_zero_at_infty.mono_left atBot_le_cocompact)
  have hpos := integral_Ioi_of_hasDerivAt_of_tendsto
    (hH.continuousAt.continuousWithinAt (x := (0 : ℝ)))
    (fun x hx => hdH x hx.ne') hD.integrableOn
    (hHk.is_zero_at_infty.mono_left atTop_le_cocompact)
  have he := integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hD
  rw [compl_Iic, hneg, hpos] at he
  have hz : (∫ x, D x) = 0 := by linarith only [he]
  rw [integral_add h1 h2] at hz
  linarith only [hz]

/-- Each actual position derivative fiber is locally integrable on the full position line. -/
theorem barrier_dx_fiber_locallyIntegrable {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) (ha : 0 < alpha) (ha1 : alpha < 1) (v : ℝ) :
    LocallyIntegrable (fun X => bellmanDx phi (X, v)) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR, hRb⟩ := hK.isBounded.exists_pos_norm_lt
  apply (barrier_jet_fiber_integrable h ha ha1 v (-R) R).1.mono_set
  intro x hx
  have hh := hRb x hx
  rw [Real.norm_eq_abs] at hh
  exact abs_le.mp hh.le

/-- The actual position convolution moves its derivative onto the source jet even at v=0. -/
theorem barrier_position_fiber_weak_dx {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) (ha : 0 < alpha) (ha1 : alpha < 1)
    (v : ℝ) (test : ℝ → ℝ) (ht : ContDiff ℝ 1 test) (hs : HasCompactSupport test) :
    (∫ X, bellmanOriginExtension phi (X, v) * deriv test X) =
      -(∫ X, bellmanDx phi (X, v) * test X) := by
  apply singular_line_weak_derivative _ _
    ((h.origin_extension_continuous ha).comp (continuous_id.prodMk continuous_const))
    (barrier_dx_fiber_locallyIntegrable h ha ha1 v) ?_ test ht hs
  intro X hX
  have hq : (X, v) ∈ bellmanPuncturedSet := fun he => hX (congrArg Prod.fst he)
  have hd := (h.1.contDiffAt (bellmanPuncturedSet_isOpen.mem_nhds hq)).differentiableAt
    (by norm_num)
  exact (bellman_hasDerivAt_first hd).congr_of_eventuallyEq
    ((barrierExtension_eventuallyEq phi hq).comp_tendsto
      ((continuous_id.prodMk continuous_const).tendsto X))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
