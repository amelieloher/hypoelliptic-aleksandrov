module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftCalculus
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.BarrierFunctionSpaceLinear
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic

/-! # Operator homogeneity for propagating the positive sphere bound -/

@[expose] public section
noncomputable section
open Set Filter Topology
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- Equality on a neighborhood identifies the complete Bellman expression. -/
theorem bellman_operator_germ_eq {phi psi : (ℝ × ℝ) → ℝ} {q : ℝ × ℝ}
    (h : phi =ᶠ[𝓝 q] psi) (b : ℝ) : bellmanOperator b phi q = bellmanOperator b psi q := by
  have hv : bellmanDv phi =ᶠ[𝓝 q] bellmanDv psi :=
    (h.fderiv (𝕜 := ℝ)).mono (fun x hx => congrArg (fun L => L (0, 1)) hx)
  unfold bellmanOperator bellmanDx bellmanDvv
  rw [h.fderiv_eq, hv.fderiv_eq]

/-- Constant multiplication scales the complete Bellman expression. -/
theorem bellman_operator_mul (c b : ℝ) (phi : (ℝ × ℝ) → ℝ) (q : ℝ × ℝ) :
    bellmanOperator b (fun z => c * phi z) q = c * bellmanOperator b phi q := by
  change bellmanOperator b (c • phi) q = _
  rw [bellmanOperator, bellmanDx, fderiv_const_smul_field, bellmanDvv_smul]
  simp only [Pi.smul_apply, smul_apply, smul_eq_mul, bellmanOperator, bellmanDx]
  ring

/-- The Bellman operator has degree alpha minus two on a C² homogeneous function. -/
theorem bellman_homogeneous_operator_scaling {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) (r : ℝ) (hr : 0 < r)
    (q : ℝ × ℝ) (hq : q ∈ bellmanPuncturedSet) (b : ℝ) :
    bellmanOperator b phi (bellmanPlaneDilation r q) =
      r ^ (alpha - 2) * bellmanOperator b phi q := by
  have he : (fun z => phi (bellmanPlaneDilation r z)) =ᶠ[𝓝 q]
      fun z => r ^ alpha * phi z := by
    filter_upwards [bellmanPuncturedSet_isOpen.mem_nhds hq] with z hz
    exact h.2 r hr z hz
  have hj : r ^ 2 * bellmanOperator b phi (bellmanPlaneDilation r q) =
      r ^ alpha * bellmanOperator b phi q := by
    rw [← bellmanOperator_comp_dilation r hr phi h.1 q hq b,
      bellman_operator_germ_eq he b, bellman_operator_mul]
  apply mul_left_cancel₀ (pow_ne_zero 2 hr.ne')
  calc
    r ^ 2 * bellmanOperator b phi (bellmanPlaneDilation r q) =
        r ^ alpha * bellmanOperator b phi q := hj
    _ = r ^ 2 * (r ^ (alpha - 2) * bellmanOperator b phi q) := by
      rw [← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hr]
      congr 2
      ring

end HypoellipticAleksandrov.KineticAleksandrov
