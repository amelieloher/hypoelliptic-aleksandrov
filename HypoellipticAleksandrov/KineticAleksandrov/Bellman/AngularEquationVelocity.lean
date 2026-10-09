module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationSeparated
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Tactic

/-! # The second velocity derivative of the literal angular separated test -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set Filter
open scoped Topology

/-- Every positive-position point is the literal angular point of its inverse coordinates. -/
theorem bellmanAngularPoint_inverse (q : ℝ × ℝ) (hq : 0 < q.1) :
    (bellmanAngularPoint (bellmanAngularHomeomorph.symm ⟨q, hq⟩)).val = q := by
  exact congrArg Subtype.val (bellmanAngularHomeomorph.apply_symm_apply ⟨q, hq⟩)

/-- The first velocity formula holds throughout the open positive-position half-plane. -/
theorem bellmanSeparatedExpression_velocity_positive (ζ φ : ℝ → ℝ)
    (hζ : Differentiable ℝ ζ) (hφ : Differentiable ℝ φ)
    (q : ℝ × ℝ) (hq : 0 < q.1) :
    fderiv ℝ (bellmanSeparatedExpression ζ φ) q (0, 1) =
      bellmanSeparatedExpression ζ (deriv φ) q / bellmanTestRadius q := by
  let w := bellmanAngularHomeomorph.symm ⟨q, hq⟩
  have he : (bellmanAngularPoint w).val = q := bellmanAngularPoint_inverse q hq
  rw [← he]
  rw [bellmanSeparatedExpression_velocity ζ φ w (hζ _) (hφ _)]
  rw [bellmanSeparatedExpression, bellmanTestRadius_angularPoint,
    bellmanTestAngle_angularPoint]

/-- The second velocity derivative is exactly ζ(s)φ''(y)/s². -/
theorem bellmanSeparatedExpression_velocity_second (ζ φ : ℝ → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (w : BellmanPositiveTime × ℝ) :
    fderiv ℝ (fun q => fderiv ℝ (bellmanSeparatedExpression ζ φ) q (0, 1))
      (bellmanAngularPoint w).val (0, 1) =
      ζ w.1.val * deriv (deriv φ) w.2 / w.1.val ^ 2 := by
  have hφd := (contDiff_infty_iff_deriv.mp hφ).2
  have hs := bellmanSeparatedExpression_hasFDerivAt ζ (deriv φ) w
    (hζ.differentiable (by simp) _) (hφd.differentiable (by simp) _)
  have hn : bellmanTestRadius (bellmanAngularPoint w).val ≠ 0 := by
    rw [bellmanTestRadius_angularPoint]
    exact w.1.property.ne'
  have hi := (hasDerivAt_inv hn).comp_hasFDerivAt (bellmanAngularPoint w).val
    (bellmanTestRadius_hasFDerivAt w)
  have hd := hs.mul hi
  have he : (fun q => fderiv ℝ (bellmanSeparatedExpression ζ φ) q (0, 1)) =ᶠ[
      𝓝 (bellmanAngularPoint w).val]
      (bellmanSeparatedExpression ζ (deriv φ) * (fun y => y⁻¹) ∘ bellmanTestRadius) := by
    have ho : IsOpen {q : ℝ × ℝ | 0 < q.1} := isOpen_lt continuous_const continuous_fst
    have hq : (bellmanAngularPoint w).val ∈ {q : ℝ × ℝ | 0 < q.1} :=
      pow_pos w.1.property 3
    filter_upwards [ho.mem_nhds hq] with q hqp
    rw [bellmanSeparatedExpression_velocity_positive ζ φ
      (hζ.differentiable (by simp)) (hφ.differentiable (by simp)) q hqp]
    rfl
  have hactual := hd.congr_of_eventuallyEq he
  rw [hactual.fderiv]
  simp only [bellmanSeparatedExpression, bellmanTestRadius_angularPoint,
    bellmanTestAngle_angularPoint, Function.comp_apply]
  change (ζ w.1.val * deriv φ w.2) *
      (-(w.1.val ^ 2)⁻¹ * (1 / (3 * w.1.val ^ 2) * 0)) +
    w.1.val⁻¹ * ((ζ w.1.val * deriv (deriv φ) w.2) *
      (w.1.val⁻¹ * 1 - w.2 / (3 * w.1.val ^ 3) * 0) +
      (deriv φ w.2 * deriv ζ w.1.val) * (1 / (3 * w.1.val ^ 2) * 0)) = _
  field_simp [w.1.property.ne']
  ring

end HypoellipticAleksandrov.KineticAleksandrov
