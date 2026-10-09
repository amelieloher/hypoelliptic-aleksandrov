module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularCoordinates
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # Log radius as an actual coordinate homeomorphism -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- Positive radius and log radius are homeomorphic, with exponential as the inverse. -/
def bellmanLogRadiusHomeomorph : BellmanPositiveTime ≃ₜ ℝ where
  toFun s := Real.log s.val
  invFun t := ⟨Real.exp t, Real.exp_pos t⟩
  left_inv s := by
    apply Subtype.ext
    exact Real.exp_log s.property
  right_inv t := Real.log_exp t
  continuous_toFun := continuous_subtype_val.log (fun s => s.property.ne')
  continuous_invFun := Real.continuous_exp.subtype_mk _

/-- The log-radius/angular product coordinates retain the literal angular variable. -/
def bellmanLogAngularHomeomorph : (BellmanPositiveTime × ℝ) ≃ₜ (ℝ × ℝ) :=
  bellmanLogRadiusHomeomorph.prodCongr (Homeomorph.refl ℝ)

/-- Radial scaling becomes translation in the log-radius coordinate. -/
theorem bellmanLogAngularHomeomorph_scale (r : ℝ) (hr : 0 < r)
    (w : BellmanPositiveTime × ℝ) :
    bellmanLogAngularHomeomorph (⟨r * w.1.val, mul_pos hr w.1.property⟩, w.2) =
      (Real.log r + (bellmanLogAngularHomeomorph w).1,
        (bellmanLogAngularHomeomorph w).2) := by
  apply Prod.ext
  · exact Real.log_mul hr.ne' w.1.property.ne'
  · rfl

end HypoellipticAleksandrov.KineticAleksandrov
