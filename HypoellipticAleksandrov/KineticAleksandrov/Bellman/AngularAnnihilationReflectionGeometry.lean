module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationHomogeneity
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureJets
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Tactic

/-! # Reflection of the actual punctured position–velocity plane -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- Simultaneous reflection of position and velocity on the punctured plane. -/
def bellmanReflection : BellmanPuncturedPlane ≃ₜ BellmanPuncturedPlane where
  toFun q := ⟨-q.val, by
    change -q.val ≠ (0 : ℝ × ℝ)
    exact neg_ne_zero.mpr q.property⟩
  invFun q := ⟨-q.val, by
    change -q.val ≠ (0 : ℝ × ℝ)
    exact neg_ne_zero.mpr q.property⟩
  left_inv q := by apply Subtype.ext; exact neg_neg _
  right_inv q := by apply Subtype.ext; exact neg_neg _
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Reflection commutes with every positive kinetic dilation. -/
theorem bellmanReflection_dilation (r : ℝ) (hr : 0 < r) (q : BellmanPuncturedPlane) :
    bellmanReflection (bellmanDilation r hr q) =
      bellmanDilation r hr (bellmanReflection q) := by
  apply Subtype.ext
  apply Prod.ext
  · change -(r ^ 3 * q.val.1) = r ^ 3 * (-q.val.1)
    ring
  · change -(r * q.val.2) = r * (-q.val.2)
    ring

/-- The first reflected test jet changes sign. -/
theorem bellman_reflected_fderiv (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (q e : ℝ × ℝ) :
    fderiv ℝ (fun z => φ (-z)) q e = -fderiv ℝ φ (-q) e := by
  have hd := (hφ.differentiable (by simp) (-q)).hasFDerivAt.comp q
    ((hasFDerivAt_id q).neg)
  change fderiv ℝ (φ ∘ Neg.neg) q e = _
  rw [hd.fderiv]
  change fderiv ℝ φ (-q) (-e) = -fderiv ℝ φ (-q) e
  exact map_neg _ _

/-- The second velocity jet of a reflected test retains its sign. -/
theorem bellman_reflected_second_velocity (φ : ℝ × ℝ → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (q : ℝ × ℝ) :
    fderiv ℝ (fun z => fderiv ℝ (fun w => φ (-w)) z (0, 1)) q (0, 1) =
      fderiv ℝ (fun z => fderiv ℝ φ z (0, 1)) (-q) (0, 1) := by
  have hjet := bellman_contDiff_direction hφ (0, 1)
  have he : (fun z => fderiv ℝ (fun w => φ (-w)) z (0, 1)) =
      (fun z => -(fderiv ℝ φ (-z) (0, 1))) := by
    funext z
    exact bellman_reflected_fderiv φ hφ z (0, 1)
  let g := fun z => fderiv ℝ φ z (0, 1)
  have hd := ((hjet.differentiable (by simp) (-q)).hasFDerivAt.comp q
    ((hasFDerivAt_id q).neg)).neg
  rw [he]
  change fderiv ℝ (-(g ∘ Neg.neg)) q (0, 1) = _
  rw [hd.fderiv]
  change -(fderiv ℝ g (-q) (-(0, 1))) = fderiv ℝ g (-q) (0, 1)
  rw [map_neg, neg_neg]

end HypoellipticAleksandrov.KineticAleksandrov
