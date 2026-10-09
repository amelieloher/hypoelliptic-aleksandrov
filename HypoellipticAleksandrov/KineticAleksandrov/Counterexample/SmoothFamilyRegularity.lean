module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.SmoothFamilyGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsRegularity
import Mathlib.Analysis.Matrix.Normed

/-! # Fixed smooth functions have bounded velocity Hessians on the cylinder -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Set HypoellipticAleksandrov.Parabolic HypoellipticAleksandrov.KineticAleksandrov.Evolution
open scoped Matrix.Norms.Elementwise

/-- Native joint smoothness supplies all genuine kinetic derivative continuity properties. -/
theorem isKineticC112On_univ_of_joint_smooth {d : ℕ} (u : KineticPoint d → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × (PDE.Vec d × PDE.Vec d) =>
      u ((KineticPoint.equivProd d).symm z))) : IsKineticC112On u univ := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (u ∘ evolutionHomeomorph d) := by
    simpa only [Function.comp_def, evolutionHomeomorph, Homeomorph.trans_apply] using!
      hu.comp (evolutionProdCLE d).contDiff
  exact TheoremA.isKineticC112On_of_contDiffOn (u := u) isOpen_univ
    (by simpa only [preimage_univ] using hs.contDiffOn)

/-- Native joint smoothness gives continuity of the actual kinetic velocity Hessian. -/
theorem continuous_kineticVelocityHessian_of_joint_smooth {d : ℕ}
    (u : KineticPoint d → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × (PDE.Vec d × PDE.Vec d) =>
      u ((KineticPoint.equivProd d).symm z))) : Continuous (kineticVelocityHessian u) :=
  continuousOn_univ.mp
    (isKineticC112On_univ_of_joint_smooth u hu).continuousOn_kineticVelocityHessian

/-- The Hessian of each fixed smooth function is bounded on the entire cylinder.
The bound is chosen after the function and is not claimed uniform across a sequence. -/
theorem kineticVelocityHessian_bound_on_cylinder {d : ℕ}
    (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) (u : KineticPoint d → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × (PDE.Vec d × PDE.Vec d) =>
      u ((KineticPoint.equivProd d).symm z))) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ P ∈ backwardCylinder P₀ R, ∀ i k,
      ‖kineticVelocityHessian u P i k‖ ≤ M := by
  obtain ⟨K, hK, hQK⟩ := backwardCylinder_subset_compact P₀ R hR
  have hc := continuous_kineticVelocityHessian_of_joint_smooth u hu
  obtain ⟨B, hb⟩ := (hK.image hc).isBounded.exists_norm_le
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro P hP i k
  apply (Matrix.norm_le_iff (le_max_right B 0)).mp _ i k
  exact (hb _ ⟨P, hQK hP, rfl⟩).trans (le_max_left _ _)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
