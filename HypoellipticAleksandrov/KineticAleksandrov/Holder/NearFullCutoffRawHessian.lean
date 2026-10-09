module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullCutoffHessian
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierFinite
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Tactic

/-! # Continuous raw-coordinate jets of the smooth unit cutoff -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Parabolic Scaling

/-- An affine slice Hessian is the restriction of the ambient second derivative. -/
theorem sliceHessian_comp_affine_embedding {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    {ι : PDE.Vec d → E} (hιc : ContDiff ℝ 2 ι)
    {J : PDE.Vec d →L[ℝ] E} (hι : ∀ x, HasFDerivAt ι J x)
    (x : PDE.Vec d) (i j : Fin d) :
    sliceHessian (fun w => f (ι w)) x i j =
      fderiv ℝ (fderiv ℝ f) (ι x) (J (PDE.basisVec i)) (J (PDE.basisVec j)) := by
  have hg : ContDiffAt ℝ 2 (fun w => f (ι w)) x := (hf.comp hιc).contDiffAt
  rw [sliceHessian_apply_eq_sndFDeriv hg]
  have hd : ∀ w, DifferentiableAt ℝ f w := hf.differentiable (by norm_num)
  have hfd : ∀ w, fderiv ℝ (fun z => f (ι z)) w = (fderiv ℝ f (ι w)).comp J :=
    fun w => ((hd (ι w)).hasFDerivAt.comp w (hι w)).fderiv
  have hgd := (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [← fderiv_clm_apply_const_eval hgd (PDE.basisVec j) (PDE.basisVec i)]
  have hfun : (fun w => fderiv ℝ (fun z => f (ι z)) w (PDE.basisVec j)) =
      fun w => fderiv ℝ f (ι w) (J (PDE.basisVec j)) := by
    funext w
    rw [hfd w]
    rfl
  rw [hfun]
  have hdf := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) (ι x)
  have hh := (hdf.clm_apply (differentiableAt_const (J (PDE.basisVec j)))).hasFDerivAt
  have hc := hh.comp x (hι x)
  rw [show (fun w => fderiv ℝ f (ι w) (J (PDE.basisVec j))) =
    (fun z => fderiv ℝ f z (J (PDE.basisVec j))) ∘ ι from rfl, hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  rw [fderiv_clm_apply_const_eval hdf]

/-- Unit velocity-Hessian entries are the corresponding ambient coordinate derivatives. -/
theorem unitCutoffVelocitySlice_hessian {d : ℕ}
    {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (Q : KineticPoint d) (i j : Fin d) :
    sliceHessian (unitCutoffVelocitySlice f Q) Q.velocity i j =
      fderiv ℝ (fderiv ℝ f) (KineticPoint.equivProd d Q)
        (0, (0, PDE.basisVec i)) (0, (0, PDE.basisVec j)) := by
  let J : PDE.Vec d →L[ℝ] ℝ × (PDE.Vec d × PDE.Vec d) :=
    (0 : PDE.Vec d →L[ℝ] ℝ).prod
      ((0 : PDE.Vec d →L[ℝ] PDE.Vec d).prod (ContinuousLinearMap.id ℝ (PDE.Vec d)))
  have hι : ∀ w, HasFDerivAt (fun z : PDE.Vec d => (Q.time, (Q.position, z))) J w :=
    fun w => (hasFDerivAt_const Q.time w).prodMk
      ((hasFDerivAt_const Q.position w).prodMk (hasFDerivAt_id w))
  have h := sliceHessian_comp_affine_embedding (hf.of_le (by simp))
    (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)) hι Q.velocity i j
  change sliceHessian (fun w => f (Q.time, (Q.position, w))) Q.velocity i j =
    fderiv ℝ (fderiv ℝ f) (Q.time, (Q.position, Q.velocity))
      (0, (0, PDE.basisVec i)) (0, (0, PDE.basisVec j))
  simpa only [J, ContinuousLinearMap.prod_apply, zero_apply, ContinuousLinearMap.id_apply,
    id_eq]
    using h

/-- The unit velocity Hessian depends continuously on the physical point. -/
theorem continuous_unitCutoffVelocityHessian {d : ℕ}
    {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Continuous (fun Q : KineticPoint d =>
      sliceHessian (unitCutoffVelocitySlice f Q) Q.velocity) := by
  have hc : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (((hf.of_le (show (3 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)).fderiv_right
      (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).continuous
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have h0 := (hc.comp (KineticPoint.homeomorphProd d).continuous).clm_apply
    (continuous_const (y := ((0, (0, PDE.basisVec i)) : ℝ × (PDE.Vec d × PDE.Vec d))))
  have h1 := h0.clm_apply (continuous_const
    (y := ((0, (0, PDE.basisVec j)) : ℝ × (PDE.Vec d × PDE.Vec d))))
  exact h1.congr (fun Q => (unitCutoffVelocitySlice_hessian hf Q i j).symm)

/-- The unit transport derivative depends continuously on the physical point. -/
theorem continuous_unitCutoffTransport {d : ℕ}
    {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Continuous (fun Q : KineticPoint d =>
      fderiv ℝ f (KineticPoint.equivProd d Q) (1, (Q.velocity, 0))) := by
  have h0 := ((hf.of_le (show (2 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)).fderiv_right
    (m := 1) (by norm_num)).continuous.comp (KineticPoint.homeomorphProd d).continuous
  exact h0.clm_apply
    (continuous_const.prodMk (continuous_velocity.prodMk continuous_const))

end HypoellipticAleksandrov.KineticAleksandrov.Holder
