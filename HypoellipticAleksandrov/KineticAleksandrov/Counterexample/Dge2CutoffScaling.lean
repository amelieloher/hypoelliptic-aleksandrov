module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2CutoffRescaling
import Mathlib.Tactic.FieldSimp

/-! # Exact dilation identities for the cutoff interpolation -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- Dilation transports the shifted regularization base exactly. -/
theorem seedBase_dilate {d : ℕ} (sigma R : ℝ) (hR : R ≠ 0) (z e : PDE.Vec d) :
    seedBase sigma (R • z) e = R ^ 2 * seedBase (R⁻¹ * sigma) z (R⁻¹ • e) := by
  have heq : R • z - e = R • (z - R⁻¹ • e) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hR, one_smul]
  unfold seedBase
  rw [heq, PDE.vecNormSq_smul]
  field_simp

/-- The radial cutoff becomes the fixed unit-radius cutoff under dilation. -/
theorem radialCutoff_dilate {d : ℕ} (R : ℝ) (hR : R ≠ 0) (z : PDE.Vec d) :
    radialCutoff R (R • z) = radialCutoff 1 z := by
  unfold radialCutoff
  rw [PDE.vecNormSq_smul]
  congr 1
  field_simp

/-- The source cutoff is exactly the rescaled interpolation times R to the alpha. -/
theorem cutoffProfile_dilate_rescaled {d : ℕ} (alpha C₀ sigma R : ℝ) (hR : 0 < R)
    (z e : PDE.Vec d) :
    cutoffProfile alpha C₀ sigma R (R • z) e =
      Real.rpow R alpha * rescaledCutoff alpha sigma
        (C₀ / Real.rpow R alpha) R⁻¹ e z := by
  have hr : 0 < Real.rpow R alpha := Real.rpow_pos_of_pos hR _
  have hrad : radialProfile alpha (R • z) = Real.rpow R alpha * radialProfile alpha z := by
    unfold radialProfile
    rw [PDE.vecNormSq_smul]
    simp only [Real.rpow_eq_pow]
    rw [Real.mul_rpow (sq_nonneg R) (PDE.vecNormSq_nonneg z),
      ← Real.rpow_natCast_mul hR.le]
    norm_num only [Nat.cast_ofNat]
    congr 2
    ring
  have hseed : Real.rpow (seedBase sigma (R • z) e) (alpha / 2) =
      Real.rpow R alpha * Real.rpow (seedBase (R⁻¹ * sigma) z (R⁻¹ • e)) (alpha / 2) := by
    rw [seedBase_dilate sigma R hR.ne']
    simp only [Real.rpow_eq_pow]
    have hn : 0 ≤ seedBase (R⁻¹ * sigma) z (R⁻¹ • e) := by
      exact add_nonneg (sq_nonneg _) (PDE.vecNormSq_nonneg _)
    rw [Real.mul_rpow (sq_nonneg R) hn, ← Real.rpow_natCast_mul hR.le]
    norm_num only [Nat.cast_ofNat]
    congr 2
    ring
  unfold cutoffProfile rescaledCutoff seed
  rw [hrad, radialCutoff_dilate R hR.ne', hseed]
  field_simp

/-- Exact first-jet scaling for a smooth scalar function on native vectors. -/
theorem fderiv_scaledFunction {d : ℕ} (F : PDE.Vec d → ℝ)
    (hF : Differentiable ℝ F) (a R : ℝ) (z w : PDE.Vec d) :
    fderiv ℝ (fun y => a * F (R • y)) z w = a * R * fderiv ℝ F (R • z) w := by
  have hh := ((hF (R • z)).hasFDerivAt.comp z
    ((hasFDerivAt_id z).const_smul R)).const_mul a
  have hh' : HasFDerivAt (fun y => a * F (R • y))
      (a • (fderiv ℝ F (R • z)).comp (R • ContinuousLinearMap.id ℝ (PDE.Vec d))) z := by
    convert hh using 1
    funext y
    rfl
  rw [hh'.fderiv]
  simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul]
  ring

/-- Exact Hessian scaling for a smooth scalar function on native vectors. -/
theorem hessian_scaledFunction {d : ℕ} (F : PDE.Vec d → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (a R : ℝ) (z w u : PDE.Vec d) :
    fderiv ℝ (fun y => fderiv ℝ (fun b => a * F (R • b)) y w) z u =
      a * R ^ 2 * fderiv ℝ (fun y => fderiv ℝ F y w) (R • z) u := by
  have hFd : Differentiable ℝ F := hF.differentiable (by simp)
  have heq : (fun y => fderiv ℝ (fun b => a * F (R • b)) y w) =
      (fun y => (a * R) * fderiv ℝ F (R • y) w) := by
    funext y
    exact fderiv_scaledFunction F hFd a R y w
  have hd : Differentiable ℝ (fun y => fderiv ℝ F y w) :=
    ((hF.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply
      contDiff_const).differentiable (by simp)
  rw [heq]
  calc
    _ = (a * R) * R * fderiv ℝ (fun y => fderiv ℝ F y w) (R • z) u :=
      fderiv_scaledFunction (fun y => fderiv ℝ F y w) hd (a * R) R z u
    _ = _ := by ring

/-- The fixed-annulus Hessian is the physical cutoff Hessian times a positive scalar. -/
theorem rescaledCutoff_hessian {d : ℕ} (alpha C₀ sigma R : ℝ)
    (hsigma : 0 < sigma) (hR : 0 < R) (e z w u : PDE.Vec d) :
    fderiv ℝ (fun a => fderiv ℝ
      (rescaledCutoff alpha sigma (C₀ / Real.rpow R alpha) R⁻¹ e) a w) z u =
      (Real.rpow R alpha)⁻¹ * R ^ 2 *
        fderiv ℝ (fun a => fderiv ℝ (fun b => cutoffProfile alpha C₀ sigma R b e) a w)
          (R • z) u := by
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun b => cutoffProfile alpha C₀ sigma R b e) :=
    (contDiff_cutoffProfile alpha C₀ sigma R hsigma hR).comp
      (contDiff_id.prodMk contDiff_const)
  have heq : rescaledCutoff alpha sigma (C₀ / Real.rpow R alpha) R⁻¹ e =
      (fun b => (Real.rpow R alpha)⁻¹ * cutoffProfile alpha C₀ sigma R (R • b) e) := by
    funext b
    rw [cutoffProfile_dilate_rescaled alpha C₀ sigma R hR b e]
    simp only [Real.rpow_eq_pow]
    rw [← mul_assoc, inv_mul_cancel₀ (Real.rpow_pos_of_pos hR alpha).ne', one_mul]
  rw [heq]
  exact hessian_scaledFunction _ hF _ R z w u

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
