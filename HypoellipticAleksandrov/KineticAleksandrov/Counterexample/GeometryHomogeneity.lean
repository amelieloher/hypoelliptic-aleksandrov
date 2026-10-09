module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Geometry
public import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.FieldSimp

/-! # Differentiating kinetic homogeneity -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- The continuous linear map realizing kinetic dilation. -/
def dilationLinearMap (d : ℕ) (r : ℝ) : XV d →L[ℝ] XV d :=
  (r ^ 3 • ContinuousLinearMap.fst ℝ (PDE.Vec d) (PDE.Vec d)).prod
    (r • ContinuousLinearMap.snd ℝ (PDE.Vec d) (PDE.Vec d))

/-- The linear dilation agrees with the literal coordinate dilation. -/
theorem dilationLinearMap_apply {d : ℕ} (r : ℝ) (q : XV d) :
    dilationLinearMap d r q = dilate r q := rfl

/-- Kinetic dilation has its constant linear differential. -/
theorem hasFDerivAt_dilate {d : ℕ} (r : ℝ) (q : XV d) :
    HasFDerivAt (dilate r : XV d → XV d) (dilationLinearMap d r) q :=
  (dilationLinearMap d r).hasFDerivAt

/-- Differentiation of the homogeneity identity in an arbitrary native direction. -/
theorem homogeneous_fderiv_identity {d : ℕ} (H : XV d → ℝ) (alpha r : ℝ)
    (_hr : 0 < r)
    (hhom : ∀ q, H (dilate r q) = Real.rpow r alpha * H q)
    (q w : XV d) (hq : DifferentiableAt ℝ H q)
    (hrq : DifferentiableAt ℝ H (dilate r q)) :
    fderiv ℝ H (dilate r q) (dilate r w) = Real.rpow r alpha * fderiv ℝ H q w := by
  have he := congrArg (fun f : XV d → ℝ => fderiv ℝ f q w) (funext hhom)
  rw [fderiv_fun_comp q hrq (hasFDerivAt_dilate r q).differentiableAt,
    fderiv_const_mul hq] at he
  simpa only [(hasFDerivAt_dilate r q).fderiv, ContinuousLinearMap.comp_apply,
    dilationLinearMap_apply, smul_apply, smul_eq_mul] using he

/-- A position derivative of a homogeneous profile has degree alpha minus three. -/
theorem homogeneous_dx_identity {d : ℕ} (H : XV d → ℝ) (alpha r : ℝ)
    (hr : 0 < r) (hhom : ∀ q, H (dilate r q) = Real.rpow r alpha * H q)
    (q : XV d) (hq : DifferentiableAt ℝ H q)
    (hrq : DifferentiableAt ℝ H (dilate r q)) (i : Fin d) :
    dx H (dilate r q) i = Real.rpow r (alpha - 3) * dx H q i := by
  have he := homogeneous_fderiv_identity H alpha r hr hhom q (Pi.single i 1, 0) hq hrq
  have hw : dilate r ((Pi.single i 1, 0) : XV d) = r ^ 3 • (Pi.single i 1, 0) := by
    simp [dilate, Prod.smul_mk]
  rw [hw, map_smul] at he
  change r ^ 3 * dx H (dilate r q) i = Real.rpow r alpha * dx H q i at he
  simp only [Real.rpow_eq_pow] at he ⊢
  rw [Real.rpow_sub hr]
  rw [Real.rpow_ofNat]
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (pow_ne_zero 3 hr.ne')).mpr
  simpa only [mul_comm, div_mul_eq_mul_div] using he

/-- A velocity derivative of a homogeneous profile has degree alpha minus one. -/
theorem homogeneous_dv_identity {d : ℕ} (H : XV d → ℝ) (alpha r : ℝ)
    (hr : 0 < r) (hhom : ∀ q, H (dilate r q) = Real.rpow r alpha * H q)
    (q : XV d) (hq : DifferentiableAt ℝ H q)
    (hrq : DifferentiableAt ℝ H (dilate r q)) (i : Fin d) :
    dv H (dilate r q) i = Real.rpow r (alpha - 1) * dv H q i := by
  have he := homogeneous_fderiv_identity H alpha r hr hhom q (0, Pi.single i 1) hq hrq
  have hw : dilate r ((0, Pi.single i 1) : XV d) = r • (0, Pi.single i 1) := by
    simp [dilate, Prod.smul_mk]
  rw [hw, map_smul] at he
  change r * dv H (dilate r q) i = Real.rpow r alpha * dv H q i at he
  simp only [Real.rpow_eq_pow] at he ⊢
  rw [Real.rpow_sub hr]
  rw [Real.rpow_one, div_mul_eq_mul_div]
  apply (eq_div_iff hr.ne').mpr
  simpa only [mul_comm, div_mul_eq_mul_div] using he

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
