module

public import HypoellipticAleksandrov.KineticAleksandrov.Operator
public import PDEFoundation.Ambient.EuclideanNorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import PDEFoundation.Geometry.EuclideanBall.Topology
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Ring

/-!
# Literal stationary geometry for Appendix C

The gauge uses the Euclidean squared norms, independently of the native supremum norm.
The derivative selectors below are total Frechet derivatives on the native product.
Their identification with weak jets on axes is a separate analytic step.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- Native position--velocity coordinates. -/
abbrev XV (d : ℕ) := PDE.Vec d × PDE.Vec d

/-- The Euclidean kinetic gauge in Appendix C. -/
noncomputable def rho {d : ℕ} (q : XV d) : ℝ :=
  Real.rpow (PDE.vecNormSq q.1 + (PDE.vecNormSq q.2) ^ 3) (1 / 6)

/-- Kinetic dilation of position and velocity. -/
def dilate {d : ℕ} (r : ℝ) (q : XV d) : XV d := (r ^ 3 • q.1, r • q.2)

/-- Position derivative selectors on the native product. -/
noncomputable def dx {d : ℕ} (H : XV d → ℝ) (q : XV d) : PDE.Vec d :=
  fun i => fderiv ℝ H q (Pi.single i 1, 0)

/-- Velocity derivative selectors on the native product. -/
noncomputable def dv {d : ℕ} (H : XV d → ℝ) (q : XV d) : PDE.Vec d :=
  fun i => fderiv ℝ H q (0, Pi.single i 1)

/-- Velocity Hessian selectors, indexed as the derivative of component `k` along `i`. -/
noncomputable def dvv {d : ℕ} (H : XV d → ℝ) (q : XV d) : PDE.Mat d :=
  fun i k => fderiv ℝ (fun z => dv H z k) q (0, Pi.single i 1)

/-- Stationary transport minus velocity diffusion. -/
noncomputable def statOp {d : ℕ} (A : XV d → PDE.Mat d)
    (H : XV d → ℝ) (q : XV d) : ℝ :=
  PDE.vecDot q.2 (dx H q) - matrixContraction (A q) (dvv H q)

/-- The kinetic gauge is nonnegative. -/
theorem rho_nonneg {d : ℕ} (q : XV d) : 0 ≤ rho q :=
  Real.rpow_nonneg
    (add_nonneg (PDE.vecNormSq_nonneg _) (pow_nonneg (PDE.vecNormSq_nonneg _) _)) _

/-- The kinetic gauge vanishes at the origin. -/
@[simp] theorem rho_zero (d : ℕ) : rho (0 : XV d) = 0 := by
  simp [rho, PDE.vecNormSq, PDE.vecDot]

/-- Unit dilation preserves both coordinates. -/
@[simp] theorem dilate_one {d : ℕ} (q : XV d) : dilate 1 q = q := by
  simp [dilate]

/-- Every dilation preserves the origin. -/
@[simp] theorem dilate_zero {d : ℕ} (r : ℝ) : dilate r (0 : XV d) = 0 := by
  simp [dilate]

/-- Kinetic dilations compose multiplicatively. -/
theorem dilate_mul {d : ℕ} (r s : ℝ) (q : XV d) :
    dilate r (dilate s q) = dilate (r * s) q := by
  simp only [dilate, smul_smul, mul_pow]

/-- The sixth power inside the gauge has kinetic degree six. -/
theorem gauge_polynomial_dilate {d : ℕ} (r : ℝ) (q : XV d) :
    PDE.vecNormSq (dilate r q).1 + (PDE.vecNormSq (dilate r q).2) ^ 3 =
      r ^ 6 * (PDE.vecNormSq q.1 + (PDE.vecNormSq q.2) ^ 3) := by
  simp only [dilate, PDE.vecNormSq_smul]
  ring

/-- The gauge scales linearly under positive kinetic dilations. -/
theorem rho_dilate {d : ℕ} (r : ℝ) (hr : 0 < r) (q : XV d) :
    rho (dilate r q) = r * rho q := by
  unfold rho
  simp only [Real.rpow_eq_pow]
  rw [gauge_polynomial_dilate]
  rw [Real.mul_rpow (show 0 ≤ r ^ (6 : ℕ) from pow_nonneg hr.le _) (z := (1 / 6 : ℝ))
    (show 0 ≤ PDE.vecNormSq q.1 + PDE.vecNormSq q.2 ^ (3 : ℕ) from
      add_nonneg (PDE.vecNormSq_nonneg _) (pow_nonneg (PDE.vecNormSq_nonneg _) _))]
  have hpower : (r ^ (6 : ℕ)) ^ (1 / 6 : ℝ) = r := by
    rw [← Real.rpow_natCast_mul hr.le]
    norm_num
  rw [hpower]

/-- The gauge is continuous also at its unique singular point. -/
theorem continuous_rho (d : ℕ) : Continuous (rho (d := d)) := by
  unfold rho
  simp only [Real.rpow_eq_pow]
  exact (Real.continuous_rpow_const (by norm_num : 0 ≤ (1 / 6 : ℝ))).comp
    ((PDE.continuous_vecNormSq.comp continuous_fst).add
      ((PDE.continuous_vecNormSq.comp continuous_snd).pow 3))

/-- The gauge vanishes only at the origin. -/
theorem rho_eq_zero_iff {d : ℕ} (q : XV d) : rho q = 0 ↔ q = 0 := by
  have hx := PDE.vecNormSq_nonneg q.1
  have hv := PDE.vecNormSq_nonneg q.2
  have hv3 : 0 ≤ PDE.vecNormSq q.2 ^ (3 : ℕ) := pow_nonneg hv _
  rw [rho, Real.rpow_eq_pow, Real.rpow_eq_zero (add_nonneg hx hv3) (by norm_num)]
  constructor
  · intro h
    have hx0 : PDE.vecNormSq q.1 = 0 := le_antisymm (by linarith only [h, hv3]) hx
    have hv0 : PDE.vecNormSq q.2 = 0 := by
      have hv30 : PDE.vecNormSq q.2 ^ (3 : ℕ) = 0 := by linarith only [h, hx0]
      exact (pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hv30
    exact Prod.ext (PDE.vecNormSq_eq_zero hx0) (PDE.vecNormSq_eq_zero hv0)
  · rintro rfl
    simp [PDE.vecNormSq, PDE.vecDot]

/-- The full-product position selectors agree with the classical slice gradient. -/
theorem dx_eq_classicalGradient {d : ℕ} (H : XV d → ℝ)
    (hH : Differentiable ℝ H) (q : XV d) :
    dx H q = PDE.classicalGradient (fun x => H (x, q.2)) q.1 := by
  funext i
  unfold dx PDE.classicalGradient PDE.basisVec
  rw [fderiv_fun_comp q.1 (hH q)
    (differentiableAt_id.prodMk (differentiableAt_const q.2))]
  have hinj := DifferentiableAt.fderiv_prodMk
    (differentiableAt_id (𝕜 := ℝ) (x := q.1)) (differentiableAt_const q.2)
  simp only [id_eq] at hinj
  rw [hinj]
  simp only [fderiv_id, fderiv_const_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    zero_apply]

/-- The full-product velocity selectors agree with the classical slice gradient. -/
theorem dv_eq_classicalGradient {d : ℕ} (H : XV d → ℝ)
    (hH : Differentiable ℝ H) (q : XV d) :
    dv H q = PDE.classicalGradient (fun v => H (q.1, v)) q.2 := by
  funext i
  unfold dv PDE.classicalGradient PDE.basisVec
  rw [fderiv_fun_comp q.2 (hH q)
    ((differentiableAt_const q.1).prodMk differentiableAt_id)]
  have hinj := DifferentiableAt.fderiv_prodMk (differentiableAt_const q.1)
    (differentiableAt_id (𝕜 := ℝ) (x := q.2))
  simp only [id_eq] at hinj
  rw [hinj]
  simp only [fderiv_id, fderiv_const_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    zero_apply]

/-- The stationary velocity Hessian agrees with the kinetic slice Hessian. -/
theorem dvv_eq_kineticVelocityHessian {d : ℕ} (H : XV d → ℝ)
    (hH : Differentiable ℝ H) (hDv : Differentiable ℝ (dv H)) (P : KineticPoint d) :
    dvv H (P.position, P.velocity) =
      Parabolic.kineticVelocityHessian (fun z => H (z.position, z.velocity)) P := by
  have heq : (fun v => PDE.classicalGradient (fun w => H (P.position, w)) v) =
      (fun v => dv H (P.position, v)) := by
    funext v
    exact (dv_eq_classicalGradient H hH (P.position, v)).symm
  unfold Parabolic.kineticVelocityHessian
  rw [heq]
  funext i k
  unfold dvv PDE.basisVec
  rw [fderiv_apply (hDv (P.position, P.velocity)) k]
  rw [fderiv_fun_comp P.velocity (hDv (P.position, P.velocity))
    ((differentiableAt_const P.position).prodMk differentiableAt_id)]
  have hinj := DifferentiableAt.fderiv_prodMk (differentiableAt_const P.position)
    (differentiableAt_id (𝕜 := ℝ) (x := P.velocity))
  simp only [id_eq] at hinj
  rw [hinj]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.prod_apply, fderiv_const_apply, fderiv_id,
    zero_apply, ContinuousLinearMap.id_apply]

/-- Stationary transport and diffusion use the native backward operator convention. -/
theorem backwardOperator_stationary {d : ℕ} (A : XV d → PDE.Mat d)
    (H : XV d → ℝ) (hH : Differentiable ℝ H) (hDv : Differentiable ℝ (dv H))
    (P : KineticPoint d) :
    backwardOperator (fun _t x v => A (x, v))
      (fun z => H (z.position, z.velocity)) P = statOp A H (P.position, P.velocity) := by
  unfold backwardOperator fullKineticCoefficientAt Parabolic.kineticTimeDerivative
    Parabolic.kineticPositionGradient statOp
  dsimp only
  rw [deriv_const, zero_add, ← dx_eq_classicalGradient H hH (P.position, P.velocity),
    ← dvv_eq_kineticVelocityHessian H hH hDv P]

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
