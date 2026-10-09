module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.KillingCalculus
public import HypoellipticAleksandrov.Parabolic.ScalarClassical
public import PDEFoundation.Sobolev.OneDimensional.SmoothTransport
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Scalar jets of the affine endpoint heat barrier -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic

/-- The unique native coordinate direction agrees with scalar differentiation,
including Mathlib's total derivative convention at nonsmooth points. -/
theorem scalar_deriv_eq_native (f : PDE.Vec 1 → ℝ) (v : PDE.Vec 1) :
    deriv (fun t => f (fun _ => t)) (v 0) = (fderiv ℝ f v) (PDE.basisVec 0) := by
  have h := PDE.scalarToVecOneContinuousLinearEquiv.comp_right_fderiv
    (f := f) (x := v 0)
  have he := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) h
  have h1 : (PDE.scalarToVecOneContinuousLinearEquiv : ℝ →L[ℝ] PDE.Vec 1) 1 =
      PDE.basisVec 0 := PDE.scalarToVecOneContinuousLinearEquiv_one
  have hv : PDE.scalarToVecOneContinuousLinearEquiv (v 0) = v := by
    ext i
    have hi := Fin.eq_zero i
    subst i
    rfl
  rw [ContinuousLinearMap.comp_apply, h1, hv] at he
  exact he


/-- The one-dimensional native Hessian is the iterated scalar derivative. -/
theorem scalarSpatialHessian_one (u : TimeVelocity 1 → ℝ) (p : TimeVelocity 1) :
    scalarSpatialHessian u p 0 0 =
      deriv (deriv (fun v => u (p.1, fun _ => v))) (p.2 0) := by
  let g : PDE.Vec 1 → PDE.Vec 1 :=
    fun v => scalarSpatialGradient u (p.1, v)
  have hg : (fun t : ℝ => g (fun _ => t) 0) =
      deriv (fun v => u (p.1, fun _ => v)) := by
    funext t
    exact (scalar_deriv_eq_native (fun v => u (p.1, v)) (fun _ => t)).symm
  have he := scalar_deriv_eq_native (fun v => g v 0) p.2
  rw [hg] at he
  have hi : (fderiv ℝ (fun v => g v 0) p.2) (PDE.basisVec 0) =
      (fderiv ℝ g p.2 (PDE.basisVec 0)) 0 := by
    let E := PDE.scalarToVecOneContinuousLinearEquiv.symm
    change (fderiv ℝ (E ∘ g) p.2) (PDE.basisVec 0) = _
    rw [E.comp_fderiv]
    rfl
  exact hi.symm.trans he.symm

/-- Affine pullback of the scalar heat barrier has its expected first derivative. -/
theorem deriv_intervalHeat_affine (lam θ s e : ℝ) :
    deriv (fun y => intervalHeat lam θ (s * (y - e))) =
      fun y => s * deriv (intervalHeat lam θ) (s * (y - e)) := by
  funext y
  have h := (hasDerivAt_intervalHeat_space lam θ (s * (y - e))).comp y
    (((hasDerivAt_id y).sub_const e).const_mul s)
  dsimp only [Function.comp_def, id_eq] at h
  rw [h.deriv, (hasDerivAt_intervalHeat_space lam θ (s * (y - e))).deriv]
  ring

/-- Affine pullback of the scalar heat barrier has its expected second derivative. -/
theorem deriv2_intervalHeat_affine {lam θ : ℝ} (_hlam : 0 < lam) (_hθ : 0 < θ)
    (s e y : ℝ) :
    deriv (deriv (fun z => intervalHeat lam θ (s * (z - e)))) y =
      s ^ 2 * deriv (deriv (intervalHeat lam θ)) (s * (y - e)) := by
  have hd : DifferentiableAt ℝ (deriv (intervalHeat lam θ)) (s * (y - e)) := by
    rw [deriv_intervalHeat_space]
    fun_prop
  have h := (hd.hasDerivAt.comp y (((hasDerivAt_id y).sub_const e).const_mul s)).const_mul s
  dsimp only [Function.comp_def, id_eq] at h
  rw [deriv_intervalHeat_affine, h.deriv]
  ring

/-- The regularized terminal barrier based at an endpoint, with inward orientation `s`. -/
def endpointHeat (lam τ ε s e : ℝ) (p : TimeVelocity 1) : ℝ :=
  intervalHeat lam (τ - p.1 + ε) (s * (p.2 0 - e))

/-- Joint regularity of the regularized endpoint barrier. -/
theorem contDiffAt_endpointHeat {lam τ ε s e : ℝ} (hlam : 0 < lam)
    (p : TimeVelocity 1) (hp : 0 < τ - p.1 + ε) :
    ContDiffAt ℝ (⊤ : ℕ∞) (endpointHeat lam τ ε s e) p := by
  have hg : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : TimeVelocity 1 => (τ - q.1 + ε, s * (q.2 0 - e))) p :=
    ((contDiffAt_const.sub contDiffAt_fst).add contDiffAt_const).prodMk
      (contDiffAt_const.mul
        (((contDiff_apply ℝ ℝ (0 : Fin 1)).contDiffAt.comp p contDiffAt_snd).sub
          contDiffAt_const))
  exact (contDiffAt_intervalHeat hlam (τ - p.1 + ε, s * (p.2 0 - e)) hp).comp p
    (f := fun q : TimeVelocity 1 => (τ - q.1 + ε, s * (q.2 0 - e))) hg

/-- The time derivative reverses the forward half-line time. -/
theorem scalarTimeDerivative_endpointHeat {lam τ ε s e : ℝ} (hlam : 0 < lam)
    (p : TimeVelocity 1) (hp : 0 < τ - p.1 + ε) :
    scalarTimeDerivative (endpointHeat lam τ ε s e) p =
      -deriv (fun θ => intervalHeat lam θ (s * (p.2 0 - e))) (τ - p.1 + ε) := by
  have h := (hasDerivAt_intervalHeat_time hlam hp (s * (p.2 0 - e))).comp p.1
    (((hasDerivAt_const p.1 τ).sub (hasDerivAt_id p.1)).add_const ε)
  dsimp only [Function.comp_def, id_eq, Pi.sub_apply] at h
  change deriv (fun r => intervalHeat lam (τ - r + ε) (s * (p.2 0 - e))) p.1 = _
  rw [h.deriv, (hasDerivAt_intervalHeat_time hlam hp (s * (p.2 0 - e))).deriv]
  ring

/-- The native Hessian is the scalar heat Hessian when the orientation has square one. -/
theorem scalarSpatialHessian_endpointHeat {lam τ ε s e : ℝ} (hlam : 0 < lam)
    (hs : s ^ 2 = 1) (p : TimeVelocity 1) (hp : 0 < τ - p.1 + ε) :
    scalarSpatialHessian (endpointHeat lam τ ε s e) p 0 0 =
      deriv (deriv (intervalHeat lam (τ - p.1 + ε))) (s * (p.2 0 - e)) := by
  rw [scalarSpatialHessian_one]
  change deriv (deriv (fun v => intervalHeat lam (τ - p.1 + ε) (s * (v - e))))
    (p.2 0) = _
  rw [deriv2_intervalHeat_affine hlam hp, hs, one_mul]

/-- The endpoint barrier is a backward supersolution under the source ellipticity bound. -/
theorem endpointHeat_operator_nonpos {lam τ ε s e : ℝ} (hlam : 0 < lam)
    (hs : s ^ 2 = 1) (B : CoefficientField 1) (p : TimeVelocity 1)
    (hp : 0 < τ - p.1 + ε) (hx : 0 ≤ s * (p.2 0 - e))
    (hB : lam ≤ B p.1 p.2 0 0) :
    scalarParabolicOperator B 0 (endpointHeat lam τ ε s e) p ≤ 0 := by
  rw [scalarParabolicOperator_apply, scalarTimeDerivative_endpointHeat hlam p hp]
  simp only [matrixContraction, Fin.sum_univ_one, Pi.zero_apply, PDE.vecDot,
    zero_mul, add_zero]
  rw [scalarSpatialHessian_endpointHeat hlam hs p hp]
  have h := (intervalHeat_supersolution hlam hp hx hB).2.2
  linarith

end HypoellipticAleksandrov.KineticAleksandrov.Interval
