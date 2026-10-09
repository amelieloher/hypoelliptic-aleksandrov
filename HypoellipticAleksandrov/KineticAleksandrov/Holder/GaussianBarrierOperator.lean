module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.GaussianBarrierProfileVelocity
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.GaussianBarrierProfileTransport
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.BarrierSignMatrix
import Mathlib.Tactic

/-! # Exact multiplied operator formula for the constructed source barrier -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Parabolic Scaling

/-- The source Gaussian operator identity without division by the amplitude. -/
theorem gaussianBarrier_backwardOperator {d : ℕ} (A : FullKineticCoefficient d)
    {lam h : ℝ} (hlam : 0 < lam) (hh : 0 < h) (Lam H L ell tminus sblock : ℝ)
    {x v : ℝ → PDE.Vec d} (hx : ContDiff ℝ (⊤ : ℕ∞) x)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hkin : ∀ s, HasDerivAt x (v s) s)
    (P : KineticPoint d) (hs : 0 < P.time - tminus - sblock) :
    backwardOperator A (gaussianBarrier lam Lam H h L ell tminus sblock x v) P =
      ell * Real.exp (-Xi d lam Lam H h * (P.time - tminus - sblock) -
        qform lam h (P.time - tminus - sblock)
          (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus))) *
      (-Xi d lam Lam H h +
        lam * PDE.vecNormSq (pform lam h (P.time - tminus - sblock)
          (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus))) +
        2 * PDE.vecDot (deriv v (P.time - tminus))
          (pform lam h (P.time - tminus - sblock)
            (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus))) +
        2 * (gramian lam h (P.time - tminus - sblock))⁻¹ 1 1 *
          (fullKineticCoefficientAt A P).trace -
        4 * PDE.vecDot (pform lam h (P.time - tminus - sblock)
          (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus)))
          ((fullKineticCoefficientAt A P).mulVec
            (pform lam h (P.time - tminus - sblock)
              (P.position - x (P.time - tminus)) (P.velocity - v (P.time - tminus))))) := by
  let s := P.time - tminus
  let sigma := s - sblock
  let y := P.position - x s
  let V := P.velocity - v s
  let pvec := pform lam h sigma y V
  let G := Real.exp (-Xi d lam Lam H h * sigma - qform lam h sigma y V)
  let B := fullKineticCoefficientAt A P
  have hf := contDiff_gaussianProfile (d := d) hlam hh Lam H L ell sblock
  have hg : kineticVelocityGradient (fun Q : KineticPoint d =>
      gaussianProfile lam Lam H h L ell sblock (s, (Q.position, Q.velocity)))
      ⟨0, y, V⟩ = (-2 * ell * G) • pvec :=
    gaussianProfile_velocityGradient lam Lam H L ell sblock hh hs y V
  have hHess : kineticVelocityHessian (fun Q : KineticPoint d =>
      gaussianProfile lam Lam H h L ell sblock (s, (Q.position, Q.velocity)))
      ⟨0, y, V⟩ =
      (fun i j => ell * G * (4 * pvec i * pvec j -
        2 * (gramian lam h sigma)⁻¹ 1 1 * (1 : PDE.Mat d) i j)) := by
    rw [kineticVelocityHessian_eq_sliceHessian]
    ext i j
    exact gaussianProfile_velocityHessian lam Lam H L ell sblock hh hs y V i j
  rw [gaussianBarrier_eq_movingLift,
    movingLift_backwardOperator A hf hx hv hkin tminus P,
    gaussianProfile_transport hlam hh Lam H L ell sblock hs y V]
  change ell * G * (-Xi d lam Lam H h + lam * PDE.vecNormSq pvec) -
    PDE.vecDot (deriv v s) _ - matrixContraction B _ = _
  rw [hg, hHess, matrixContraction_gaussian]
  rw [PDE.vecDot_comm (deriv v s), vecDot_smul_left, PDE.vecDot_comm pvec]
  change _ = ell * G * (-Xi d lam Lam H h + lam * PDE.vecNormSq pvec +
    2 * PDE.vecDot (deriv v s) pvec + 2 * (gramian lam h sigma)⁻¹ 1 1 * B.trace -
    4 * PDE.vecDot pvec (B.mulVec pvec))
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Holder
