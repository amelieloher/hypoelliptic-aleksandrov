module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.MovingFrame
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic

/-! # The complete source operator in moving skeleton coordinates -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Parabolic Scaling

/-- Velocity translation leaves the velocity Hessian unchanged in moving coordinates. -/
theorem movingLift_velocityHessian {d : ℕ}
    {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (tminus : ℝ) (x v : ℝ → PDE.Vec d)
    (P : KineticPoint d) :
    kineticVelocityHessian (movingLift f tminus x v) P =
      kineticVelocityHessian
        (fun Q : KineticPoint d => f (P.time - tminus, (Q.position, Q.velocity)))
        ⟨0, P.position - x (P.time - tminus), P.velocity - v (P.time - tminus)⟩ := by
  let s := P.time - tminus
  let y := P.position - x s
  let g := fun V : PDE.Vec d => f (s, (y, V))
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hf.comp
    (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))
  have hslice : (fun V : PDE.Vec d => movingLift f tminus x v ⟨P.time, P.position, V⟩) =
      (fun V => g (-v s + (1 : ℝ) • V)) := by
    funext V
    simp only [movingLift, movingCoordinates, s, y, g, one_smul]
    congr 2
    abel_nf
  rw [kineticVelocityHessian_eq_sliceHessian, hslice,
    kineticVelocityHessian_eq_sliceHessian]
  have h := sliceHessian_affine (y₀ := -v s) (c := (1 : ℝ)) (Y := P.velocity)
    (hg.contDiffAt.of_le (by norm_cast))
  simpa only [one_smul, one_pow, neg_add_eq_sub] using h

/-- The source time slice is the raw time-direction derivative. -/
theorem deriv_raw_time_slice {d : ℕ}
    {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (s : ℝ) (y V : PDE.Vec d) :
    deriv (fun r => f (r, (y, V))) s = fderiv ℝ f (s, (y, V)) (1, (0, 0)) := by
  have hc := (hasDerivAt_id s).prodMk (hasDerivAt_const s (y, V))
  exact ((hf.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt s hc).deriv

/-- The source position-line derivative is the raw transport-direction derivative. -/
theorem deriv_raw_position_line {d : ℕ}
    {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (s : ℝ) (y V : PDE.Vec d) :
    deriv (fun r : ℝ => f (s, (y + r • V, V))) 0 =
      fderiv ℝ f (s, (y, V)) (0, (V, 0)) := by
  have hx : HasDerivAt (fun r : ℝ => y + r • V) V 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const V).const_add y
  have hc := (hasDerivAt_const 0 s).prodMk (hx.prodMk (hasDerivAt_const 0 V))
  simpa only [Function.comp_def, zero_smul, add_zero] using
    ((hf.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt 0 hc).deriv

/-- The complete source chain rule, with precisely the acceleration correction. -/
theorem movingLift_backwardOperator {d : ℕ} (A : FullKineticCoefficient d)
    {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ} {x v : ℝ → PDE.Vec d}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hx : ContDiff ℝ (⊤ : ℕ∞) x)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hkin : ∀ s, HasDerivAt x (v s) s)
    (tminus : ℝ) (P : KineticPoint d) :
    backwardOperator A (movingLift f tminus x v) P =
      deriv (fun s => f (s, (P.position - x (P.time - tminus),
        P.velocity - v (P.time - tminus)))) (P.time - tminus) +
      deriv (fun r : ℝ => f (P.time - tminus,
        (P.position - x (P.time - tminus) + r • (P.velocity - v (P.time - tminus)),
          P.velocity - v (P.time - tminus)))) 0 -
      PDE.vecDot (deriv v (P.time - tminus))
        (kineticVelocityGradient (fun Q : KineticPoint d =>
          f (P.time - tminus, (Q.position, Q.velocity)))
          ⟨0, P.position - x (P.time - tminus), P.velocity - v (P.time - tminus)⟩) -
      matrixContraction (fullKineticCoefficientAt A P)
        (kineticVelocityHessian (fun Q : KineticPoint d =>
          f (P.time - tminus, (Q.position, Q.velocity)))
          ⟨0, P.position - x (P.time - tminus), P.velocity - v (P.time - tminus)⟩) := by
  let s := P.time - tminus
  let y := P.position - x s
  let V := P.velocity - v s
  have hslice : DifferentiableAt ℝ (rawLift (fun Q : KineticPoint d =>
      f (s, (Q.position, Q.velocity)))) (rawPoint (⟨0, y, V⟩ : KineticPoint d)) := by
    exact (hf.comp (contDiff_const.prodMk contDiff_snd)).differentiable (by norm_num) _
  rw [backwardOperator, movingLift_transport hf hx hv hkin,
    movingLift_velocityHessian hf, deriv_raw_time_slice hf, deriv_raw_position_line hf]
  rw [vecDot_kineticVelocityGradient hslice]
  change _ = _
  have hvel : fderiv ℝ (rawLift (fun Q : KineticPoint d => f (s, (Q.position, Q.velocity))))
      (rawPoint (⟨0, y, V⟩ : KineticPoint d)) (0, (0, deriv v s)) =
      fderiv ℝ f (s, (y, V)) (0, (0, deriv v s)) := by
    have hc := (hasFDerivAt_const s (rawPoint (⟨0, y, V⟩ : KineticPoint d))).prodMk
      (hasFDerivAt_snd (𝕜 := ℝ) (p := rawPoint (⟨0, y, V⟩ : KineticPoint d)))
    change fderiv ℝ (f ∘ fun Q : ℝ × (PDE.Vec d × PDE.Vec d) => (s, Q.2))
      (rawPoint (⟨0, y, V⟩ : KineticPoint d)) (0, (0, deriv v s)) = _
    rw [((hf.differentiable (by norm_num) _).hasFDerivAt.comp _ hc).fderiv]
    simp [rawPoint]
  rw [hvel]
  rw [← map_add]
  simp only [movingCoordinates, s, y, V, Prod.mk_add_mk, zero_add, add_zero]

end HypoellipticAleksandrov.KineticAleksandrov.Holder
