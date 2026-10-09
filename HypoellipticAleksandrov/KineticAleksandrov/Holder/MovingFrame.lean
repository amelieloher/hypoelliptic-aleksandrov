module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullCutoffJets
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Tactic

/-! # Literal moving coordinates along a kinetic skeleton -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Parabolic Scaling

/-- Source moving-frame coordinates, without any change of velocity normalization. -/
def movingCoordinates {d : ℕ} (tminus : ℝ) (x v : ℝ → PDE.Vec d)
    (P : KineticPoint d) : ℝ × (PDE.Vec d × PDE.Vec d) :=
  (P.time - tminus, (P.position - x (P.time - tminus),
    P.velocity - v (P.time - tminus)))

/-- The literal scalar function in moving coordinates. -/
def movingLift {d : ℕ} (f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ)
    (tminus : ℝ) (x v : ℝ → PDE.Vec d) (P : KineticPoint d) : ℝ :=
  f (movingCoordinates tminus x v P)

/-- Smooth paths yield a smooth moving-coordinate map in native raw coordinates. -/
theorem contDiff_movingCoordinates {d : ℕ} {x v : ℝ → PDE.Vec d}
    (hx : ContDiff ℝ (⊤ : ℕ∞) x) (hv : ContDiff ℝ (⊤ : ℕ∞) v) (tminus : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun Q : ℝ × (PDE.Vec d × PDE.Vec d) =>
      movingCoordinates tminus x v ⟨Q.1, Q.2.1, Q.2.2⟩) := by
  unfold movingCoordinates
  exact (contDiff_fst.sub contDiff_const).prodMk
    ((contDiff_fst.comp contDiff_snd).sub
      (hx.comp (contDiff_fst.sub contDiff_const)) |>.prodMk
      ((contDiff_snd.comp contDiff_snd).sub
        (hv.comp (contDiff_fst.sub contDiff_const))))

/-- Transport of the moving frame includes precisely the skeleton acceleration term. -/
theorem hasDerivAt_movingCoordinates_transport {d : ℕ} (tminus : ℝ)
    (x v : ℝ → PDE.Vec d) (P : KineticPoint d)
    (hx : HasDerivAt x (v (P.time - tminus)) (P.time - tminus))
    (hv : DifferentiableAt ℝ v (P.time - tminus)) :
    HasDerivAt (fun r : ℝ => movingCoordinates tminus x v
      ⟨P.time + r, P.position + r • P.velocity, P.velocity⟩)
      (1, (P.velocity - v (P.time - tminus), -deriv v (P.time - tminus))) 0 := by
  have ht : HasDerivAt (fun r : ℝ => P.time + r - tminus) 1 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_add P.time).sub_const tminus
  have hx' : HasDerivAt x (v (P.time - tminus)) (P.time + 0 - tminus) := by
    simpa only [add_zero] using hx
  have hxc := hx'.scomp 0 ht
  have hv' : HasDerivAt v (deriv v (P.time - tminus)) (P.time + 0 - tminus) := by
    simpa only [add_zero] using hv.hasDerivAt
  have hvc := hv'.scomp 0 ht
  have hpos : HasDerivAt (fun r : ℝ => P.position + r • P.velocity) P.velocity 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const P.velocity).const_add P.position
  simpa only [movingCoordinates, Pi.sub_apply, Function.comp_def, mul_one, one_smul,
    zero_add, add_zero, zero_sub] using
    ht.prodMk ((hpos.sub hxc).prodMk ((hasDerivAt_const 0 P.velocity).sub hvc))

/-- The moving-frame transport identity, before the velocity Hessian is subtracted. -/
theorem movingLift_transport {d : ℕ}
    {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ} {x v : ℝ → PDE.Vec d}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hx : ContDiff ℝ (⊤ : ℕ∞) x)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hkin : ∀ s, HasDerivAt x (v s) s)
    (tminus : ℝ) (P : KineticPoint d) :
    kineticTimeDerivative (movingLift f tminus x v) P +
      PDE.vecDot P.velocity (kineticPositionGradient (movingLift f tminus x v) P) =
    fderiv ℝ f (movingCoordinates tminus x v P)
      (1, (P.velocity - v (P.time - tminus), 0)) -
    fderiv ℝ f (movingCoordinates tminus x v P)
      (0, (0, deriv v (P.time - tminus))) := by
  have hcomp := hf.comp (contDiff_movingCoordinates hx hv tminus)
  have hd : DifferentiableAt ℝ (rawLift (movingLift f tminus x v)) (rawPoint P) :=
    hcomp.differentiable (by norm_num) _
  have hcurve := hasDerivAt_movingCoordinates_transport tminus x v P
    (hkin _) (hv.differentiable (by norm_num) _)
  have hder := (hf.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt 0 hcurve
  have htransport := hasDerivAt_kinetic_transport hd
  have heq := htransport.unique hder
  simp only [add_zero, zero_smul] at heq
  rw [heq]
  rw [← map_sub]
  congr 1
  ext <;> simp

end HypoellipticAleksandrov.KineticAleksandrov.Holder
