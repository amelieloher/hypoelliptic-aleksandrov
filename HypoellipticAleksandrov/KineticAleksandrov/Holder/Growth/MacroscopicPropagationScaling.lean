module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.ReferenceGeometry
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Tactic

/-! # Physical transport of the constructed reference skeleton -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

/-- Position path in physical affine coordinates, parameterized from its own start time. -/
def physicalPathPosition {d : ℕ} (P0 : KineticPoint d) (scale start : ℝ)
    (x : ℝ → PDE.Vec d) (s : ℝ) : PDE.Vec d :=
  P0.position + scale ^ 3 • x (s / scale ^ 2) +
    (scale ^ 2 * start + s) • P0.velocity

/-- Velocity of the physically transported position path. -/
def physicalPathVelocity {d : ℕ} (P0 : KineticPoint d) (scale : ℝ)
    (v : ℝ → PDE.Vec d) (s : ℝ) : PDE.Vec d :=
  P0.velocity + scale • v (s / scale ^ 2)

/-- Physical transport preserves position-velocity derivative compatibility. -/
theorem physicalPath_derivative {d : ℕ} (P0 : KineticPoint d) {scale : ℝ}
    (_hscale : scale ≠ 0) (start : ℝ) {x v : ℝ → PDE.Vec d}
    (hkin : ∀ s, HasDerivAt x (v s) s) (s : ℝ) :
    HasDerivAt (physicalPathPosition P0 scale start x)
      (physicalPathVelocity P0 scale v s) s := by
  apply hasDerivAt_pi.mpr
  intro i
  have hin := (hasDerivAt_id s).div_const (scale ^ 2)
  have hx := ((hasDerivAt_pi.mp (hkin (s / scale ^ 2))) i).comp s hin
  have hfirst := (hx.const_mul (scale ^ 3)).const_add (P0.position i)
  have hlast := ((hasDerivAt_const s (scale ^ 2 * start)).add
    (hasDerivAt_id s)).mul_const (P0.velocity i)
  have h := hfirst.add hlast
  have hd : scale ^ 3 * (v (s / scale ^ 2) i * (1 / scale ^ 2)) +
      (0 + 1 : ℝ) * P0.velocity i = physicalPathVelocity P0 scale v s i := by
    simp only [physicalPathVelocity, Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_add]
    field_simp
    ring
  rw [hd] at h
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun t => by
    simp only [physicalPathPosition, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Function.comp_def, id_eq])

/-- Physical transport divides the Euclidean acceleration bound by the length scale. -/
theorem physicalPath_velocity_lipschitz {d : ℕ} (P0 : KineticPoint d) {scale H : ℝ}
    (hscale : 0 < scale) {v : ℝ → PDE.Vec d}
    (hLip : ∀ s t, PDE.vecEuclideanNorm (v s - v t) ≤ H * |s - t|) (s t : ℝ) :
    PDE.vecEuclideanNorm (physicalPathVelocity P0 scale v s -
      physicalPathVelocity P0 scale v t) ≤ (H / scale) * |s - t| := by
  have heq : physicalPathVelocity P0 scale v s - physicalPathVelocity P0 scale v t =
      scale • (v (s / scale ^ 2) - v (t / scale ^ 2)) := by
    simp only [physicalPathVelocity, smul_sub]
    abel
  rw [heq, PDE.vecEuclideanNorm_smul, abs_of_pos hscale]
  have he := mul_le_mul_of_nonneg_left (hLip (s / scale ^ 2) (t / scale ^ 2)) hscale.le
  apply he.trans_eq
  rw [← sub_div, abs_div, abs_of_pos (pow_pos hscale 2)]
  field_simp

/-- The physically transported velocity is continuous. -/
theorem physicalPath_velocity_continuous {d : ℕ} (P0 : KineticPoint d) (scale : ℝ)
    {v : ℝ → PDE.Vec d} (hv : Continuous v) :
    Continuous (physicalPathVelocity P0 scale v) := by
  have ht : Continuous (fun s : ℝ => s / scale ^ 2) := continuous_id.div_const _
  have hc : Continuous (fun s : ℝ => P0.velocity + scale • v (s / scale ^ 2)) :=
    (continuous_const (y := P0.velocity)).add ((hv.comp ht).const_smul scale)
  exact hc

/-- The transported path is a source skeleton on any required closed interval. -/
theorem physicalPath_isSkeleton {d : ℕ} (P0 : KineticPoint d) {scale H : ℝ}
    (hscale : 0 < scale) (start a b : ℝ) {x v : ℝ → PDE.Vec d} (hv : Continuous v)
    (hkin : ∀ s, HasDerivAt x (v s) s)
    (hLip : ∀ s t, PDE.vecEuclideanNorm (v s - v t) ≤ H * |s - t|) :
    IsSkeleton (physicalPathPosition P0 scale start x) (physicalPathVelocity P0 scale v)
      (H / scale) a b :=
  ⟨(physicalPath_velocity_continuous P0 scale hv).continuousOn,
    fun s _ => (physicalPath_derivative P0 hscale.ne' start hkin s).hasDerivWithinAt,
    fun s _ t _ => physicalPath_velocity_lipschitz P0 hscale hLip s t⟩

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
