module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarAnsatz
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Profile
import Mathlib.Tactic

/-!
# Native scalar derivative selectors

Classical derivatives on the open position half-planes are identified on the native carrier.
The position axis is excluded here; its weak gluing is a separate step.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter Set
open scoped Topology ContDiff

/-- The one-dimensional position slice through a native point. -/
def scalarPositionSlice (q : XV 1) (x : ℝ) : XV 1 := (fun _ => x, q.2)

/-- The one-dimensional velocity slice through a native point. -/
def scalarVelocitySlice (q : XV 1) (v : ℝ) : XV 1 := (q.1, fun _ => v)

/-- The position slice passes through the native point. -/
theorem scalarPositionSlice_at (q : XV 1) : scalarPositionSlice q (q.1 0) = q := by
  apply Prod.ext
  · funext i
    exact congrArg q.1 (Subsingleton.elim 0 i)
  · rfl

/-- The velocity slice passes through the native point. -/
theorem scalarVelocitySlice_at (q : XV 1) : scalarVelocitySlice q (q.2 0) = q := by
  apply Prod.ext
  · rfl
  · funext i
    exact congrArg q.2 (Subsingleton.elim 0 i)

/-- The slice tangent is the literal native position basis vector. -/
theorem scalarPositionSlice_hasDerivAt (q : XV 1) (x : ℝ) :
    HasDerivAt (scalarPositionSlice q) (Pi.single 0 1, 0) x := by
  have he : (fun _ : Fin 1 => (1 : ℝ)) = Pi.single 0 1 := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp
  rw [← he]
  exact (hasDerivAt_pi.mpr (fun _ => hasDerivAt_id x)).prodMk (hasDerivAt_const x q.2)

/-- The slice tangent is the literal native velocity basis vector. -/
theorem scalarVelocitySlice_hasDerivAt (q : XV 1) (v : ℝ) :
    HasDerivAt (scalarVelocitySlice q) (0, Pi.single 0 1) v := by
  have he : (fun _ : Fin 1 => (1 : ℝ)) = Pi.single 0 1 := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp
  rw [← he]
  exact (hasDerivAt_const v q.1).prodMk (hasDerivAt_pi.mpr (fun _ => hasDerivAt_id v))

/-- Full-product position derivatives agree with their literal scalar slices. -/
theorem dx_eq_scalar_slice (H : XV 1 → ℝ) (q : XV 1)
    (hH : DifferentiableAt ℝ H q) :
    dx H q 0 = deriv (fun x => H (scalarPositionSlice q x)) (q.1 0) := by
  have hh := hH.hasFDerivAt
  rw [← scalarPositionSlice_at q] at hh
  have hd := hh.comp_hasDerivAt (q.1 0) (scalarPositionSlice_hasDerivAt q (q.1 0))
  simpa only [dx, scalarPositionSlice_at, Function.comp_def] using hd.deriv.symm

/-- Full-product velocity derivatives agree with their literal scalar slices. -/
theorem dv_eq_scalar_slice (H : XV 1 → ℝ) (q : XV 1)
    (hH : DifferentiableAt ℝ H q) :
    dv H q 0 = deriv (fun v => H (scalarVelocitySlice q v)) (q.2 0) := by
  have hh := hH.hasFDerivAt
  rw [← scalarVelocitySlice_at q] at hh
  have hd := hh.comp_hasDerivAt (q.2 0) (scalarVelocitySlice_hasDerivAt q (q.2 0))
  simpa only [dv, scalarVelocitySlice_at, Function.comp_def] using hd.deriv.symm

/-- The second native velocity selector agrees with the literal second scalar derivative. -/
theorem dvv_eq_scalar_slice (H : XV 1 → ℝ) (q : XV 1)
    (hH : ContDiffAt ℝ 2 H q) :
    dvv H q 0 0 = deriv (deriv (fun v => H (scalarVelocitySlice q v))) (q.2 0) := by
  have hD : DifferentiableAt ℝ (fun z => dv H z 0) q := by
    exact ((hH.fderiv_right (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).clm_apply
      contDiffAt_const).differentiableAt (by norm_num)
  have hd := dv_eq_scalar_slice (fun z => dv H z 0) q hD
  have hs : Continuous (scalarVelocitySlice q) := by
    unfold scalarVelocitySlice
    fun_prop
  have he : (fun v => dv H (scalarVelocitySlice q v) 0) =ᶠ[𝓝 (q.2 0)]
      deriv (fun v => H (scalarVelocitySlice q v)) := by
    have ht : Tendsto (scalarVelocitySlice q) (𝓝 (q.2 0)) (𝓝 q) := by
      simpa only [scalarVelocitySlice_at] using hs.continuousAt.tendsto (x := q.2 0)
    have hh := ht.eventually (hH.eventually (by norm_num : (2 : ℕ∞ω) ≠ ∞))
    filter_upwards [hh] with v hv
    have ht := dv_eq_scalar_slice H (scalarVelocitySlice q v)
      (hv.differentiableAt (by norm_num))
    simpa only [scalarVelocitySlice, Prod.snd, Prod.fst] using ht
  exact hd.trans he.deriv_eq

/-- The positive-half-plane native ansatz. -/
def scalarNativeAnsatz (gamma : ScalarGamma) (Lam : ℝ) (q : XV 1) : ℝ :=
  scalarAnsatz gamma Lam (q.1 0) (q.2 0)

/-- The literal native ansatz is C² wherever the position coordinate is positive. -/
theorem scalarNativeAnsatz_contDiffAt (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (q : XV 1) (hx : 0 < q.1 0) : ContDiffAt ℝ 2 (scalarNativeAnsatz gamma Lam) q := by
  have hX : ContDiffAt ℝ 2 (fun z : XV 1 => z.1 0) q := by fun_prop
  have hV : ContDiffAt ℝ 2 (fun z : XV 1 => z.2 0) q := by fun_prop
  have hP := (Real.contDiffAt_rpow_const_of_ne (p := gamma.1) hx.ne').comp q hX
  have hK := (Real.contDiffAt_rpow_const_of_ne (p := (1 / 3 : ℝ)) hx.ne').comp q hX
  have hS := hV.neg.div hK (Real.rpow_pos_of_pos hx (1 / 3 : ℝ)).ne'
  exact hP.mul ((F_contDiff_two gamma Lam hLam).contDiffAt.comp q hS)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
