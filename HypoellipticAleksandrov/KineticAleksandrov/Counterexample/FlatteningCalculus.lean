module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningProfile
public import Mathlib.Analysis.Calculus.FDeriv.Congr

/-! # The second classical chain rule for the literal flattening -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter

/-- At a C2 point the flattened velocity Hessian has the literal rank-one correction. -/
theorem dvv_flatProfile_of_contDiffAt {d : ℕ} (H : XV d → ℝ) (alpha r : ℝ)
    (hr : 0 < r) (q : XV d) (hH : ContDiffAt ℝ 2 H q) (i k : Fin d) :
    dvv (flatProfile H flatteningPsi flatteningOffset alpha r) q i k =
      -deriv flatteningPsi (H q / Real.rpow r alpha) * dvv H q i k -
        Real.rpow r (-alpha) * deriv (deriv flatteningPsi) (H q / Real.rpow r alpha) *
          dv H q i * dv H q k := by
  let a := Real.rpow r alpha
  have hin : HasFDerivAt (fun z => H z / a) (a⁻¹ • fderiv ℝ H q) q := by
    simpa only [div_eq_mul_inv, mul_comm] using
      (hH.differentiableAt (by norm_num)).hasFDerivAt.const_mul a⁻¹
  have hpsi : DifferentiableAt ℝ (deriv flatteningPsi) (H q / a) :=
    by
      rw [funext deriv_flatteningPsi]
      exact (contDiff_flatteningSlope.differentiable (by simp)).differentiableAt
  have hout := hpsi.hasDerivAt.comp_hasFDerivAt q hin
  have hv : DifferentiableAt ℝ (fun z => dv H z k) q :=
    ((hH.fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiffAt_const).differentiableAt (by norm_num)
  have he := hout.neg.mul hv.hasFDerivAt
  change HasFDerivAt (fun z => -deriv flatteningPsi (H z / a) * dv H z k) _ q at he
  have hnear := hH.eventually (by norm_num)
  have hloc : (fun z => dv (flatProfile H flatteningPsi flatteningOffset alpha r) z k) =ᶠ[nhds q]
      (fun z => -deriv flatteningPsi (H z / a) * dv H z k) := by
    filter_upwards [hnear] with z hz
    unfold dv
    rw [fderiv_flatProfile H alpha r hr z (hz.differentiableAt (by norm_num))]
    rfl
  unfold dvv
  rw [hloc.fderiv_eq, he.fderiv]
  simp only [add_apply, smul_apply, neg_apply, smul_eq_mul]
  change -deriv flatteningPsi (H q / a) * dvv H q i k +
    dv H q k * -(deriv (deriv flatteningPsi) (H q / a) * (a⁻¹ * dv H q i)) = _
  have ha : a⁻¹ = Real.rpow r (-alpha) := by
    dsimp [a]
    rw [Real.rpow_neg hr.le]
  rw [ha]
  dsimp only [a, dvv]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
