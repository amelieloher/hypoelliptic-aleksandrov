module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftRegularity
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic

/-! # The literal spatial derivative of the radial lift integrand -/

@[expose] public section
noncomputable section
open Set Filter Topology
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The joint derivative in a spatial direction has the literal dilation chain factor. -/
theorem bellmanLiftIntegrand_spatial_fderiv (alpha : ℝ) (zeta : (ℝ × ℝ) → ℝ)
    (hz : ContDiff ℝ 1 zeta) (q : ℝ × ℝ) (r : ℝ) (hr : 0 < r) (e : ℝ × ℝ) :
    fderiv ℝ (bellmanLiftIntegrand alpha zeta) (q, r) (e, 0) =
      r ^ (-1 - alpha) * fderiv ℝ zeta (bellmanPlaneDilation r q)
        (bellmanDilationLinear r e) := by
  have hf := bellmanLiftIntegrand_contDiffOn_order 1 alpha zeta hz
  have hd : DifferentiableAt ℝ (bellmanLiftIntegrand alpha zeta) (q, r) :=
    ((hf (q, r) ⟨trivial, hr⟩).contDiffAt
      ((isOpen_univ.prod isOpen_Ioi).mem_nhds ⟨trivial, hr⟩)).differentiableAt (by norm_num)
  let L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) × ℝ :=
    (ContinuousLinearMap.id ℝ (ℝ × ℝ)).prod 0
  have hpair : HasFDerivAt (fun x : ℝ × ℝ => (x, r)) L q :=
    (hasFDerivAt_id q).prodMk (hasFDerivAt_const r q)
  have hcomp := hd.hasFDerivAt.comp q hpair
  have hslice := (((hz.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt).comp q
    (bellmanDilationLinear r).hasFDerivAt).const_mul (r ^ (-1 - alpha))
  change HasFDerivAt (fun x => bellmanLiftIntegrand alpha zeta (x, r)) _ q at hslice
  have he := congrArg (fun D : (ℝ × ℝ) →L[ℝ] ℝ => D e) (hcomp.unique hslice)
  simpa only [ContinuousLinearMap.comp_apply, L, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, zero_apply, smul_apply, smul_eq_mul,
    bellmanDilationLinear_apply]
    using he

end HypoellipticAleksandrov.KineticAleksandrov
