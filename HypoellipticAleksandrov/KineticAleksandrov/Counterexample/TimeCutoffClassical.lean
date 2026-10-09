module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoff
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningSourceProfile
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-! # Classical cutoff calculus at the almost everywhere regular profile points -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Filter MeasureTheory

/-- The ordinary first differential of the fixed scalar cutoff. -/
theorem fderiv_timeCutoffTheta_comp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → ℝ) (q : E) (hf : DifferentiableAt ℝ f q) :
    fderiv ℝ (fun y => timeCutoffTheta (f y)) q =
      deriv timeCutoffTheta (f q) • fderiv ℝ f q := by
  have ht : DifferentiableAt ℝ timeCutoffTheta (f q) :=
    (contDiff_timeCutoffTheta.differentiable (by simp)).differentiableAt
  exact (ht.hasDerivAt.comp_hasFDerivAt q hf.hasFDerivAt).fderiv

/-- The second velocity chain rule retains the exact positive rank-one term. -/
theorem dvv_timeCutoffTheta_comp {d : ℕ} (f : XV d → ℝ) (q : XV d)
    (hf : ContDiffAt ℝ 2 f q) (i k : Fin d) :
    dvv (fun y => timeCutoffTheta (f y)) q i k =
      deriv timeCutoffTheta (f q) * dvv f q i k +
        deriv (deriv timeCutoffTheta) (f q) * dv f q i * dv f q k := by
  have htheta2 : ContDiff ℝ 2 timeCutoffTheta := contDiff_timeCutoffTheta.of_le (by simp)
  have hd : DifferentiableAt ℝ (deriv timeCutoffTheta) (f q) :=
    htheta2.differentiable_deriv_two.differentiableAt
  have hout := hd.hasDerivAt.comp_hasFDerivAt q
    (hf.differentiableAt (by norm_num)).hasFDerivAt
  have hv : DifferentiableAt ℝ (fun z => dv f z k) q :=
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiffAt_const).differentiableAt (by norm_num)
  have he := hout.mul hv.hasFDerivAt
  change HasFDerivAt (fun z => deriv timeCutoffTheta (f z) * dv f z k) _ q at he
  have hloc : (fun z => dv (fun y => timeCutoffTheta (f y)) z k) =ᶠ[nhds q]
      (fun z => deriv timeCutoffTheta (f z) * dv f z k) := by
    filter_upwards [hf.eventually (by norm_num)] with z hz
    unfold dv
    rw [fderiv_timeCutoffTheta_comp f z (hz.differentiableAt (by norm_num))]
    rfl
  unfold dvv
  rw [hloc.fderiv_eq, he.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  change deriv timeCutoffTheta (f q) * dvv f q i k +
    dv f q k * (deriv (deriv timeCutoffTheta) (f q) * dv f q i) = _
  simp only [dv, dvv]
  ring

/-- The selected flattened profile has genuine second regularity almost everywhere. -/
theorem selectedFlatProfile_contDiffAt_ae {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) :
    ∀ᵐ q ∂volume, ContDiffAt ℝ 2 (selectedFlatProfile h r) q := by
  have hC2 := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  filter_upwards [hC2] with q hq
  unfold selectedFlatProfile flatProfile
  exact contDiffAt_const.sub (contDiffAt_const.mul
    ((contDiff_flatteningPsi.of_le (by simp)).contDiffAt.comp q (hq.div_const _)))

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
