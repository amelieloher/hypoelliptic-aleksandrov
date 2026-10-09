module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoffNativeJets

/-! # Differences of classical native selectors at second regularity points -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Filter

/-- First position selectors distribute over a differentiable difference. -/
theorem dx_sub_at {d : ℕ} (f g : XV d → ℝ) (q : XV d)
    (hf : DifferentiableAt ℝ f q) (hg : DifferentiableAt ℝ g q) :
    dx (fun y => f y - g y) q = dx f q - dx g q := by
  funext i
  unfold dx
  have he := hf.hasFDerivAt.sub hg.hasFDerivAt
  change HasFDerivAt (fun y => f y - g y) _ q at he
  rw [he.fderiv]
  rfl

/-- First velocity selectors distribute over a differentiable difference. -/
theorem dv_sub_at {d : ℕ} (f g : XV d → ℝ) (q : XV d)
    (hf : DifferentiableAt ℝ f q) (hg : DifferentiableAt ℝ g q) :
    dv (fun y => f y - g y) q = dv f q - dv g q := by
  funext i
  unfold dv
  have he := hf.hasFDerivAt.sub hg.hasFDerivAt
  change HasFDerivAt (fun y => f y - g y) _ q at he
  rw [he.fderiv]
  rfl

/-- Second velocity selectors distribute over a difference at a C2 point. -/
theorem dvv_sub_at {d : ℕ} (f g : XV d → ℝ) (q : XV d)
    (hf : ContDiffAt ℝ 2 f q) (hg : ContDiffAt ℝ 2 g q) :
    dvv (fun y => f y - g y) q = dvv f q - dvv g q := by
  funext i k
  have hloc : (fun y => dv (fun z => f z - g z) y k) =ᶠ[nhds q]
      (fun y => dv f y k - dv g y k) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hy hz
    rw [dv_sub_at f g y (hy.differentiableAt (by norm_num))
      (hz.differentiableAt (by norm_num))]
    rfl
  have hdf : DifferentiableAt ℝ (fun y => dv f y k) q :=
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiffAt_const).differentiableAt (by norm_num)
  have hdg : DifferentiableAt ℝ (fun y => dv g y k) q :=
    ((hg.fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiffAt_const).differentiableAt (by norm_num)
  unfold dvv
  have he := hdf.hasFDerivAt.sub hdg.hasFDerivAt
  change HasFDerivAt (fun y => dv f y k - dv g y k) _ q at he
  rw [hloc.fderiv_eq, he.fderiv]
  rfl

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
