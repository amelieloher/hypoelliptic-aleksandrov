module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsBarrierGrowth
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsPhysicalGreen

/-! # The actual rectangular cutoff generator errors, without coefficient derivatives -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Set MeasureTheory

/-- Literal position, second velocity and cross velocity errors of the rectangular cutoff. -/
def barrierRectError (a : ℝ → ℝ → ℝ) (f : Z → ℝ) (Y R : ℝ) (z : Z) : ℝ :=
  z.2 * (deriv barrierCutoff ((z.1 - Y) / R ^ 3) / R ^ 3) *
    barrierCutoff (z.2 / R) * f z +
  a z.1 z.2 * barrierCutoff ((z.1 - Y) / R ^ 3) *
    (deriv (deriv barrierCutoff) (z.2 / R) / R ^ 2) * f z +
  2 * a z.1 z.2 * barrierCutoff ((z.1 - Y) / R ^ 3) *
    (deriv barrierCutoff (z.2 / R) / R) * deriv (fun v => f (z.1, v)) z.2

/-- Centering the position cutoff changes no derivative scale. -/
theorem barrier_position_cutoff_deriv (Y R x : ℝ) :
    deriv (fun X => barrierCutoff ((X - Y) / R ^ 3)) x =
      deriv barrierCutoff ((x - Y) / R ^ 3) / R ^ 3 := by
  have hc := (barrierCutoff_contDiff.differentiable (by simp) ((x - Y) / R ^ 3)).hasDerivAt
  have hx := ((hasDerivAt_id x).sub_const Y).div_const (R ^ 3)
  simpa only [one_div, div_eq_mul_inv, Function.comp_def, id_eq, one_mul] using (hc.comp x hx).deriv

/-- The literal error is exactly the generator product rule for a joint C² physical test. -/
theorem barrierRectError_eq_operator (a : ℝ → ℝ → ℝ) (f : Z → ℝ)
    (hf : ContDiff ℝ 2 f) (Y R : ℝ) (hR : 0 < R) (z : Z) :
    physicalSpatialOperator a (fun w => barrierRectCutoff Y R w * f w) z =
      barrierRectCutoff Y R z * physicalSpatialOperator a f z + barrierRectError a f Y R z := by
  let chi := fun X => barrierCutoff ((X - Y) / R ^ 3)
  let psi := scaledScalarCutoff barrierCutoff R
  let Phi := fun p : Point => f (p.position 0, p.velocity 0)
  let p : Point := ⟨0, fun _ => z.1, fun _ => z.2⟩
  have hc : ContDiff ℝ 2 barrierCutoff := barrierCutoff_contDiff.of_le (by simp)
  have hchi : ContDiff ℝ 2 chi := hc.comp ((contDiff_id.sub contDiff_const).div_const _)
  have hpsi : ContDiff ℝ 2 psi := scaledScalarCutoff_contDiff _ hc _
  have ht : DifferentiableAt ℝ (fun t => Phi ⟨t, p.position, p.velocity⟩) p.time := by
    change DifferentiableAt ℝ (fun _ : ℝ => f z) 0
    exact differentiableAt_const _
  have hx : DifferentiableAt ℝ (fun X => Phi ⟨p.time, fun _ => X, p.velocity⟩)
      (p.position 0) := by
    have hs : ContDiff ℝ 2 (fun X : ℝ => f (X, z.2)) :=
      hf.comp (contDiff_id.prodMk contDiff_const)
    exact hs.differentiable (by norm_num) z.1
  have hv : ContDiff ℝ 2 (fun v => Phi ⟨p.time, p.position, fun _ => v⟩) :=
    hf.comp (contDiff_const.prodMk contDiff_id)
  have hh := spatialCutoffTest_operator a chi psi hchi hpsi Phi p ht hx hv
  have he : spatialCutoffTest chi psi Phi =
      fun q : Point => (fun w => barrierRectCutoff Y R w * f w)
        (q.position 0, q.velocity 0) := rfl
  rw [he, ← physicalSpatialOperator_eq_forward a
    (fun w => barrierRectCutoff Y R w * f w) p] at hh
  change physicalSpatialOperator a (fun w => barrierRectCutoff Y R w * f w) z = _ at hh
  rw [← physicalSpatialOperator_eq_forward a f p, kineticVelocityGradient_scalar] at hh
  dsimp only [chi] at hh
  rw [barrier_position_cutoff_deriv, scaledScalarCutoff_second_deriv _ hc hR.ne',
    scaledScalarCutoff_deriv _ hc] at hh
  simpa only [psi, Phi, p, barrierRectCutoff, barrierRectError, scaledScalarCutoff, Prod.mk.eta,
    add_assoc] using hh

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
