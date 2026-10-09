module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsEstimates
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic

/-! # Anisotropic cutoff scales

A position cutoff uses radius R³ and a velocity cutoff radius R. Their actual
first and second derivatives provide the R⁻³, R⁻¹ and R⁻² Green error scales.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov.Parabolic

/-- Rescale a scalar cutoff by its physical radius. -/
def scaledScalarCutoff (chi : ℝ → ℝ) (R : ℝ) : ℝ → ℝ := fun s => chi (s/R)

/-- Scalar rescaling preserves C² regularity. -/
theorem scaledScalarCutoff_contDiff (chi : ℝ → ℝ) (hchi : ContDiff ℝ 2 chi)
    (R : ℝ) : ContDiff ℝ 2 (scaledScalarCutoff chi R) :=
  hchi.comp (contDiff_id.div_const R)

/-- The first derivative has the exact inverse-radius factor. -/
theorem scaledScalarCutoff_deriv (chi : ℝ → ℝ) (hchi : ContDiff ℝ 2 chi)
    (R s : ℝ) :
    deriv (scaledScalarCutoff chi R) s = deriv chi (s/R)/R := by
  have hc := (hchi.differentiable (by norm_num) (s/R)).hasDerivAt
  have hs := (hasDerivAt_id s).div_const R
  change deriv (chi ∘ (fun t => t/R)) s = _
  simpa only [id_eq, one_div, div_eq_mul_inv, one_mul] using (hc.comp s hs).deriv

/-- The second derivative has the exact inverse-square radius factor. -/
theorem scaledScalarCutoff_second_deriv (chi : ℝ → ℝ) (hchi : ContDiff ℝ 2 chi)
    {R : ℝ} (hR : R ≠ 0) (s : ℝ) :
    deriv (deriv (scaledScalarCutoff chi R)) s = deriv (deriv chi) (s/R)/R^2 := by
  have he : deriv (scaledScalarCutoff chi R) = fun t => deriv chi (t/R)/R := by
    funext t
    exact scaledScalarCutoff_deriv chi hchi R t
  rw [he]
  have hc := (hchi.differentiable_deriv_two (s/R)).hasDerivAt
  have hs := (hasDerivAt_id s).div_const R
  have hd : deriv (fun t => deriv chi (t/R)/R) s =
      (deriv (deriv chi) (s/R)*(1/R))/R := by
    simpa only [Function.comp_def, id_eq] using ((hc.comp s hs).div_const R).deriv
  rw [hd]
  field_simp

/-- Uniform first-derivative bounds acquire one inverse-radius factor. -/
theorem scaledScalarCutoff_deriv_bound (chi : ℝ → ℝ) (hchi : ContDiff ℝ 2 chi)
    {R : ℝ} (hR : 0 < R) (C : ℝ) (hC : ∀ s, |deriv chi s| ≤ C) (s : ℝ) :
    |deriv (scaledScalarCutoff chi R) s| ≤ C/R := by
  rw [scaledScalarCutoff_deriv chi hchi, abs_div, abs_of_pos hR]
  exact div_le_div_of_nonneg_right (hC _) hR.le

/-- Uniform second-derivative bounds acquire two inverse-radius factors. -/
theorem scaledScalarCutoff_second_deriv_bound (chi : ℝ → ℝ)
    (hchi : ContDiff ℝ 2 chi) {R : ℝ} (hR : 0 < R)
    (C : ℝ) (hC : ∀ s, |deriv (deriv chi) s| ≤ C) (s : ℝ) :
    |deriv (deriv (scaledScalarCutoff chi R)) s| ≤ C/R^2 := by
  rw [scaledScalarCutoff_second_deriv chi hchi hR.ne', abs_div,
    abs_of_pos (pow_pos hR 2)]
  exact div_le_div_of_nonneg_right (hC _) (pow_nonneg hR.le 2)

/-- Actual cutoff errors at the source's position and velocity scales. -/
theorem anisotropic_cutoff_error_le (a : ℝ → ℝ → ℝ) (chi psi : ℝ → ℝ)
    (hchi : ContDiff ℝ 2 chi) (hpsi : ContDiff ℝ 2 psi)
    (phi : Point → ℝ) (p : Point)
    (ht : DifferentiableAt ℝ (fun t => phi ⟨t, p.position, p.velocity⟩) p.time)
    (hx : DifferentiableAt ℝ (fun x => phi ⟨p.time, fun _ => x, p.velocity⟩)
      (p.position 0))
    (hv : ContDiff ℝ 2 (fun v => phi ⟨p.time, p.position, fun _ => v⟩))
    {R : ℝ} (hR : 0 < R) (Lam DX DV DVV B0 B1 : ℝ)
    (ha : 0 ≤ a (p.position 0) (p.velocity 0))
    (haL : a (p.position 0) (p.velocity 0) ≤ Lam)
    (hc : ∀ s, |chi s| ≤ 1) (hp : ∀ s, |psi s| ≤ 1)
    (hdx : ∀ s, |deriv chi s| ≤ DX) (hdv : ∀ s, |deriv psi s| ≤ DV)
    (hdvv : ∀ s, |deriv (deriv psi) s| ≤ DVV)
    (hb : |phi p| ≤ B0) (hbv : |kineticVelocityGradient phi p 0| ≤ B1) :
    |forwardScalarOperator a
        (spatialCutoffTest (scaledScalarCutoff chi (R^3)) (scaledScalarCutoff psi R) phi) p-
      scaledScalarCutoff chi (R^3) (p.position 0)*scaledScalarCutoff psi R (p.velocity 0)*
        forwardScalarOperator a phi p| ≤
      |p.velocity 0| * (DX/R^3)*B0+Lam*(DVV/R^2)*B0+2*Lam*(DV/R)*B1 := by
  exact spatialCutoffTest_error_le a _ _ (scaledScalarCutoff_contDiff chi hchi _)
    (scaledScalarCutoff_contDiff psi hpsi _) phi p ht hx hv Lam (DX/R^3) (DV/R)
    (DVV/R^2) B0 B1 ha haL (hc _) (hp _)
    (scaledScalarCutoff_deriv_bound chi hchi (pow_pos hR 3) DX hdx _)
    (scaledScalarCutoff_deriv_bound psi hpsi hR DV hdv _)
    (scaledScalarCutoff_second_deriv_bound psi hpsi hR DVV hdvv _) hb hbv

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
