module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarEquations
public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Abel's identity for the scalar equation

The nonsingular real s equation has a nonvanishing Wronskian whenever its value at
zero is nonzero. This avoids initial-value arguments at Kummer's singular z point.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- The ordinary scalar Wronskian, with the source solution first. -/
def scalarWronskian (f g : ℝ → ℝ) (s : ℝ) : ℝ := f s * deriv g s - deriv f s * g s

/-- The Wronskian of two solutions satisfies Abel's differential equation. -/
theorem scalarWronskian_hasDerivAt (f g : ℝ → ℝ) (gamma s : ℝ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfo : deriv (deriv f) s - s ^ 2 / 3 * deriv f s + gamma * s * f s = 0)
    (hgo : deriv (deriv g) s - s ^ 2 / 3 * deriv g s + gamma * s * g s = 0) :
    HasDerivAt (scalarWronskian f g) (s ^ 2 / 3 * scalarWronskian f g s) s := by
  have hdf := (hf.differentiable (by norm_num) s).hasDerivAt
  have hdg := (hg.differentiable (by norm_num) s).hasDerivAt
  have hdf' := (hf.differentiable_deriv_two s).hasDerivAt
  have hdg' := (hg.differentiable_deriv_two s).hasDerivAt
  have hd := (hdf.mul hdg').sub (hdf'.mul hdg)
  simp only [Pi.sub_def, Pi.mul_def] at hd
  unfold scalarWronskian
  convert hd using 1
  linear_combination g s * hfo - f s * hgo

/-- The scalar Wronskian has exactly the exponential source normalization. -/
theorem scalarWronskian_identity (f g : ℝ → ℝ) (gamma : ℝ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfo : ∀ s, deriv (deriv f) s - s ^ 2 / 3 * deriv f s + gamma * s * f s = 0)
    (hgo : ∀ s, deriv (deriv g) s - s ^ 2 / 3 * deriv g s + gamma * s * g s = 0)
    (s : ℝ) : scalarWronskian f g s * Real.exp (-(s ^ 3 / 9)) =
      scalarWronskian f g 0 := by
  let w : ℝ → ℝ := fun t => scalarWronskian f g t * Real.exp (-(t ^ 3 / 9))
  have hd (t : ℝ) : HasDerivAt w 0 t := by
    have hpoly : HasDerivAt (fun t : ℝ => -(t ^ 3 / 9)) (-(t ^ 2 / 3)) t := by
      have hp := (((hasDerivAt_id t).pow 3).div_const 9).neg
      simp only [Pi.neg_def, id_eq] at hp
      convert hp using 1
      norm_num
      ring
    have he := hpoly.exp
    have hw := (scalarWronskian_hasDerivAt f g gamma t hf hg (hfo t) (hgo t)).mul he
    simp only [Pi.mul_def] at hw
    change HasDerivAt (fun t => scalarWronskian f g t * Real.exp (-(t ^ 3 / 9))) 0 t
    convert hw using 1
    ring
  have hc := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) s 0
  simpa only [w, zero_pow (by decide : 3 ≠ 0), zero_div, neg_zero, Real.exp_zero,
    mul_one] using hc

/-- The signed second M solution of the s equation. -/
def scalarSecondM (gamma : ScalarGamma) (s : ℝ) : ℝ :=
  s * Kummer.M (1 / 3 - gamma.1) Kummer.b43 (scalarCubic 1 s)

/-- The signed second solution is smooth on the full real s carrier. -/
theorem contDiff_scalarSecondM (gamma : ScalarGamma) :
    ContDiff ℝ 2 (scalarSecondM gamma) :=
  contDiff_id.mul ((Kummer.analyticOnNhd_M _ _).contDiff.comp
    ((contDiff_scalarCubic 1).of_le (by norm_num)))

/-- The signed second solution obeys the exact nonsingular s equation. -/
theorem scalarSecondM_ode (gamma : ScalarGamma) (s : ℝ) :
    deriv (deriv (scalarSecondM gamma)) s - s ^ 2 / 3 * deriv (scalarSecondM gamma) s +
      gamma.1 * s * scalarSecondM gamma s = 0 := by
  have h := scalarCubic_second_ode (Kummer.M (1 / 3 - gamma.1) Kummer.b43) gamma.1 1 s
    one_ne_zero (Kummer.analyticOnNhd_M _ _).contDiff
    (by simpa only [Kummer.b43] using
      Kummer.M_ode (1 / 3 - gamma.1) Kummer.b43 (scalarCubic 1 s))
  unfold scalarSecondM
  simpa only [one_mul] using h

/-- The second solution is normalized by a unit derivative at zero. -/
theorem scalarSecondM_zero_jets (gamma : ScalarGamma) :
    scalarSecondM gamma 0 = 0 ∧ deriv (scalarSecondM gamma) 0 = 1 := by
  have hc : scalarCubic 1 0 = 0 := by simp [scalarCubic]
  have hm := (Kummer.hasDerivAt_M (1 / 3 - gamma.1) Kummer.b43 (scalarCubic 1 0)).comp
    0 (hasDerivAt_scalarCubic 1 0)
  have hd := (hasDerivAt_id (0 : ℝ)).mul hm
  simp only [Pi.mul_def, Function.comp_def, id_eq, hc, Kummer.M_zero,
    one_mul, zero_mul, add_zero] at hd
  unfold scalarSecondM
  exact ⟨by simp, hd.deriv⟩

/-- The actual negative scalar piece never has a simultaneous zero value and derivative. -/
theorem Fminus_no_zero_jet (gamma : ScalarGamma) (Lam s : ℝ) :
    ¬ (Fminus gamma Lam s = 0 ∧ deriv (Fminus gamma Lam) s = 0) := by
  intro hz
  have hw := scalarWronskian_identity (Fminus gamma Lam) (scalarSecondM gamma) gamma.1
    ((contDiff_Fminus gamma Lam).of_le (by norm_num)) (contDiff_scalarSecondM gamma)
    (Fminus_ode gamma Lam) (scalarSecondM_ode gamma) s
  simp only [scalarWronskian, hz.1, hz.2, zero_mul, sub_self, Fminus_zero,
    (scalarSecondM_zero_jets gamma).1, (scalarSecondM_zero_jets gamma).2,
    mul_zero, mul_one, sub_zero] at hw
  exact (gamma_constants_pos gamma.1 gamma.2.1 gamma.2.2).1.ne' hw.symm

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
