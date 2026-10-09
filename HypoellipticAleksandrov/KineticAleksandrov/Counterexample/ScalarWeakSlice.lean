module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

/-!
# One-dimensional integration by parts through a continuous join

Separate half-line boundary terms cancel at the joining point. A derivative at that point
is not assumed and is not needed for this weak identity.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Filter Set
open scoped Topology

/-- Integration by parts for a continuous join whose classical derivative exists off zero. -/
theorem scalar_integral_mul_deriv_off_zero (u up v vp : ℝ → ℝ)
    (hu : Continuous u) (hv : Continuous v)
    (hdu : ∀ x, x ≠ 0 → HasDerivAt u (up x) x)
    (hdv : ∀ x, HasDerivAt v (vp x) x)
    (hupv : Integrable (fun x => up x * v x))
    (huvp : Integrable (fun x => u x * vp x))
    (ht : Tendsto (fun x => u x * v x) atTop (𝓝 0))
    (hb : Tendsto (fun x => u x * v x) atBot (𝓝 0)) :
    (∫ x, u x * vp x) = -(∫ x, up x * v x) := by
  have hzero : Tendsto (u * v) (𝓝 0) (𝓝 (u 0 * v 0)) :=
    (hu.mul hv).tendsto 0
  have hp := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (fun x hx => hdu x hx.ne') (fun x _ => hdv x)
    (by simpa only [Pi.mul_def] using huvp.integrableOn)
    (by simpa only [Pi.mul_def] using hupv.integrableOn)
    (hzero.mono_left nhdsWithin_le_nhds) (by simpa only [Pi.mul_def] using ht)
  have hn := integral_Iic_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (fun x hx => hdu x hx.ne) (fun x _ => hdv x)
    (by simpa only [Pi.mul_def] using huvp.integrableOn)
    (by simpa only [Pi.mul_def] using hupv.integrableOn)
    (hzero.mono_left nhdsWithin_le_nhds) (by simpa only [Pi.mul_def] using hb)
  have hvp := integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic huvp
  have hup := integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hupv
  simp only [compl_Iic] at hvp hup
  linear_combination hp + hn - hvp - hup

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
