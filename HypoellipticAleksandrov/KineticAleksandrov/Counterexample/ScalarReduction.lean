module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarPieces
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.Basis
import Mathlib.Tactic

/-!
# The signed cubic reduction

Direct real differentiation of the cubic substitution. The second basis function is
`s * M(...)`, so no fractional power of a negative argument is introduced.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter Set
open scoped Topology ContDiff

/-- The source cubic change of independent variable. -/
def scalarCubic (a s : ℝ) : ℝ := s ^ 3 / (9 * a)

/-- Its exact derivative. -/
theorem hasDerivAt_scalarCubic (a s : ℝ) :
    HasDerivAt (scalarCubic a) (s ^ 2 / (3 * a)) s := by
  change HasDerivAt (fun t : ℝ => t ^ 3 / (9 * a)) _ s
  convert ((hasDerivAt_id s).pow 3).div_const (9 * a) using 1 <;> norm_num
  ring

/-- First derivative of the pulled-back function. -/
theorem deriv_comp_scalarCubic (f : ℝ → ℝ) (a s : ℝ)
    (hf : DifferentiableAt ℝ f (scalarCubic a s)) :
    deriv (fun t => f (scalarCubic a t)) s = deriv f (scalarCubic a s) *
      (s ^ 2 / (3 * a)) :=
  (hf.hasDerivAt.comp s (hasDerivAt_scalarCubic a s)).deriv

/-- Second derivative of the pulled-back function at a twice differentiable point. -/
theorem deriv2_comp_scalarCubic (f : ℝ → ℝ) (a s : ℝ)
    (hf : ContDiffAt ℝ 2 f (scalarCubic a s)) :
    deriv (deriv (fun t => f (scalarCubic a t))) s =
      deriv (deriv f) (scalarCubic a s) * (s ^ 2 / (3 * a)) ^ 2 +
        deriv f (scalarCubic a s) * (2 * s / (3 * a)) := by
  have hc : Continuous (scalarCubic a) := by unfold scalarCubic; fun_prop
  have hdf := hf.differentiableAt (by norm_num)
  have hdf' := (hf.derivWithin (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).differentiableAt
    (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have he : deriv (fun t => f (scalarCubic a t)) =ᶠ[𝓝 s]
      fun t => deriv f (scalarCubic a t) * (t ^ 2 / (3 * a)) := by
    have he' := hf.eventually (by norm_num : (2 : ℕ∞ω) ≠ ∞)
    filter_upwards [hc.continuousAt.tendsto.eventually he'] with t ht
    exact deriv_comp_scalarCubic f a t (ht.differentiableAt (by norm_num))
  have h1 := hdf'.hasDerivAt.comp s (hasDerivAt_scalarCubic a s)
  have h2 : HasDerivAt (fun t : ℝ => t ^ 2 / (3 * a)) (2 * s / (3 * a)) s := by
    convert ((hasDerivAt_id s).pow 2).div_const (3 * a) using 1 <;> simp
  exact ((h1.mul h2).congr_of_eventuallyEq he).deriv.trans (by dsimp only [Function.comp_def]; ring)

/-- Kummer's first solution reduces to the source signed scalar equation. -/
theorem scalarCubic_ode (f : ℝ → ℝ) (gamma a s : ℝ) (ha : a ≠ 0)
    (hf : ContDiffAt ℝ 2 f (scalarCubic a s))
    (hode : scalarCubic a s * deriv (deriv f) (scalarCubic a s) +
      (2 / 3 - scalarCubic a s) * deriv f (scalarCubic a s) +
        gamma * f (scalarCubic a s) = 0) :
    a * deriv (deriv (fun t => f (scalarCubic a t))) s -
      s ^ 2 / 3 * deriv (fun t => f (scalarCubic a t)) s +
        gamma * s * f (scalarCubic a s) = 0 := by
  rw [deriv2_comp_scalarCubic f a s hf,
    deriv_comp_scalarCubic f a s (hf.differentiableAt (by norm_num))]
  dsimp only [scalarCubic] at hode ⊢
  field_simp at hode ⊢
  linear_combination (s / 3) * hode

/-- The signed second solution satisfies the same scalar equation. -/
theorem scalarCubic_second_ode (f : ℝ → ℝ) (gamma a s : ℝ) (ha : a ≠ 0)
    (hf : ContDiff ℝ 2 f)
    (hode : scalarCubic a s * deriv (deriv f) (scalarCubic a s) +
      (4 / 3 - scalarCubic a s) * deriv f (scalarCubic a s) -
        (1 / 3 - gamma) * f (scalarCubic a s) = 0) :
    a * deriv (deriv (fun t => t * f (scalarCubic a t))) s -
      s ^ 2 / 3 * deriv (fun t => t * f (scalarCubic a t)) s +
        gamma * s * (s * f (scalarCubic a s)) = 0 := by
  have hd (t : ℝ) := (hf.contDiffAt (x := scalarCubic a t)).differentiableAt
    (by norm_num : (2 : ℕ∞ω) ≠ 0)
  have hd' := hf.differentiable_deriv_two
  have hfirst (t : ℝ) : HasDerivAt (fun w => w * f (scalarCubic a w))
      (f (scalarCubic a t) + t *
        (deriv f (scalarCubic a t) * (t ^ 2 / (3 * a)))) t := by
    simpa only [one_mul, Function.comp_def, Pi.mul_def, id_eq] using
      (hasDerivAt_id t).mul ((hd t).hasDerivAt.comp t (hasDerivAt_scalarCubic a t))
  have hfirsteq : deriv (fun w => w * f (scalarCubic a w)) =
      fun t => f (scalarCubic a t) + t *
        (deriv f (scalarCubic a t) * (t ^ 2 / (3 * a))) := funext (fun t => (hfirst t).deriv)
  have hc2 : HasDerivAt (fun t : ℝ => t ^ 2 / (3 * a)) (2 * s / (3 * a)) s := by
    convert ((hasDerivAt_id s).pow 2).div_const (3 * a) using 1 <;> simp
  have hsecond := ((hd s).hasDerivAt.comp s (hasDerivAt_scalarCubic a s)).add
    ((hasDerivAt_id s).mul
      (((hd' _).hasDerivAt.comp s (hasDerivAt_scalarCubic a s)).mul hc2))
  simp only [Function.comp_def, Pi.add_def, Pi.mul_def, id_eq] at hsecond
  rw [hfirsteq, hsecond.deriv]
  dsimp only [scalarCubic] at hode ⊢
  field_simp at hode ⊢
  linear_combination (s ^ 2 / 3) * hode

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
