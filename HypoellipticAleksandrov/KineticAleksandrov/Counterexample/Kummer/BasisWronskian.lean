module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.BasisM
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Abel's identity on the positive axis

The weighted Wronskian of two classical Kummer solutions is constant.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

open Set

/-- Wronskian with the Abel integrating factor for Kummer's equation. -/
def weightedWronskian (b : ℝ) (f g : ℝ → ℝ) (z : ℝ) : ℝ :=
  Real.exp (-z) * z ^ b * (deriv f z * g z - f z * deriv g z)

/-- The weighted Wronskian has zero derivative for two classical solutions. -/
theorem hasDerivAt_weightedWronskian (a b : ℝ) (f g : ℝ → ℝ)
    (z : ℝ) (hz : 0 < z) (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) (hf' : DifferentiableAt ℝ (deriv f) z)
    (hg' : DifferentiableAt ℝ (deriv g) z)
    (heqf : z * deriv (deriv f) z + (b - z) * deriv f z - a * f z = 0)
    (heqg : z * deriv (deriv g) z + (b - z) * deriv g z - a * g z = 0) :
    HasDerivAt (weightedWronskian b f g) 0 z := by
  have hd := (((hasDerivAt_id z).neg.exp.mul
    ((hasDerivAt_id z).rpow_const (p := b) (Or.inl hz.ne'))).mul
    ((hf'.hasDerivAt.mul hg.hasDerivAt).sub (hf.hasDerivAt.mul hg'.hasDerivAt)))
  convert hd using 1
  · rfl
  · dsimp only [id_eq, Pi.mul_apply, Pi.sub_apply, Pi.neg_apply]
    have hp : z ^ b = z * z ^ (b - 1) := by
      conv_rhs => lhs; rw [← Real.rpow_one z]
      rw [← Real.rpow_add hz]
      congr 1
      ring
    rw [hp]
    linear_combination -(Real.exp (-z) * z ^ (b - 1) * g z) * heqf +
      (Real.exp (-z) * z ^ (b - 1) * f z) * heqg

/-- Abel's weighted Wronskian is constant on the positive axis. -/
theorem weightedWronskian_eq (a b : ℝ) (f g : ℝ → ℝ)
    (hf : DifferentiableOn ℝ f (Ioi 0)) (hg : DifferentiableOn ℝ g (Ioi 0))
    (hf' : DifferentiableOn ℝ (deriv f) (Ioi 0))
    (hg' : DifferentiableOn ℝ (deriv g) (Ioi 0))
    (heqf : ∀ z > 0, z * deriv (deriv f) z + (b - z) * deriv f z - a * f z = 0)
    (heqg : ∀ z > 0, z * deriv (deriv g) z + (b - z) * deriv g z - a * g z = 0)
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    weightedWronskian b f g x = weightedWronskian b f g y := by
  have hd (z : ℝ) (hz : z ∈ Ioi (0 : ℝ)) := hasDerivAt_weightedWronskian a b f g z hz
    (hf.differentiableAt (isOpen_Ioi.mem_nhds hz))
    (hg.differentiableAt (isOpen_Ioi.mem_nhds hz))
    (hf'.differentiableAt (isOpen_Ioi.mem_nhds hz))
    (hg'.differentiableAt (isOpen_Ioi.mem_nhds hz)) (heqf z hz) (heqg z hz)
  exact isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi (0 : ℝ)).isPreconnected
    (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd z hz).deriv) hx hy

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
