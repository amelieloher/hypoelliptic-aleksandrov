module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.IntegrationByParts
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Algebra.FlowIdentities

/-!
# The integral of the flow operator over phase space

The time-integrated identities: the terms `N : D²(·)` with `N = M^h` integrate
to zero in `y`, because `r^q` and `r^q |β|²` are `W^{2,1}` in `y` (the smoothing estimates). Here
`flowL` is
the operator of `Algebra.FlowOperator`; it equals `heatOperator` of the smoothing package.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

theorem flowL_eq_heatOperator (lam h : ℝ) (F : EvolutionAmbientState d → ℝ) :
    flowL lam h F = heatOperator lam h F := rfl

theorem SmoothW21.integrable_flowL {g : EvolutionAmbientState d → ℝ} (hg : SmoothW21 g)
    (lam h : ℝ) : Integrable (flowL lam h g) := by
  have h1 : Integrable (fun y => ∑ i, coordPartial (Sum.inr i) (coordPartial (Sum.inr i) g) y) :=
    integrable_finsetSum _ fun i _ => hg.2.2.2 (Sum.inr i) (Sum.inr i)
  have h2 : Integrable (fun y => ∑ i, coordPartial (Sum.inr i) (coordPartial (Sum.inl i) g) y) :=
    integrable_finsetSum _ fun i _ => hg.2.2.2 (Sum.inl i) (Sum.inr i)
  have h3 : Integrable (fun y => ∑ i, coordPartial (Sum.inl i) (coordPartial (Sum.inl i) g) y) :=
    integrable_finsetSum _ fun i _ => hg.2.2.2 (Sum.inl i) (Sum.inl i)
  have hs : Integrable (fun y => 2 * h ^ 2 * ∑ i, coordPartial (Sum.inr i)
      (coordPartial (Sum.inr i) g) y - 2 * h * ∑ i, coordPartial (Sum.inr i)
      (coordPartial (Sum.inl i) g) y + ∑ i, coordPartial (Sum.inl i)
      (coordPartial (Sum.inl i) g) y) := ((h1.const_mul _).sub (h2.const_mul _)).add h3
  exact hs.const_mul (lam / 2)

theorem SmoothW21.integral_flowL {g : EvolutionAmbientState d → ℝ} (hg : SmoothW21 g)
    (lam h : ℝ) : ∫ y, flowL lam h g y = 0 := by
  have h1 : Integrable (fun y => ∑ i, coordPartial (Sum.inr i) (coordPartial (Sum.inr i) g) y) :=
    integrable_finsetSum _ fun i _ => hg.2.2.2 (Sum.inr i) (Sum.inr i)
  have h2 : Integrable (fun y => ∑ i, coordPartial (Sum.inr i) (coordPartial (Sum.inl i) g) y) :=
    integrable_finsetSum _ fun i _ => hg.2.2.2 (Sum.inl i) (Sum.inr i)
  have h3 : Integrable (fun y => ∑ i, coordPartial (Sum.inl i) (coordPartial (Sum.inl i) g) y) :=
    integrable_finsetSum _ fun i _ => hg.2.2.2 (Sum.inl i) (Sum.inl i)
  have e1 : ∫ y, ∑ i, coordPartial (Sum.inr i) (coordPartial (Sum.inr i) g) y = 0 := by
    rw [integral_finsetSum _ fun i _ => hg.2.2.2 (Sum.inr i) (Sum.inr i)]
    exact Finset.sum_eq_zero fun i _ => hg.integral_coordPartial₂ (Sum.inr i) (Sum.inr i)
  have e2 : ∫ y, ∑ i, coordPartial (Sum.inr i) (coordPartial (Sum.inl i) g) y = 0 := by
    rw [integral_finsetSum _ fun i _ => hg.2.2.2 (Sum.inl i) (Sum.inr i)]
    exact Finset.sum_eq_zero fun i _ => hg.integral_coordPartial₂ (Sum.inl i) (Sum.inr i)
  have e3 : ∫ y, ∑ i, coordPartial (Sum.inl i) (coordPartial (Sum.inl i) g) y = 0 := by
    rw [integral_finsetSum _ fun i _ => hg.2.2.2 (Sum.inl i) (Sum.inl i)]
    exact Finset.sum_eq_zero fun i _ => hg.integral_coordPartial₂ (Sum.inl i) (Sum.inl i)
  have hs : Integrable (fun y => 2 * h ^ 2 * ∑ i, coordPartial (Sum.inr i)
      (coordPartial (Sum.inr i) g) y - 2 * h * ∑ i, coordPartial (Sum.inr i)
      (coordPartial (Sum.inl i) g) y) := (h1.const_mul _).sub (h2.const_mul _)
  have key : flowL lam h g = fun y => lam / 2 * (2 * h ^ 2 * ∑ i, coordPartial (Sum.inr i)
      (coordPartial (Sum.inr i) g) y - 2 * h * ∑ i, coordPartial (Sum.inr i)
      (coordPartial (Sum.inl i) g) y + ∑ i, coordPartial (Sum.inl i)
      (coordPartial (Sum.inl i) g) y) := rfl
  rw [key, integral_const_mul, integral_add hs h3, integral_sub (h1.const_mul _) (h2.const_mul _),
    integral_const_mul, integral_const_mul, e1, e2, e3]
  simp

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
