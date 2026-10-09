module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Flow.Mass
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Flow.Heat
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Flow.Integrability

/-!
# The auxiliary Gaussian flow: summary

Facade for the definition and properties of the Gaussian flow:

* (i) `flowKernel_pos`, `flowKernel_contDiff`, `flowKernel_differentiableAt_param`,
  `integral_flowKernel`, `flowKernel_le`;
* (ii) `hasDerivAt_flowKernel`;
* (iii) `transportDerivative_flowKernel`;
* (iv) `flowKernel_iterPartial_bound` (all orders, uniform for `h ≥ a`), with the order one and
  two corollaries below, `integrable_pow_mul_flowKernel`, `integrable_norm_pow_mul_flowKernel`,
  `integrable_sq_div_dirPartial_flowKernel`, `integrable_gradient_sq_div_flowKernel`,
  `integrable_norm_velocity_mul_positionPartial` and
  `integrable_norm_velocity_mul_dirPartial_dirPartial`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

/-- The Gaussian flow estimates: differentiability of `Φ_h(y)` in the scale parameter `h > 0`. -/
theorem flowKernel_differentiableAt_param {lam h : ℝ} (hl : 0 < lam) (hh : 0 < h)
    (y : EvolutionAmbientState d) :
    DifferentiableAt ℝ (fun h' => flowKernel lam h' y) h :=
  (hasDerivAt_flowKernel hl hh y).differentiableAt

/-- The Gaussian flow estimates, order one in velocity coordinates. -/
theorem flowKernel_velocityPartial_bound {lam a : ℝ} (hl : 0 < lam) (ha : 0 < a) (i : Fin d) :
    ∃ C : ℝ, ∀ h : ℝ, a ≤ h → ∀ y : EvolutionAmbientState d,
      |velocityPartial i (flowKernel lam h) y| ≤ C * (1 + ‖y‖) * flowKernel lam h y := by
  obtain ⟨C, hC⟩ := flowKernel_iterPartial_bound (d := d) hl ha [Sum.inl i]
  refine ⟨C, fun h hah y => ?_⟩
  have := hC h hah y
  simp only [iterPartial, List.length_singleton, pow_one] at this
  exact this

/-- The Gaussian flow estimates, order one in position coordinates. -/
theorem flowKernel_positionPartial_bound {lam a : ℝ} (hl : 0 < lam) (ha : 0 < a) (i : Fin d) :
    ∃ C : ℝ, ∀ h : ℝ, a ≤ h → ∀ y : EvolutionAmbientState d,
      |positionPartial i (flowKernel lam h) y| ≤ C * (1 + ‖y‖) * flowKernel lam h y := by
  obtain ⟨C, hC⟩ := flowKernel_iterPartial_bound (d := d) hl ha [Sum.inr i]
  refine ⟨C, fun h hah y => ?_⟩
  have := hC h hah y
  simp only [iterPartial, List.length_singleton, pow_one] at this
  exact this

/-- The Gaussian flow estimates, order two, for any pair of coordinate directions. -/
theorem flowKernel_dirPartial_dirPartial_bound {lam a : ℝ} (hl : 0 < lam) (ha : 0 < a)
    (δ δ' : Fin d ⊕ Fin d) :
    ∃ C : ℝ, ∀ h : ℝ, a ≤ h → ∀ y : EvolutionAmbientState d,
      |dirPartial δ' (dirPartial δ (flowKernel lam h)) y| ≤
        C * (1 + ‖y‖) ^ 2 * flowKernel lam h y := by
  obtain ⟨C, hC⟩ := flowKernel_iterPartial_bound (d := d) hl ha [δ', δ]
  exact ⟨C, fun h hah y => by simpa [iterPartial] using hC h hah y⟩

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
