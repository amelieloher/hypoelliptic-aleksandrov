module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# The differential inequality behind the absorption

The absorption estimate: if `-E' ≤ 4 a h^{-θ} - κ F'` on `[ε, S]`, then
`E(ε) - κ F(ε) ≤ E(S) - κ F(S) + (4a/(1-θ)) (S^{1-θ} - ε^{1-θ})`. This is the integration in
the smoothing time `h`, phrased as monotonicity of an auxiliary function.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

theorem absorb_core {E Fx E' F' : ℝ → ℝ} {a θ κ ε S : ℝ} (hε : 0 < ε) (hεS : ε ≤ S)
    (hθ : θ < 1)
    (hE : ∀ h ∈ Set.Icc ε S, HasDerivAt E (E' h) h)
    (hF : ∀ h ∈ Set.Icc ε S, HasDerivAt Fx (F' h) h)
    (hineq : ∀ h ∈ Set.Icc ε S, -E' h ≤ 4 * a * h ^ (-θ) - κ * F' h) :
    E ε - κ * Fx ε ≤ E S - κ * Fx S + 4 * a / (1 - θ) * (S ^ (1 - θ) - ε ^ (1 - θ)) := by
  have hθ1 : 1 - θ ≠ 0 := (by linarith : (0 : ℝ) < 1 - θ).ne'
  have hder : ∀ h ∈ Set.Icc ε S, HasDerivAt
      (fun h => E h - κ * Fx h + 4 * a / (1 - θ) * h ^ (1 - θ))
      (E' h - κ * F' h + 4 * a / (1 - θ) * ((1 - θ) * h ^ (1 - θ - 1))) h := by
    intro h hh
    have hh0 : 0 < h := lt_of_lt_of_le hε hh.1
    have := (Real.hasDerivAt_rpow_const (p := 1 - θ) (Or.inl hh0.ne')).const_mul (4 * a / (1 - θ))
    exact ((hE h hh).sub ((hF h hh).const_mul κ)).add this
  have hmono : MonotoneOn (fun h => E h - κ * Fx h + 4 * a / (1 - θ) * h ^ (1 - θ))
      (Set.Icc ε S) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc ε S)
      (fun h hh => (hder h hh).continuousAt.continuousWithinAt)
      (fun h hh => (hder h (interior_subset hh)).differentiableAt.differentiableWithinAt)
      (fun h hh => ?_)
    rw [interior_Icc] at hh
    have hh' : h ∈ Set.Icc ε S := Set.Ioo_subset_Icc_self hh
    rw [(hder h hh').deriv]
    have h1 := hineq h hh'
    have e : 4 * a / (1 - θ) * ((1 - θ) * h ^ (1 - θ - 1)) = 4 * a * h ^ (-θ) := by
      rw [show 1 - θ - 1 = -θ by ring]; field_simp
    rw [e]; linarith
  have := hmono ⟨le_refl ε, hεS⟩ ⟨hεS, le_refl S⟩ hεS
  simp only at this
  linarith

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
