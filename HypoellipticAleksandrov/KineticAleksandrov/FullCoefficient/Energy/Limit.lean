module

public import Mathlib.MeasureTheory.Integral.Prod
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Calculus

/-!
# Fatou's lemma for the removal of the cut-off

The energy inequality, last step: if the cut-off integrals satisfy a
bound with a convergent right-hand side, so does the limit integral. This is the double Fatou
argument (in `y`, then in `τ`) for the iterated integral of a non-negative measurable function.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory Filter Topology

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

theorem lintegral_cutoff_le_of_bound {S : Set ℝ} (F : ℝ × EvolutionAmbientState d → ℝ)
    (hF : Measurable F) {ζ : ℕ → EvolutionAmbientState d → ℝ} (hζm : ∀ n, Measurable (ζ n))
    (hlim : ∀ y, Tendsto (fun n => ζ n y) atTop (𝓝 1)) {c : ENNReal} (hc : c ≠ 0) (hct : c ≠ ⊤)
    {W : ℕ → ENNReal} {W' : ENNReal} (hW : Tendsto W atTop (𝓝 W'))
    (hbd : ∀ n, c * ∫⁻ τ in S, ∫⁻ y, ENNReal.ofReal (ζ n y * F (τ, y)) ≤ W n) :
    c * ∫⁻ τ in S, ∫⁻ y, ENNReal.ofReal (F (τ, y)) ≤ W' := by
  have hmeas1 : ∀ n τ, Measurable fun y => ENNReal.ofReal (ζ n y * F (τ, y)) := fun n τ =>
    ENNReal.measurable_ofReal.comp ((hζm n).mul (hF.comp measurable_prodMk_left))
  have hmeas2 : ∀ n, Measurable fun τ : ℝ => ∫⁻ y, ENNReal.ofReal (ζ n y * F (τ, y)) :=
    fun n => Measurable.lintegral_prod_right'
      (f := fun p : ℝ × EvolutionAmbientState d => ENNReal.ofReal (ζ n p.2 * F p))
      (ENNReal.measurable_ofReal.comp (((hζm n).comp measurable_snd).mul hF))
  have h1 : ∀ τ : ℝ, ∫⁻ y, ENNReal.ofReal (F (τ, y)) ≤
      liminf (fun n => ∫⁻ y, ENNReal.ofReal (ζ n y * F (τ, y))) atTop := fun τ => by
    calc ∫⁻ y, ENNReal.ofReal (F (τ, y))
        = ∫⁻ y, liminf (fun n => ENNReal.ofReal (ζ n y * F (τ, y))) atTop := by
          refine lintegral_congr fun y => ?_
          have := ENNReal.tendsto_ofReal ((hlim y).mul_const (F (τ, y)))
          rw [one_mul] at this
          exact this.liminf_eq.symm
      _ ≤ _ := lintegral_liminf_le (hmeas1 · τ)
  have h2 : ∫⁻ τ in S, ∫⁻ y, ENNReal.ofReal (F (τ, y)) ≤
      liminf (fun n => ∫⁻ τ in S, ∫⁻ y, ENNReal.ofReal (ζ n y * F (τ, y))) atTop :=
    (lintegral_mono h1).trans (lintegral_liminf_le hmeas2)
  have h3 : ∀ n, ∫⁻ τ in S, ∫⁻ y, ENNReal.ofReal (ζ n y * F (τ, y)) ≤ c⁻¹ * W n := fun n =>
    (ENNReal.mul_le_iff_le_inv hc hct).1 (hbd n)
  have h4 : Tendsto (fun n => c⁻¹ * W n) atTop (𝓝 (c⁻¹ * W')) :=
    ENNReal.Tendsto.const_mul hW (Or.inr (ENNReal.inv_ne_top.2 hc))
  have h5 : liminf (fun n => ∫⁻ τ in S, ∫⁻ y, ENNReal.ofReal (ζ n y * F (τ, y))) atTop ≤
      c⁻¹ * W' := by
    rw [← h4.liminf_eq]
    exact liminf_le_liminf (Eventually.of_forall h3)
  exact (ENNReal.mul_le_iff_le_inv hc hct).2 (h2.trans h5)

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
