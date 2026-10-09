module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Absorb.GreenLimitB

/-!
# The mollified absorption bound on a time slab, for the Green measure
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory ProbabilityTheory Filter Topology
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal

variable {d : ℕ} {lam Lam T q : ℝ}

/-- The absorption constant `C₁ = 2 c^{q-1} (1 + 4/(1-2d(q-1)))`. -/
def absorbConst (d : ℕ) (lam q : ℝ) : ℝ :=
  2 * flowSupConstant d lam ^ (q - 1) * (1 + 4 / (1 - 2 * (d : ℝ) * (q - 1)))

theorem green_slab_lintegral_le (hd : 1 ≤ d) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : FullKineticCoefficient d) (hB : IsSmoothFullKineticCoefficient B)
    (hBs : IsSymmetricFullKineticCoefficient B) (hell : HasEverywhereLoewnerBounds lam Lam B)
    (S : TerminalOperatorFamily (wholeSpace d) (fun _ => 0))
    (K : MovingFiberKernel (wholeSpace d) (fun _ => 0))
    (hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ B
      (identityDrift d) S K)
    (σ₀ : ℝ) (hT : 0 < T) (p : EvolutionState (wholeSpace d) (fun _ => 0) σ₀)
    (Γ : Measure (ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d))
    (hΓ : IsGreenMeasure K σ₀ (ENNReal.ofReal T) (Measure.dirac p) Γ)
    (hq : 1 < q) (hqΛ : q ≤ 1 + 3 * lam ^ 2 / (128 * (d : ℝ) ^ 2 * Lam ^ 2))
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} {τ₁ τ₂ : ℝ} (hτ : τ₁ < τ₂) (hτ₁ : mollRadius n < τ₁)
    (hτ₂ : τ₂ + mollRadius n < T) :
    ∫⁻ x in (fun x : ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d => x.1.1) ⁻¹'
        Set.Ioo τ₁ τ₂, ENNReal.ofReal (greenDensity hlam (mollN n) ε Γ x.1.1 x.2 ^ q)
      ∂((elapsedVolume (ENNReal.ofReal T)).prod (volume : Measure (EvolutionAmbientState d))) ≤
      ENNReal.ofReal (absorbConst d lam q * T ^ (1 - 2 * (d : ℝ) * (q - 1))) := by
  obtain ⟨hq43, hθ, hκ⟩ := qstar_facts hd hlam hLam hq hqΛ
  have hfin : IsFiniteMeasure Γ := isFiniteMeasure_green K σ₀ hT p Γ hΓ
  have hD := green_datum hlam hLam B hB hBs hell K σ₀ hT p Γ hΓ
  have hfin' : IsFiniteMeasure (greenPushforward Γ) := hD.finite
  have hη := isMollifier_mollN n
  have hδ := mollRadius_pos n
  have hab : Set.Ioo τ₁ τ₂ ⊆ Set.Ioo 0 T := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hc : Continuous fun p : ℝ × EvolutionAmbientState d =>
      greenDensity hlam (mollN n) ε Γ p.1 p.2 :=
    (contDiff_greenDensity hlam Γ hη hε).continuous
  have hG : Measurable fun p : ℝ × EvolutionAmbientState d =>
      ENNReal.ofReal (greenDensity hlam (mollN n) ε Γ p.1 p.2 ^ q) :=
    ENNReal.measurable_ofReal.comp (hc.measurable.pow_const q)
  rw [lintegral_elapsed_slab (G := fun p : ℝ × EvolutionAmbientState d =>
    ENNReal.ofReal (greenDensity hlam (mollN n) ε Γ p.1 p.2 ^ q)) hT hab hG]
  have hslice : ∀ t : ℝ, ∫⁻ y, ENNReal.ofReal (greenDensity hlam (mollN n) ε Γ t y ^ q) =
      ENNReal.ofReal (∫ y, smoothedDensity (flowKernelFamily (d := d) hlam) (mollN n) ε
        (greenPushforward Γ) t y ^ q) := fun t => by
    have := isFiniteMeasure_averagedSlice_of_datum (τ := t) hη hD
    have hi := (integral_smoothDensity_pow_le (flowKernelFamily (d := d) hlam)
      (averagedSlice (mollN n) t (greenPushforward Γ))
      (averagedSlice_real_univ_le_of_datum hη hD) hε hq).1
    exact (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun y =>
      Real.rpow_nonneg (smoothDensity_nonneg _ _ hε y) _)).symm
  simp only [hslice]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_tau_pow (flowKernelFamily (d := d) hlam) hη hD hε hq)
    (Filter.Eventually.of_forall fun t => slice_pow_nonneg _ hε t)]
  refine ENNReal.ofReal_le_ofReal ?_
  exact absorb_datum (flowKernelFamily (d := d) hlam) hη hD hδ hq hq43 hθ hκ hτ hτ₁ hτ₂
    (by linarith) (isForwardMeasure_green hd hlam hLam B hB hBs hell S K hreal σ₀ hT p Γ hΓ)
    (fun h hh w => transportDerivative_flowKernel hlam hh w) hε

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
