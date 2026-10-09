module

public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierDomination

/-!
# The Fourier marginal has a density `k^ξ`, dominated by the shifted occupation density

* `ae_enorm_le_of_setIntegral_enorm_le`: `‖∫_E k‖ ≤ ∫_E G` for all `E` gives `‖k‖ ≤ G` a.e.
* `slab_fourier_ae_bound` (Lemma 5.1): any density `k` of the complex
  measure `E ↦ ∫_{(τ,w)∈E, T<τ<2T} e^{-iξ·z} dΓ` on `(T,2T) × ℝ^d` satisfies
  `‖k(τ,w)‖ ≤ g^ξ(τ - T/2, w)` a.e., where `g^ξ` is the occupation density of `|η_T^ξ|`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Green

open MeasureTheory Set
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal NNReal ProbabilityTheory

/-- A density `k` with `‖∫_E k‖ ≤ ∫_E ĝ` for all measurable `E` satisfies `‖k‖ ≤ ĝ` a.e. -/
theorem ae_enorm_le_of_setIntegral_enorm_le {α : Type*} [MeasurableSpace α] (m : Measure α)
    [SigmaFinite m] (k : α → ℂ) (hk : Integrable k m) (G : α → ℝ≥0∞)
    (h : ∀ E, MeasurableSet E → ‖∫ y in E, k y ∂m‖ₑ ≤ ∫⁻ y in E, G y ∂m) :
    ∀ᵐ y ∂m, ‖k y‖ₑ ≤ G y := by
  have hv : (m.withDensityᵥ k).variation = m.withDensity (fun y => ‖k y‖ₑ) :=
    Measure.variation_withDensityᵥ hk
  have hle : (m.withDensityᵥ k).variation ≤ m.withDensity G := by
    refine VectorMeasure.variation_le_of_forall_enorm_le (fun E hE => ?_)
    rw [withDensityᵥ_apply hk hE, withDensity_apply _ hE]
    exact h E hE
  rw [hv] at hle
  refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ hk.aestronglyMeasurable.enorm
    (fun E hE _ => ?_)
  have := Measure.le_iff.1 hle E hE
  rwa [withDensity_apply _ hE, withDensity_apply _ hE] at this


variable {d : ℕ} (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))

/-- **Lemma 5.1: pointwise domination of any density `k^ξ`.**
`gξ` is the occupation density of `|η_T^ξ|` (start time `σ₀ + T/2`, horizon `3T/2`); `k` is any
integrable density of the Fourier marginal. -/
theorem slab_fourier_ae_bound
    (hcov : IsTranslationCovariantEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ K)
    (hcomp : K.HasComposition MeasurableSet.univ) (σ₀ : ℝ)
    (μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀))
    [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier d)) (hΓ : IsGreenMeasure K σ₀ ⊤ μ Γ)
    {T : ℝ} (hT : 0 < T) (ξ : PDE.Vec d) (gξ : ℝ × PDE.Vec d → ℝ)
    (hgξ : SlabOccupationDensity K (σ₀ + T / 2) (3 * T / 2)
      (halfMeasure K σ₀ T hT.le μ ξ).variation gξ)
    (hint : Integrable gξ (volume.restrict (Ioo (0 : ℝ) (3 * T / 2) ×ˢ (univ : Set (PDE.Vec d)))))
    (k : SlabBase d → ℂ) (hk : Integrable k (slabBase d T))
    (hkE : ∀ E : Set (SlabBase d), MeasurableSet E →
      ∫ y in E, k y ∂slabBase d T =
        ∫ p in {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T},
          Complex.exp (-((PDE.vecDot ξ p.2.2 : ℝ) * Complex.I)) ∂Γ) :
    ∀ᵐ y ∂slabBase d T, ‖k y‖ₑ ≤ ENNReal.ofReal (gξ (slabShift d (T / 2) y)) := by
  have hρfin : IsFiniteMeasure (halfMeasure K σ₀ T hT.le μ ξ).variation :=
    evolved_variation_finite μ _ _ _ (measurable_halfPhase ξ _) (norm_halfPhase ξ _)
  refine ae_enorm_le_of_setIntegral_enorm_le (slabBase d T) k hk _ (fun E hE => ?_)
  rw [hkE E hE]
  refine (slab_domination_ineq K hcov hcomp σ₀ μ Γ hΓ hT ξ hE).trans (le_of_eq ?_)
  exact (slab_occupation_identity K (σ₀ + T / 2) (T / 2) T (3 * T / 2) (by linarith) hT
    (by linarith) (by linarith) _ gξ hgξ hint hE).symm

end HypoellipticAleksandrov.KineticAleksandrov.Green
