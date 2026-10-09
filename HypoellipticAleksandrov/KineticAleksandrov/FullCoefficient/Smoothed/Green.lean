module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothed.Divergence
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothed.SlicePackage
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Forward.Main
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.FlowInstance

/-!
# The smoothed equation for the Green measure

The smoothed equation: the abstract smoothing datum `(Γ', B_t)` of `Smoothed/Datum.lean` is the
Green measure `Γ` of the unit point mass at the pole, pushed forward to `ℝ × ℝ^{2d}` along
`((τ, y) ↦ (τ, y))` (the elapsed time as a real coordinate), with `B_t(y) = B(σ₀ + t, y)`.  The
forward equation of `Forward/Main.lean` is `IsForwardMeasure`, the smoothing kernel is the
Gaussian flow kernel, and the commutator is the transport commutator of the flow.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory Set
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal

variable {d : ℕ}

/-- The Green measure with the elapsed time as a real coordinate. -/
def greenPushforward {S : ℝ≥0∞} (Γ : Measure (ElapsedTime S × EvolutionAmbientState d)) :
    Measure (ℝ × EvolutionAmbientState d) :=
  Γ.map fun q => (q.1.1, q.2)

/-- The coefficient `B_t(y) = B(σ₀ + t, y)` on `ℝ × ℝ^{2d}`. -/
def greenCoefficient (σ₀ : ℝ) (B : FullKineticCoefficient d) :
    ℝ → EvolutionAmbientState d → PDE.Mat d :=
  fun t y => B (σ₀ + t) y.1 y.2

theorem measurable_greenMap {S : ℝ≥0∞} :
    Measurable fun q : ElapsedTime S × EvolutionAmbientState d => (q.1.1, q.2) :=
  (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd

variable {lam Lam T : ℝ}

theorem isFiniteMeasure_green (K : MovingFiberKernel (wholeSpace d) (fun _ => 0))
    (σ₀ : ℝ) (hT : 0 < T) (p : EvolutionState (wholeSpace d) (fun _ => 0) σ₀)
    (Γ : Measure (ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d))
    (hΓ : IsGreenMeasure K σ₀ (ENNReal.ofReal T) (Measure.dirac p) Γ) : IsFiniteMeasure Γ :=
  ⟨lt_of_le_of_lt (greenMeasure_mass_le K σ₀ T hT (Measure.dirac p) Γ hΓ)
    (ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top)⟩

/-- The time marginal of the pushed-forward Green measure is dominated by Lebesgue measure. -/
theorem greenPushforward_marginal_le {S : ℝ≥0∞}
    (Γ : Measure (ElapsedTime S × EvolutionAmbientState d))
    (hle : ∀ A : Set (ElapsedTime S), MeasurableSet A →
      Γ (Prod.fst ⁻¹' A) ≤ elapsedVolume S A) :
    (greenPushforward Γ).map Prod.fst ≤ volume := by
  refine Measure.le_iff.2 fun s hs => ?_
  unfold greenPushforward
  rw [Measure.map_apply measurable_fst hs,
    Measure.map_apply measurable_greenMap (measurable_fst hs)]
  have hA : MeasurableSet (Subtype.val ⁻¹' s : Set (ElapsedTime S)) := measurable_subtype_coe hs
  calc Γ ((fun q : ElapsedTime S × EvolutionAmbientState d => (q.1.1, q.2)) ⁻¹'
        (Prod.fst ⁻¹' s)) = Γ (Prod.fst ⁻¹' (Subtype.val ⁻¹' s)) := rfl
    _ ≤ elapsedVolume S (Subtype.val ⁻¹' s) := hle _ hA
    _ = volume (Subtype.val '' (Subtype.val ⁻¹' s)) := elapsedVolume_apply S _ hA
    _ ≤ volume s := measure_mono (image_preimage_subset _ _)

/-- The Green measure with the coefficient `B_t` is a smoothing datum. -/
theorem isSmoothingDatum_green (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : FullKineticCoefficient d) (hB : IsSmoothFullKineticCoefficient B)
    (hBs : IsSymmetricFullKineticCoefficient B) (hell : HasEverywhereLoewnerBounds lam Lam B)
    (σ₀ : ℝ) {S : ℝ≥0∞} (Γ : Measure (ElapsedTime S × EvolutionAmbientState d))
    [IsFiniteMeasure Γ]
    (hle : ∀ A : Set (ElapsedTime S), MeasurableSet A →
      Γ (Prod.fst ⁻¹' A) ≤ elapsedVolume S A) :
    IsSmoothingDatum lam Lam (greenCoefficient σ₀ B) (greenPushforward Γ) where
  lam_pos := hlam
  lam_le := hLam
  finite := by unfold greenPushforward; infer_instance
  marginal := greenPushforward_marginal_le Γ hle
  measurable := fun i j =>
    ((hB i j).continuous.comp ((continuous_const.add continuous_fst).prodMk
      continuous_snd)).measurable
  symm := fun t y => hBs _ _ _
  loewner := fun t y => hell _ _ _

/-- **The forward equation for the pushed-forward Green measure**, in the form `IsForwardMeasure`.
-/
theorem isForwardMeasure_green (hd : 1 ≤ d) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : FullKineticCoefficient d) (hB : IsSmoothFullKineticCoefficient B)
    (hBs : IsSymmetricFullKineticCoefficient B) (hell : HasEverywhereLoewnerBounds lam Lam B)
    (S : TerminalOperatorFamily (wholeSpace d) (fun _ => 0))
    (K : MovingFiberKernel (wholeSpace d) (fun _ => 0))
    (hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ B
      (identityDrift d) S K)
    (σ₀ : ℝ) (hT : 0 < T) (p : EvolutionState (wholeSpace d) (fun _ => 0) σ₀)
    (Γ : Measure (ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d))
    (hΓ : IsGreenMeasure K σ₀ (ENNReal.ofReal T) (Measure.dirac p) Γ) :
    IsForwardMeasure T (greenCoefficient σ₀ B) (greenPushforward Γ) := by
  intro φ hφ
  obtain ⟨h1, h2, h3, h4⟩ := forward_equation hd hlam hLam B hB hBs hell S K hreal σ₀ hT p Γ hΓ hφ
  have hg := measurable_greenMap (S := ENNReal.ofReal T) (d := d)
  have c1 : Continuous fun q : ℝ × EvolutionAmbientState d =>
      deriv (fun s => φ s q.2) q.1 := hφ.timeDeriv.1
  have c2 : Continuous fun q : ℝ × EvolutionAmbientState d =>
      velocityHessianContraction (greenCoefficient σ₀ B q.1 q.2) (φ q.1) q.2 :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (((hB i j).continuous.comp ((continuous_const.add continuous_fst).prodMk
        continuous_snd))).mul (hφ.velocityHess i j).1
  have c3 : Continuous fun q : ℝ × EvolutionAmbientState d =>
      transportDerivative (φ q.1) q.2 :=
    continuous_finsetSum _ fun i _ => (hφ.weightedTransport i i).1
  unfold greenPushforward
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (integrable_map_measure c1.aestronglyMeasurable hg.aemeasurable).2 h1
  · exact (integrable_map_measure c2.aestronglyMeasurable hg.aemeasurable).2 h2
  · exact (integrable_map_measure c3.aestronglyMeasurable hg.aemeasurable).2 h3
  · have hsum : Continuous fun q : ℝ × EvolutionAmbientState d =>
        deriv (fun s => φ s q.2) q.1 +
          velocityHessianContraction (greenCoefficient σ₀ B q.1 q.2) (φ q.1) q.2 +
            transportDerivative (φ q.1) q.2 := (c1.add c2).add c3
    rw [integral_map hg.aemeasurable hsum.aestronglyMeasurable]
    exact h4

/-- The smoothed density `ρ(τ, y)` of the Green measure, for the flow kernel. -/
abbrev greenDensity (hlam : 0 < lam) (η : ℝ → ℝ) (h : ℝ)
    (Γ : Measure (ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d)) :
    ℝ → EvolutionAmbientState d → ℝ :=
  smoothedDensity (flowKernelFamily hlam) η h (greenPushforward Γ)

/-- The smoothed flux `J(τ, y)` of the Green measure, for the flow kernel. -/
abbrev greenFlux (hlam : 0 < lam) (η : ℝ → ℝ) (B : FullKineticCoefficient d) (σ₀ Lam h : ℝ)
    (Γ : Measure (ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d)) :
    ℝ → EvolutionAmbientState d → PDE.Mat d :=
  smoothedFlux (flowKernelFamily hlam) η (greenCoefficient σ₀ B) Lam h (greenPushforward Γ)

/-- The smoothed coefficient `β_h(τ, y)` of the Green measure, for the flow kernel. -/
abbrev greenBeta (hlam : 0 < lam) (η : ℝ → ℝ) (B : FullKineticCoefficient d) (σ₀ Lam h : ℝ)
    (Γ : Measure (ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d)) :
    ℝ → EvolutionAmbientState d → PDE.Mat d :=
  smoothedBeta (flowKernelFamily hlam) η (greenCoefficient σ₀ B) Lam h (greenPushforward Γ)

/-- **The smoothed equation for the Green measure**. -/
theorem green_smoothed_equation (hd : 1 ≤ d) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : FullKineticCoefficient d) (hB : IsSmoothFullKineticCoefficient B)
    (hBs : IsSymmetricFullKineticCoefficient B) (hell : HasEverywhereLoewnerBounds lam Lam B)
    (S : TerminalOperatorFamily (wholeSpace d) (fun _ => 0))
    (K : MovingFiberKernel (wholeSpace d) (fun _ => 0))
    (hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ B
      (identityDrift d) S K)
    (σ₀ : ℝ) (hT : 0 < T) (p : EvolutionState (wholeSpace d) (fun _ => 0) σ₀)
    (Γ : Measure (ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d))
    (hΓ : IsGreenMeasure K σ₀ (ENNReal.ofReal T) (Measure.dirac p) Γ)
    {δ : ℝ} {η : ℝ → ℝ} (hη : IsMollifier δ η) {h τ : ℝ} (hh : 0 < h) (hδ : 0 < δ)
    (hτ : δ < τ) (hτT : τ + δ < T) (y : EvolutionAmbientState d) :
    deriv (fun τ' => greenDensity hlam η h Γ τ' y) τ +
        transportDerivative (greenDensity hlam η h Γ τ) y =
      lam * h ^ 2 / 2 * positionLaplacian (greenDensity hlam η h Γ τ) y -
        lam * h * mixedDivergence (greenDensity hlam η h Γ τ) y +
        ∑ i, ∑ j, velocityPartial i (velocityPartial j
          (fun y => greenFlux hlam η B σ₀ Lam h Γ τ y i j)) y := by
  have : IsFiniteMeasure Γ := isFiniteMeasure_green K σ₀ hT p Γ hΓ
  exact smoothed_equation (flowKernelFamily hlam) hη
    (isSmoothingDatum_green hlam hLam B hB hBs hell σ₀ Γ
      (fun A hA => green_prod_fst_le K σ₀ (ENNReal.ofReal T) p Γ hΓ A hA)) hh hδ hτ hτT
    (isForwardMeasure_green hd hlam hLam B hB hBs hell S K hreal σ₀ hT p Γ hΓ)
    (fun w => transportDerivative_flowKernel hlam hh w) y

/-- **The smoothed equation in divergence form for the Green measure**, on a non-zero slice. -/
theorem green_smoothed_equation_div (hd : 1 ≤ d) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : FullKineticCoefficient d) (hB : IsSmoothFullKineticCoefficient B)
    (hBs : IsSymmetricFullKineticCoefficient B) (hell : HasEverywhereLoewnerBounds lam Lam B)
    (S : TerminalOperatorFamily (wholeSpace d) (fun _ => 0))
    (K : MovingFiberKernel (wholeSpace d) (fun _ => 0))
    (hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ B
      (identityDrift d) S K)
    (σ₀ : ℝ) (hT : 0 < T) (p : EvolutionState (wholeSpace d) (fun _ => 0) σ₀)
    (Γ : Measure (ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d))
    (hΓ : IsGreenMeasure K σ₀ (ENNReal.ofReal T) (Measure.dirac p) Γ)
    {δ : ℝ} {η : ℝ → ℝ} (hη : IsMollifier δ η) {h τ : ℝ} (hh : 0 < h) (hδ : 0 < δ)
    (hτ : δ < τ) (hτT : τ + δ < T)
    (hm : averagedSlice η τ (greenPushforward Γ) ≠ 0) (y : EvolutionAmbientState d) :
    deriv (fun τ' => greenDensity hlam η h Γ τ' y) τ +
        transportDerivative (greenDensity hlam η h Γ τ) y =
      divGradFlux lam h (greenBeta hlam η B σ₀ Lam h Γ τ) (greenDensity hlam η h Γ τ) y +
        divDensityDivBeta (greenBeta hlam η B σ₀ Lam h Γ τ) (greenDensity hlam η h Γ τ) y := by
  have : IsFiniteMeasure Γ := isFiniteMeasure_green K σ₀ hT p Γ hΓ
  exact smoothed_equation_div (flowKernelFamily hlam) hη
    (isSmoothingDatum_green hlam hLam B hB hBs hell σ₀ Γ
      (fun A hA => green_prod_fst_le K σ₀ (ENNReal.ofReal T) p Γ hΓ A hA)) hh hδ hτ hτT
    (isForwardMeasure_green hd hlam hLam B hB hBs hell S K hreal σ₀ hT p Γ hΓ)
    (fun w => transportDerivative_flowKernel hlam hh w) hm y

/-- The pushed-forward Green measure of a point mass with the coefficient `B_t` is a smoothing
datum, so that all abstract results of `Smoothed/*` apply to it. -/
theorem green_datum (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : FullKineticCoefficient d) (hB : IsSmoothFullKineticCoefficient B)
    (hBs : IsSymmetricFullKineticCoefficient B) (hell : HasEverywhereLoewnerBounds lam Lam B)
    (K : MovingFiberKernel (wholeSpace d) (fun _ => 0))
    (σ₀ : ℝ) (hT : 0 < T) (p : EvolutionState (wholeSpace d) (fun _ => 0) σ₀)
    (Γ : Measure (ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d))
    (hΓ : IsGreenMeasure K σ₀ (ENNReal.ofReal T) (Measure.dirac p) Γ) :
    IsSmoothingDatum lam Lam (greenCoefficient σ₀ B) (greenPushforward Γ) := by
  have : IsFiniteMeasure Γ := isFiniteMeasure_green K σ₀ hT p Γ hΓ
  exact isSmoothingDatum_green hlam hLam B hB hBs hell σ₀ Γ
    (fun A hA => green_prod_fst_le K σ₀ (ENNReal.ofReal T) p Γ hΓ A hA)

/-- `ρ` is jointly smooth in `(τ, y)` for the Green measure. -/
theorem contDiff_greenDensity (hlam : 0 < lam)
    (Γ : Measure (ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d))
    [IsFiniteMeasure Γ] {δ : ℝ} {η : ℝ → ℝ} (hη : IsMollifier δ η) {h : ℝ} (hh : 0 < h) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × EvolutionAmbientState d =>
      greenDensity hlam η h Γ p.1 p.2) := by
  have : IsFiniteMeasure (greenPushforward Γ) := by unfold greenPushforward; infer_instance
  exact contDiff_smoothedDensity (flowKernelFamily hlam) hη hh

/-- The entries of `J` are jointly smooth in `(τ, y)` for the Green measure. -/
theorem contDiff_greenFlux (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : FullKineticCoefficient d) (hB : IsSmoothFullKineticCoefficient B)
    (hBs : IsSymmetricFullKineticCoefficient B) (hell : HasEverywhereLoewnerBounds lam Lam B)
    (K : MovingFiberKernel (wholeSpace d) (fun _ => 0))
    (σ₀ : ℝ) (hT : 0 < T) (p : EvolutionState (wholeSpace d) (fun _ => 0) σ₀)
    (Γ : Measure (ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d))
    (hΓ : IsGreenMeasure K σ₀ (ENNReal.ofReal T) (Measure.dirac p) Γ)
    {δ : ℝ} {η : ℝ → ℝ} (hη : IsMollifier δ η) {h : ℝ} (hh : 0 < h) (i j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × EvolutionAmbientState d =>
      greenFlux hlam η B σ₀ Lam h Γ q.1 q.2 i j) := by
  have hD := green_datum hlam hLam B hB hBs hell K σ₀ hT p Γ hΓ
  have := hD.finite
  exact contDiff_smoothedFlux (flowKernelFamily hlam) hη hD.marginal hD.measurable
    hD.abs_apply_le hD.lam_nonneg_Lam hD.loewner hh i j

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
