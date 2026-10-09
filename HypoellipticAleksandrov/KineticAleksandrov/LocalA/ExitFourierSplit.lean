module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitFourierContraction
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitDecompositionMass

/-! # The actual exit Fourier variation is bounded by lateral mass plus killed variation -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo Parabolic
open scoped ENNReal

/-- The actual exit Fourier density-map is additive in finite physical measures. -/
theorem exitFourier_add {d : ℕ} (μ ν : Measure (PDE.Vec d × TimeVelocity d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (ξ : PDE.Vec d) :
    exitFourier (μ + ν) ξ = exitFourier μ ξ + exitFourier ν ξ := by
  apply VectorMeasure.ext
  intro E hE
  rw [exitFourier_apply _ ξ E hE, _root_.add_apply,
    exitFourier_apply μ ξ E hE, exitFourier_apply ν ξ E hE, Measure.restrict_add,
    integral_add_measure (integrable_exitPhase μ ξ).integrableOn
      (integrable_exitPhase ν ξ).integrableOn]

/-- The short-strip Fourier estimate uses exactly the actual lateral loss and killed kernel. -/
theorem ballExit_fourier_short_strip_bound
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})
    (H : {t : ℝ // P.1.time < t ∧ t < T.1}) (ξ : PDE.Vec d) :
    ((exitFourier (ballExit hH hLE hd hlam hLam B hB v₀ hR P T) ξ).variation univ).toReal ≤
      1 - (ballTransition hH hLE hd hlam hLam B hB v₀ hR P ⟨H.1, H.2.1⟩).real univ +
        ((fourierProjection (localBallKernel hH hLE hd hlam hLam B hB v₀ hR)
          (ballEvolutionQuery P ⟨H.1, H.2.1⟩) ξ).variation univ).toReal := by
  let β := (ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P ⟨H.1, H.2.1⟩).restrict
    {Q | Q.velocity ∈ frontier (PDE.euclideanBall v₀ R)}
  let ζ := ballExitRestart hH hLE hd hlam hLam B hB v₀ hR P T H
  let ν := fourierProjection (localBallKernel hH hLE hd hlam hLam B hB v₀ hR)
    (ballEvolutionQuery P ⟨H.1, H.2.1⟩) ξ
  have hs : exitFourier (ballExit hH hLE hd hlam hLam B hB v₀ hR P T) ξ =
      exitFourier (β.map (exitCoordinates P.1 v₀)) ξ +
        exitFourier (ζ.map (exitCoordinates P.1 v₀)) ξ := by
    unfold ballExit
    rw [ballExit_short_strip_measure_decomposition hH hLE hd hlam hLam B hB v₀ hR P T H,
      Measure.map_add _ _ (continuous_exitCoordinates P.1 v₀).measurable, exitFourier_add]
  have he : (exitFourier (ballExit hH hLE hd hlam hLam B hB v₀ hR P T) ξ).variation univ ≤
      β univ + ν.variation univ := by
    rw [hs]
    apply (Measure.le_iff.mp VectorMeasure.variation_add_le univ MeasurableSet.univ).trans
    apply add_le_add
    · have hb := exitFourier_totalVariation_le_mass (β.map (exitCoordinates P.1 v₀)) ξ
      rwa [Measure.map_apply (continuous_exitCoordinates P.1 v₀).measurable
        MeasurableSet.univ, preimage_univ] at hb
    · exact ballExitRestart_fourier_variation_le hH hLE hd hlam hLam B hB v₀ hR P T H ξ
  have hn := fourierProjection_totalVariation_le_one
    (localBallKernel hH hLE hd hlam hLam B hB v₀ hR)
    (ballEvolutionQuery P ⟨H.1, H.2.1⟩) ξ _ (fourierProjection_spec _ _ _)
  have hνfin : ν.variation univ ≠ ⊤ := ne_of_lt (hn.trans_lt ENNReal.one_lt_top)
  have hr := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top β univ, hνfin⟩) he
  rw [ENNReal.toReal_add (measure_ne_top β univ) hνfin] at hr
  change _ ≤ β.real univ + (ν.variation univ).toReal at hr
  dsimp only [β] at hr
  rw [ballExit_lateral_mass hH hLE hd hlam hLam B hB v₀ hR P ⟨H.1, H.2.1⟩] at hr
  exact hr

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
