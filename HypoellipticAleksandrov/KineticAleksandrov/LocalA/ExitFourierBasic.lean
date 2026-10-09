module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitDecomposition
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.KilledFourier
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

/-! # Integral characterization and total variation of the actual exit Fourier measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo Parabolic
open scoped ENNReal

/-- The literal exit Fourier measure has the density-map integral characterization. -/
theorem exitFourier_apply {d : ℕ}
    (ω : Measure (PDE.Vec d × TimeVelocity d)) [IsFiniteMeasure ω]
    (ξ : PDE.Vec d) (E : Set (TimeVelocity d)) (hE : MeasurableSet E) :
    exitFourier ω ξ E = ∫ z in Prod.snd ⁻¹' E, exitPhase ξ z ∂ω := by
  unfold exitFourier
  rw [VectorMeasure.map_apply _ measurable_snd hE,
    withDensityᵥ_apply (integrable_exitPhase ω ξ) (measurable_snd hE)]

/-- Fourier density and projection cannot increase the total mass of a finite exit measure. -/
theorem exitFourier_variation_le {d : ℕ}
    (ω : Measure (PDE.Vec d × TimeVelocity d)) [IsFiniteMeasure ω] (ξ : PDE.Vec d) :
    (exitFourier ω ξ).variation ≤ ω.map Prod.snd := by
  apply VectorMeasure.variation_map_le.trans
  rw [Measure.variation_withDensityᵥ (integrable_exitPhase ω ξ)]
  have hp : (fun z => ‖exitPhase ξ z‖ₑ) = 1 := by
    funext z
    rw [← ofReal_norm, norm_exitPhase]
    norm_num
  rw [hp, withDensity_one]

/-- The Fourier total variation is bounded by the original finite total mass. -/
theorem exitFourier_totalVariation_le_mass {d : ℕ}
    (ω : Measure (PDE.Vec d × TimeVelocity d)) [IsFiniteMeasure ω] (ξ : PDE.Vec d) :
    (exitFourier ω ξ).variation univ ≤ ω univ := by
  have h := Measure.le_iff.mp (exitFourier_variation_le ω ξ) univ MeasurableSet.univ
  rwa [Measure.map_apply measurable_snd MeasurableSet.univ, preimage_univ] at h

/-- The actual ball exit Fourier measure has total variation at most one. -/
theorem ballExit_fourier_totalVariation_le_one
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t}) (ξ : PDE.Vec d) :
    (exitFourier (ballExit hH hLE hd hlam hLam B hB v₀ hR P T) ξ).variation univ ≤ 1 := by
  exact (exitFourier_totalVariation_le_mass _ ξ).trans_eq
    (ballExit_mass hH hLE hd hlam hLam B hB v₀ hR P T)

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
