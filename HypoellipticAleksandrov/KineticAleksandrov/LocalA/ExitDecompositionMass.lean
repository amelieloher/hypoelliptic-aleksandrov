module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitDecomposition

/-! # The lateral exit mass is exactly the actual killed mass loss -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo Parabolic

/-- The terminal corner stays lateral, and its total mass is the precise killed loss. -/
theorem ballExit_lateral_mass
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t}) :
    ((ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T).restrict
      {Q | Q.velocity ∈ frontier (PDE.euclideanBall v₀ R)}).real univ =
      1 - (ballTransition hH hLE hd hlam hLam B hB v₀ hR P T).real univ := by
  have hf : IsFiniteMeasure (ballTransition hH hLE hd hlam hLam B hB v₀ hR P T) :=
    ⟨((localBallKernel hH hLE hd hlam hLam B hB v₀ hR).mass_le_one
      (ballEvolutionQuery P T)).trans_lt ENNReal.one_lt_top⟩
  let μ := ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T
  let S : Set (KineticPoint d) := {Q | Q.velocity ∈ PDE.euclideanBall v₀ R}
  have hS : MeasurableSet S :=
    (PDE.isOpen_euclideanBall v₀ R).measurableSet.preimage continuous_velocity.measurable
  have ht := congrArg (fun ν : Measure (EvolutionAmbientState d) => ν univ)
    (ballExit_terminal_interior_map hH hLE hd hlam hLam B hB v₀ hR P T)
  rw [Measure.map_apply continuous_exitStateCoordinates.measurable MeasurableSet.univ,
    preimage_univ] at ht
  have ha := congrArg (fun ν : Measure (KineticPoint d) => ν univ)
    (Measure.restrict_add_restrict_compl hS (μ := μ))
  rw [Measure.add_apply, ht, ballExit_lateral_restrict hH hLE hd hlam hLam B hB v₀ hR P T,
    ballExitRaw_mass hH hLE hd hlam hLam B hB v₀ hR P T] at ha
  have hr := congrArg ENNReal.toReal ha
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    ENNReal.toReal_one] at hr
  change _ + _ = 1 at hr
  dsimp only [Measure.real]
  linarith only [hr]

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
