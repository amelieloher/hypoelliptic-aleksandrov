module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomyBoundedData
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ScalarAdapters

/-! # Physical-coordinate generator of the full-space autonomous action -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set MeasureTheory
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

/-- Exchange position and velocity, and reverse terminal time into elapsed time. -/
def autonomousReversal (p : Point) : Point := ⟨-p.time, p.velocity, p.position⟩

/-- The generator equation uses positive transport and diffusion on its right side. -/
def autonomousGeneratorResidual (a : ℝ → ℝ → ℝ) (u : Point → ℝ) (p : Point) : ℝ :=
  kineticTimeDerivative u p - p.velocity 0 * kineticPositionGradient u p 0 -
    a (p.position 0) (p.velocity 0) * kineticVelocityHessian u p 0 0

/-- Reflect physical position without changing elapsed time or velocity. -/
def autonomousPositionReflection (p : Point) : Point :=
  ⟨p.time, -p.position, p.velocity⟩

/-- Position reflection converts the generator equation to the source PDE convention. -/
theorem autonomous_generator_positionReflection (a : ℝ → ℝ → ℝ)
    (u : Point → ℝ) (p : Point) :
    autonomousScalarOperator (reflectedAutonomous a) (u ∘ autonomousPositionReflection) p =
      autonomousGeneratorResidual a u (autonomousPositionReflection p) := by
  have hg : kineticPositionGradient (u ∘ autonomousPositionReflection) p =
      -kineticPositionGradient u (autonomousPositionReflection p) := by
    ext i
    let f : PDE.Vec 1 → ℝ := fun x => u ⟨p.time, x, p.velocity⟩
    let e := ContinuousLinearEquiv.neg ℝ (M := PDE.Vec 1)
    change (fderiv ℝ (f ∘ e) p.position) (PDE.basisVec i) =
      -(fderiv ℝ f (-p.position)) (PDE.basisVec i)
    rw [e.comp_right_fderiv]
    simp [e]
  rw [autonomousScalarOperator, autonomousGeneratorResidual, hg]
  change kineticTimeDerivative u (autonomousPositionReflection p) +
      p.velocity 0 * (-kineticPositionGradient u (autonomousPositionReflection p) 0) -
      a (-p.position 0) (p.velocity 0) *
        kineticVelocityHessian u (autonomousPositionReflection p) 0 0 = _
  dsimp only [autonomousPositionReflection, Pi.neg_apply]
  ring

/-- The time and coordinate exchange gives the source generator with its literal sign. -/
theorem autonomous_generator_reversal (a : ℝ → ℝ → ℝ) (u : Point → ℝ) (p : Point) :
    autonomousGeneratorResidual a (u ∘ autonomousReversal) p =
      -transportedForwardOperator (evolutionCoefficient a) (identityDrift 1) u
        (autonomousReversal p) := by
  rw [autonomousGeneratorResidual, transportedForwardOperator_apply]
  have ht : kineticTimeDerivative (u ∘ autonomousReversal) p =
      -kineticTimeDerivative u (autonomousReversal p) :=
    deriv_comp_neg (fun r => u ⟨r, p.velocity, p.position⟩) p.time
  rw [ht]
  simp only [matrixContraction, Fin.sum_univ_one, fullKineticCoefficientAt,
    evolutionCoefficient, PDE.vecDot, identityDrift]
  change -kineticTimeDerivative u (autonomousReversal p) -
      p.velocity 0 * kineticVelocityGradient u (autonomousReversal p) 0 -
      a (p.position 0) (p.velocity 0) * diffusedHessian u (autonomousReversal p) 0 0 = _
  dsimp only [autonomousReversal, id_eq]
  ring

/-- Physical terminal data use position first, velocity second. -/
def physicalTerminalDatum (F : BoundedBorel (EvolutionAmbientState 1)) :
    BoundedBorel (EvolutionAmbientState 1) :=
  F.pullback Prod.swap measurable_swap

/-- The supplied full-space kernel action has the physical generator for bounded smooth data.
The represented function is defined for all positive elapsed times by the actual kernel. -/
theorem fullspace_bounded_smooth_generator
    (hH : HormanderHypoellipticityStatement) {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (F : BoundedBorel (EvolutionAmbientState 1)) (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ∃ U : Point → ℝ,
      (∀ (p : Point) (hp : 0 ≤ p.time),
        U p = ∫ x, F (x.2, x.1) ∂E.2.master
          (wholeSpaceQuery (-p.time) 0 (neg_nonpos.mpr hp) p.velocity p.position)) ∧
      (∀ p : Point, 0 < p.time → autonomousGeneratorResidual A.a U p = 0) ∧
      (∀ p : Point, 0 < p.time →
        autonomousScalarOperator (reflectedAutonomous A.a)
          (U ∘ autonomousPositionReflection) p = 0) := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (physicalTerminalDatum F) :=
    hF.comp (contDiff_snd.prodMk contDiff_fst)
  obtain ⟨u, hu, hr⟩ := fullspace_bounded_smooth_solution hH hlam hLam A E hE
    0 (physicalTerminalDatum F) hs
  refine ⟨u ∘ autonomousReversal, ?_, ?_, ?_⟩
  · intro p hp
    exact hr (wholeSpaceQuery (-p.time) 0 (by linarith) p.velocity p.position) rfl
  · intro p hp
    rw [autonomous_generator_reversal]
    have hi : autonomousReversal p ∈
        evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) 0 :=
      ⟨by change -p.time < 0; linarith, by
        change p.velocity ∈ movingDomain (wholeSpace 1) (fun _ => 0) (-p.time)
        rw [movingDomain_wholeSpace]; trivial⟩
    rw [hu.2.2.2.1 _ hi, neg_zero]
  · intro p hp
    rw [autonomous_generator_positionReflection, autonomous_generator_reversal]
    have hi : autonomousReversal (autonomousPositionReflection p) ∈
        evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) 0 :=
      ⟨by change -p.time < 0; linarith, by
        change p.velocity ∈ movingDomain (wholeSpace 1) (fun _ => 0) (-p.time)
        rw [movingDomain_wholeSpace]; trivial⟩
    rw [hu.2.2.2.1 _ hi, neg_zero]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
