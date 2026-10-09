module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomyGenerator
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.PastGluingLocality

/-! # The literal physical full-space action and its generator equation -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set MeasureTheory Filter
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped Topology

/-- Elapsed-time kernel action, with physical state order `(X,v)`. -/
def fullSpaceAction (E : FullSpaceEvolution) (F : BoundedBorel (EvolutionAmbientState 1))
    (p : Point) : ℝ :=
  if hp : 0 ≤ p.time then
    ∫ x, F (x.2, x.1) ∂E.2.master
      (wholeSpaceQuery (-p.time) 0 (neg_nonpos.mpr hp) p.velocity p.position)
  else F (p.position, p.velocity)

/-- The definition agrees exactly with the source kernel formula at times `0,t`. -/
theorem fullSpaceAction_eq_zeroTime {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (F : BoundedBorel (EvolutionAmbientState 1)) (p : Point) (hp : 0 ≤ p.time) :
    fullSpaceAction E F p = ∫ x, F (x.2, x.1) ∂E.2.master
      (wholeSpaceQuery 0 p.time hp p.velocity p.position) := by
  rw [fullSpaceAction, dite_eq_left hp]
  have hk := fullspace_kernel_timeShift A E hE p.time
    (wholeSpaceQuery (-p.time) 0 (neg_nonpos.mpr hp) p.velocity p.position)
  have hq : autonomousQueryShift p.time
      (wholeSpaceQuery (-p.time) 0 (neg_nonpos.mpr hp) p.velocity p.position) =
      wholeSpaceQuery 0 p.time hp p.velocity p.position := by
    apply Subtype.ext
    dsimp only [autonomousQueryShift, wholeSpaceQuery]
    congr 1 <;> ring
  rw [hq] at hk
  exact congrArg (fun μ => ∫ x, F (x.2, x.1) ∂μ) hk.symm

/-- The elapsed-time coordinate reversal is a continuous involution. -/
theorem autonomousReversal_continuous : Continuous autonomousReversal :=
  KineticPoint.continuous_mk continuous_time.neg continuous_velocity continuous_position

/-- Reversing twice gives the same physical point. -/
theorem autonomousReversal_involutive (p : Point) :
    autonomousReversal (autonomousReversal p) = p := by
  ext <;> simp [autonomousReversal]

/-- The literal physical generator depends only on the local germ. -/
theorem autonomousGeneratorResidual_congr_germ (a : ℝ → ℝ → ℝ)
    {u v : Point → ℝ} {p : Point} (h : u =ᶠ[𝓝 p] v) :
    autonomousGeneratorResidual a u p = autonomousGeneratorResidual a v p := by
  have hc : (u ∘ autonomousReversal) =ᶠ[𝓝 (autonomousReversal p)]
      (v ∘ autonomousReversal) := by
    have ht := autonomousReversal_continuous.tendsto (autonomousReversal p)
    rw [autonomousReversal_involutive] at ht
    exact h.comp_tendsto ht
  have he := viscousTransportedOperator_congr_germ (evolutionCoefficient a)
    (identityDrift 1) 0 hc
  rw [viscousTransportedOperator_zero, viscousTransportedOperator_zero] at he
  have hu := autonomous_generator_reversal a (u ∘ autonomousReversal) p
  have hv := autonomous_generator_reversal a (v ∘ autonomousReversal) p
  have hcomp (f : Point → ℝ) : (f ∘ autonomousReversal) ∘ autonomousReversal = f := by
    funext q
    simp only [Function.comp_apply, autonomousReversal_involutive]
  rw [hcomp] at hu hv
  exact hu.trans ((congrArg Neg.neg he).trans hv.symm)

/-- The actual full-space kernel action satisfies the source generator for bounded smooth data. -/
theorem fullSpaceAction_generator
    (hH : HormanderHypoellipticityStatement) {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (F : BoundedBorel (EvolutionAmbientState 1)) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (p : Point) (hp : 0 < p.time) : autonomousGeneratorResidual A.a (fullSpaceAction E F) p = 0 :=
    by
  obtain ⟨U, hr, hg, _⟩ := fullspace_bounded_smooth_generator hH hlam hLam A E hE F hF
  have he : fullSpaceAction E F =ᶠ[𝓝 p] U := by
    filter_upwards [(isOpen_lt continuous_const continuous_time).mem_nhds hp] with q hq
    rw [fullSpaceAction, dite_eq_left hq.le]
    exact (hr q hq.le).symm
  rw [autonomousGeneratorResidual_congr_germ A.a he]
  exact hg p hp

/-- Elapsed-time differentiation equals positive physical transport plus velocity diffusion. -/
theorem fullSpaceAction_timeDerivative
    (hH : HormanderHypoellipticityStatement) {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (F : BoundedBorel (EvolutionAmbientState 1)) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (p : Point) (hp : 0 < p.time) :
    deriv (fun t => fullSpaceAction E F ⟨t, p.position, p.velocity⟩) p.time =
      p.velocity 0 * kineticPositionGradient (fullSpaceAction E F) p 0 +
        A.a (p.position 0) (p.velocity 0) *
          kineticVelocityHessian (fullSpaceAction E F) p 0 0 := by
  have h := fullSpaceAction_generator hH hlam hLam A E hE F hF p hp
  unfold autonomousGeneratorResidual kineticTimeDerivative at h
  linarith

/-- Position reflection of the actual action satisfies `dt + v dx - a(-x,v) dvv = 0`. -/
theorem fullSpaceAction_positionReflection
    (hH : HormanderHypoellipticityStatement) {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (F : BoundedBorel (EvolutionAmbientState 1)) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (p : Point) (hp : 0 < p.time) :
    autonomousScalarOperator (reflectedAutonomous A.a)
      (fullSpaceAction E F ∘ autonomousPositionReflection) p = 0 := by
  rw [autonomous_generator_positionReflection]
  exact fullSpaceAction_generator hH hlam hLam A E hE F hF _ hp

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
