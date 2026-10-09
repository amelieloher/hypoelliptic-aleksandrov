module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FullSpaceIdentification
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! # Time translation of the autonomous classical equation -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

/-- Translate time while keeping physical position and velocity fixed. -/
def autonomousTimeShift (h : ℝ) (p : KineticPoint 1) : KineticPoint 1 :=
  ⟨p.time + h, p.position, p.velocity⟩

/-- The time translation is continuous. -/
theorem continuous_autonomousTimeShift (h : ℝ) : Continuous (autonomousTimeShift h) :=
  KineticPoint.continuous_mk (continuous_time.add continuous_const)
    continuous_position continuous_velocity

/-- The forward autonomous operator commutes with time translation. -/
theorem autonomous_operator_timeShift (a : ℝ → ℝ → ℝ) (h : ℝ)
    (u : KineticPoint 1 → ℝ) (p : KineticPoint 1) :
    transportedForwardOperator (evolutionCoefficient a) (identityDrift 1)
      (fun q => u (autonomousTimeShift h q)) p =
    transportedForwardOperator (evolutionCoefficient a) (identityDrift 1) u
      (autonomousTimeShift h p) := by
  rw [transportedForwardOperator_apply, transportedForwardOperator_apply]
  have ht : kineticTimeDerivative (fun q => u (autonomousTimeShift h q)) p =
      kineticTimeDerivative u (autonomousTimeShift h p) :=
    deriv_comp_add_const (fun r => u ⟨r, p.position, p.velocity⟩) h p.time
  rw [ht]
  rfl

/-- Time translation carries an actual full-space terminal solution to an actual solution. -/
theorem fullspace_classical_timeShift {a : ℝ → ℝ → ℝ} (h τ : ℝ)
    (F : BoundedBorel (EvolutionAmbientState 1)) (u : KineticPoint 1 → ℝ)
    (hu : IsClassicalTerminalSolution autonomousWholeDomain (fun _ => 0)
      (evolutionCoefficient a) (identityDrift 1) (τ + h) F u) :
    IsClassicalTerminalSolution autonomousWholeDomain (fun _ => 0)
      (evolutionCoefficient a) (identityDrift 1) τ F
      (fun p => u (autonomousTimeShift h p)) := by
  have hd (t : ℝ) : movingDomain autonomousWholeDomain (fun _ => 0) t = univ :=
    movingDomain_wholeSpace 1 t
  have hclosed (p : KineticPoint 1)
      (hp : p ∈ evolutionPastClosedCylinder autonomousWholeDomain (fun _ => 0) τ) :
      autonomousTimeShift h p ∈
        evolutionPastClosedCylinder autonomousWholeDomain (fun _ => 0) (τ + h) :=
    ⟨by change p.time + h ≤ τ + h; linarith [hp.1], by rw [hd, closure_univ]; trivial⟩
  obtain ⟨⟨C, hC0, hC⟩, hc, hs, hop, ht, _⟩ := hu
  refine ⟨⟨C, hC0, fun p hp => hC _ (hclosed p hp)⟩,
    hc.comp (continuous_autonomousTimeShift h).continuousOn hclosed, ?_, ?_, ?_, ?_⟩
  · exact hs.comp ((contDiff_fst.add contDiff_const).prodMk contDiff_snd).contDiffOn
      (fun q hq => ⟨by change q.1 + h < τ + h; linarith [hq.1], by rw [hd]; trivial⟩)
  · intro p hp
    rw [autonomous_operator_timeShift]
    exact hop _ ⟨by change p.time + h < τ + h; linarith [hp.1], by rw [hd]; trivial⟩
  · intro p hp
    exact ht _ ⟨congrArg (fun r : ℝ => r + h) hp.1,
      by rw [hd, closure_univ]; trivial⟩
  · intro p hp
    have hf := hp.2
    rw [hd, frontier_univ] at hf
    exact False.elim hf

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
