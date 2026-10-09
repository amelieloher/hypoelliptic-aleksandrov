module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Conservation
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ScalarAdaptersCalculus
import Mathlib.Tactic

/-! # Physical terminal kernel and polynomial comparison

The kernel is the EV-14 master pushed to physical position and velocity.
Comparison uses the proved epsilon-Lyapunov bounded-cylinder argument.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set MeasureTheory Filter
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal Topology

/-- Physical scalar phase space, position followed by velocity. -/
abbrev Z := ℝ × ℝ

/-- Scalar projection from the evolution state. -/
def nativeToXV (q : EvolutionAmbientState 1) : Z := (q.2 0, q.1 0)

/-- Whole-space query starting at zero in physical scalar coordinates. -/
def wholeQuery (t : NNReal) (z : Z) : EvolutionQuery autonomousWholeDomain (fun _ => 0) :=
  wholeSpaceQuery 0 t t.property (fun _ => z.2) (fun _ => z.1)

/-- Physical kernel obtained by pushing the actual master measure forward. -/
def kernelXV (E : FullSpaceEvolution) (t : NNReal) (z : Z) : Measure Z :=
  (E.2.master (wholeQuery t z)).map nativeToXV

/-- Coordinate projection is measurable. -/
theorem nativeToXV_measurable : Measurable nativeToXV := by
  exact (measurable_pi_apply 0 |>.comp measurable_snd).prodMk
    (measurable_pi_apply 0 |>.comp measurable_fst)

/-- Scalar kernels have probability mass. -/
theorem kernelXV_mass_one {lam Lam : ℝ} (hlam : 0 < lam)
    (A : SmoothAutonomous lam Lam) (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (t : NNReal) (z : Z) : kernelXV E t z univ = 1 := by
  rw [kernelXV, Measure.map_apply nativeToXV_measurable MeasurableSet.univ,
    preimage_univ, fullspace_mass_one hlam A E hE]

/-- Exchange spatial fields, keeping terminal time. -/
def terminalPhysicalPoint (p : Point) : Point := ⟨p.time, p.velocity, p.position⟩

/-- Physical and evolution operators agree under the explicit spatial exchange. -/
theorem terminalPhysicalPoint_operator (a : ℝ → ℝ → ℝ) (W : Point → ℝ) (p : Point) :
    transportedForwardOperator (evolutionCoefficient a) (identityDrift 1)
      (W ∘ terminalPhysicalPoint) p = forwardScalarOperator a W (terminalPhysicalPoint p) := by
  rw [transportedForwardOperator_apply, forwardScalarOperator]
  simp only [matrixContraction, Fin.sum_univ_one, fullKineticCoefficientAt,
    evolutionCoefficient, PDE.vecDot, identityDrift]
  change kineticTimeDerivative W (terminalPhysicalPoint p) +
      a (p.velocity 0) (p.position 0) *
        kineticVelocityHessian W (terminalPhysicalPoint p) 0 0 +
      p.position 0 * kineticPositionGradient W (terminalPhysicalPoint p) 0 = _
  dsimp only [terminalPhysicalPoint]
  ring

/-- A nonnegative supersolution bounds compact-data classical terminal solutions.
The bounded-above difference uses the proved epsilon-Lyapunov comparison. -/
theorem terminal_polynomial_comparison {lam Lam : ℝ} (hlam : 0 < lam)
    (A : SmoothAutonomous lam Lam) (tau : ℝ)
    (F : BoundedBorel (EvolutionAmbientState 1)) (u W : Point → ℝ)
    (hu : IsClassicalTerminalSolution autonomousWholeDomain (fun _ => 0)
      (evolutionCoefficient A.a) (identityDrift 1) tau F u)
    (hc : Continuous W) (hr : ∀ p, IsSliceRegularAt W p)
    (hn : ∀ p, p.time ≤ tau → 0 ≤ W p)
    (hop : ∀ p, p.time ≤ tau →
      transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1) W p ≤ 0)
    (ht : ∀ p, p.time = tau → F (p.position, p.velocity) ≤ W p)
    (p0 : Point) (hp0 : p0.time ≤ tau) : u p0 ≤ W p0 := by
  have hΩ := isOpen_of_isAdmissibleEvolutionDomain autonomousWholeDomain_admissible
  have hs : ∀ p ∈ movingClosedSlab autonomousWholeDomain (fun _ => 0) p0.time tau,
      p ∈ evolutionPastClosedCylinder autonomousWholeDomain (fun _ => 0) tau :=
    fun _ hp => ⟨hp.2.1, hp.2.2⟩
  have hus := (isClassicalViscousTerminalSolution_zero_iff _ _ _ _ _ _ _).2 hu
  have hreg (p : Point) (hp : p ∈ movingActiveSlab autonomousWholeDomain
      (fun _ => 0) p0.time tau) : IsSliceRegularAt u p :=
    hus.isSliceRegularAt hΩ continuous_const ⟨hp.2.1, hp.2.2⟩
  obtain ⟨C, -, hC⟩ := hu.1
  have h := growth_comparison hΩ continuous_const hlam (evolutionCoefficient_bounds A)
    (identityDrift_bounds 1).1 (le_refl 0) zero_le_one
    (a := p0.time) (T := tau) (u := fun p => u p - W p)
    ⟨C, fun p hp => by
      have hb := hC p (hs p hp)
      have hh := hn p hp.2.1
      linarith [le_abs_self (u p)]⟩
    ((hu.2.1.mono hs).sub hc.continuousOn)
    (fun p hp => (hreg p hp).sub (hr p))
    (fun p hp => by
      rw [viscousTransportedOperator_sub (hreg p hp) (hr p),
        viscousTransportedOperator_zero, hu.2.2.2.1 p ⟨hp.2.1, hp.2.2⟩,
        viscousTransportedOperator_zero]
      linarith [hop p hp.2.1.le])
    (fun p hp htime => by
      rw [hu.2.2.2.2.1 p ⟨htime, by simpa only [← htime] using hp.2.2⟩]
      exact sub_nonpos.mpr (ht p htime))
    (fun p _ hf => by
      change p.position ∈ frontier (movingDomain (wholeSpace 1) (fun _ => 0) p.time) at hf
      rw [movingDomain_wholeSpace, frontier_univ] at hf
      exact False.elim hf)
  have hm : p0 ∈ movingClosedSlab autonomousWholeDomain (fun _ => 0) p0.time tau :=
    ⟨le_rfl, hp0, by
      change p0.position ∈ closure (movingDomain (wholeSpace 1) (fun _ => 0) p0.time)
      rw [movingDomain_wholeSpace, closure_univ]; trivial⟩
  exact sub_nonpos.mp (h p0 hm)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
