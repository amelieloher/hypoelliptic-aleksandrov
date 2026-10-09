module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitFunctionalProbes
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonLinear

/-! # Linear homogeneous values of smooth exit probes -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic
open SectionTwo TheoremA Evolution
open scoped Topology

/-- The actual scalar kinetic source of a probe, as bounded Borel data. -/
def exitProbeOperatorDatum {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (f : exitProbeSubmodule) : BoundedBorel Point :=
  ⟨forwardScalarOperator A.a (exitProbePhysical f), by
    have hm := (exitProbe_operator_smooth_compact A f).1.continuous.measurable.comp
      reconstructionPhysicalHomeomorph.symm.continuous.measurable
    have heq : forwardScalarOperator A.a (exitProbePhysical f) =
        transportedOperator (evolutionCoefficient A.a) (identityDrift 1) f.1 ∘
          reconstructionPhysicalHomeomorph.symm := funext (exitProbePhysical_operator A f)
    rw [heq]
    exact hm, by
    obtain ⟨M, hM⟩ := exitProbePhysical_bounded_source A f
    exact ⟨max M 0, le_max_right _ _, fun p => (hM p).2.trans (le_max_left _ _)⟩⟩

/-- The homogeneous value is the actual test value plus its actual kinetic-source integral. -/
def exitProbeValue {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (H : Interval)
    (E : StripEvolution H) (T : ℝ) (e : StripPole H (T : WithTop ℝ))
    (f : exitProbeSubmodule) : ℝ :=
  exitProbePhysical f e.1 + ∫ p, forwardScalarOperator A.a (exitProbePhysical f) p
    ∂stripGreenOfKernel H E.2 T e

private theorem probe_operator_add {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (f g : exitProbeSubmodule) :
    forwardScalarOperator A.a (exitProbePhysical (f + g)) =
      fun p => forwardScalarOperator A.a (exitProbePhysical f) p +
        forwardScalarOperator A.a (exitProbePhysical g) p := by
  funext p
  have h := comparison_forwardOperator_add
    (exitProbePhysical_isKineticC112On f univ isOpen_univ)
    (exitProbePhysical_isKineticC112On g univ isOpen_univ) (autonomousCoefficient A.a) (mem_univ p)
  simp only [forwardOperator_autonomous] at h
  exact h

private theorem probe_operator_smul {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (c : ℝ) (f : exitProbeSubmodule) :
    forwardScalarOperator A.a (exitProbePhysical (c • f)) =
      fun p => c * forwardScalarOperator A.a (exitProbePhysical f) p := by
  funext p
  have h := comparison_forwardOperator_const_mul
    (exitProbePhysical_isKineticC112On f univ isOpen_univ) c (autonomousCoefficient A.a)
      (mem_univ p)
  simp only [forwardOperator_autonomous] at h
  exact h

/-- Homogeneous probe values form a linear functional before boundary restriction. -/
def exitProbeValueLinear {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (H : Interval)
    (E : StripEvolution H) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    exitProbeSubmodule →ₗ[ℝ] ℝ where
  toFun := exitProbeValue A H E T e
  map_add' f g := by
    unfold exitProbeValue
    rw [probe_operator_add]
    have hf : Integrable (forwardScalarOperator A.a (exitProbePhysical f))
        (stripGreenOfKernel H E.2 T e) :=
      stripGreen_integrable_boundedBorel H E.2 T e (exitProbeOperatorDatum A f)
    have hg : Integrable (forwardScalarOperator A.a (exitProbePhysical g))
        (stripGreenOfKernel H E.2 T e) :=
      stripGreen_integrable_boundedBorel H E.2 T e (exitProbeOperatorDatum A g)
    rw [integral_add hf hg]
    change exitProbePhysical f e.1 + exitProbePhysical g e.1 + _ = _
    ring
  map_smul' c f := by
    unfold exitProbeValue
    rw [probe_operator_smul, integral_const_mul]
    change c * exitProbePhysical f e.1 + _ = c * _
    ring

/-- Boundary order bounds the actual homogeneous value of each smooth compact probe. -/
theorem exitProbeValue_le_of_boundary
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ))
    (f : exitProbeSubmodule) (c : ℝ)
    (hbd : ∀ p ∈ stripClosedExit H T, exitProbePhysical f p ≤ c) :
    exitProbeValue A H E T e f ≤ c := by
  obtain ⟨M, hM⟩ := exitProbePhysical_bounded_source A f
  have h := reconstruction_boundary_comparison hH hlam hLam A H E hE
    (e.1.time - 1) T e (by linarith) (exitProbePhysical f)
    (exitProbePhysical_isKineticC112On f _ (isOpen_reconstructionStrip H _ T))
    (exitProbePhysical_continuous_compact f).1
    ⟨M, fun p _ => hM p⟩ M (fun p => (hM p).1) c hbd
  simpa only [exitProbeValue, integral_neg, sub_neg_eq_add] using h

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
