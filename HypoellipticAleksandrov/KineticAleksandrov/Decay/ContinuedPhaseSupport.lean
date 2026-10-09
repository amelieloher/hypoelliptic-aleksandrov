module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.SourceNotation
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.ContinuationMeasure
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-! # Addition of source and continuation phase errors -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open Set MeasureTheory

/-- Changing the transported base point splits the phase coordinate additively. -/
theorem phaseCoordinate_split {d : ℕ} (ξ z0 : PDE.Vec d)
    (x y : EvolutionAmbientState d) :
    phaseCoordinate ξ z0 x = phaseCoordinate ξ z0 y + phaseCoordinate ξ y.2 x := by
  unfold phaseCoordinate PDE.vecDot
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Pi.sub_apply]
  ring

/-- Source and conditional continuation phase errors add under kernel integration. -/
theorem continuation_phase_support {d : ℕ} {α : Type*} [MeasurableSpace α]
    (sourceState : α → EvolutionAmbientState d) (hsource : Measurable sourceState)
    (ξ z0 : PDE.Vec d) (a c e1 e2 : ℝ)
    (R : Measure α) [IsFiniteMeasure R]
    (κ : ProbabilityTheory.Kernel α (EvolutionAmbientState d))
    (hR : ∀ᵐ p ∂R, |phaseCoordinate ξ z0 (sourceState p) - a| ≤ e1)
    (hκ : ∀ᵐ p ∂R, ∀ᵐ x ∂κ p, |phaseCoordinate ξ (sourceState p).2 x - c| ≤ e2)
    (E : Measure (EvolutionAmbientState d))
    (hE : ∀ A, MeasurableSet A → E A = ∫⁻ p, κ p A ∂R) :
    ∀ᵐ x ∂E, |phaseCoordinate ξ z0 x - (a + c)| ≤ e1 + e2 := by
  have hmeas : MeasurableSet {x : EvolutionAmbientState d |
      ¬ |phaseCoordinate ξ z0 x - (a + c)| ≤ e1 + e2} := by
    have hq : Continuous (fun x : EvolutionAmbientState d =>
        |phaseCoordinate ξ z0 x - (a + c)|) := by
      unfold phaseCoordinate PDE.vecDot
      fun_prop
    exact (isClosed_le hq continuous_const).measurableSet.compl
  apply ae_iff.mpr
  rw [hE _ hmeas]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hR, hκ] with p hp hk
  apply ae_iff.mp
  filter_upwards [hk] with x hx
  have he : phaseCoordinate ξ z0 x - (a + c) =
      (phaseCoordinate ξ z0 (sourceState p) - a) +
      (phaseCoordinate ξ (sourceState p).2 x - c) := by
    rw [phaseCoordinate_split ξ z0 x (sourceState p)]
    ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hp hx)

end HypoellipticAleksandrov.KineticAleksandrov.Decay
