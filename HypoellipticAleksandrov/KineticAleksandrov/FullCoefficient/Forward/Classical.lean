module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Forward.Operator
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Realization

/-!
# Classical solutions with zero terminal datum vanish

A terminal solution family satisfying the realization clauses has a unique classical solution
for each smooth compactly supported datum.  For the zero datum the zero function is a classical
solution, so every classical solution with zero datum vanishes on the closed past cylinder.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open Set

variable {d : ℕ}

/-- The transported operator annihilates the zero function. -/
theorem transportedForwardOperator_zero (B : FullKineticCoefficient d)
    (b : PDE.Vec d → PDE.Vec d) (p : KineticPoint d) :
    transportedForwardOperator B b (fun _ => (0 : ℝ)) p = 0 := by
  obtain ⟨t, a, z⟩ := p
  have := transportedForwardOperator_eq_forwardRepr B b (fun _ => (0 : ℝ)) isOpen_univ
    contDiffOn_const (t, (a, z)) trivial
  rw [this]
  have hraw : rawOf (fun _ : KineticPoint d => (0 : ℝ)) = fun _ => 0 := rfl
  have h0 : ∀ j, jointVelocityPartial j (fun _ : ℝ × EvolutionAmbientState d => (0 : ℝ)) =
      fun _ => 0 := by
    intro j
    funext q
    simp [jointVelocityPartial]
  simp [hraw, h0, forwardRepr, jointTimePartial, jointVelocityPartial, jointPositionPartial]

/-- The zero function is a classical terminal solution with zero datum. -/
theorem isClassicalTerminalSolution_zero (Ω : Set (PDE.Vec d)) (γ : ℝ → PDE.Vec d)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d) (T : ℝ) :
    IsClassicalTerminalSolution Ω γ B b T (0 : BoundedBorel (EvolutionAmbientState d))
      (fun _ => 0) := by
  refine ⟨⟨0, le_rfl, fun p _ => by simp⟩, continuousOn_const, contDiffOn_const,
    fun p _ => transportedForwardOperator_zero B b p, ?_, ?_⟩
  · intro p _
    simp [BoundedBorel.zero_apply]
  · intro p _
    rfl

/-- The zero terminal datum is smooth with compact support. -/
theorem isSmoothCompactTerminalDatum_zero (Ω : Set (PDE.Vec d)) (γ : ℝ → PDE.Vec d) (T : ℝ) :
    IsSmoothCompactTerminalDatum Ω γ T (0 : BoundedBorel (EvolutionAmbientState d)) := by
  have h : ((0 : BoundedBorel (EvolutionAmbientState d)) : EvolutionAmbientState d → ℝ) =
      fun _ => 0 := funext fun x => BoundedBorel.zero_apply x
  rw [IsSmoothCompactTerminalDatum, h]
  refine ⟨contDiff_const, HasCompactSupport.zero, ?_⟩
  simp

/-- Every classical solution with zero terminal datum vanishes on the closed past cylinder. -/
theorem classicalSolution_zero_datum_eq_zero {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    {hΩ : MeasurableSet Ω} {B : FullKineticCoefficient d} {b : PDE.Vec d → PDE.Vec d}
    {S : TerminalOperatorFamily Ω γ} {K : MovingFiberKernel Ω γ}
    (hreal : SectionTwo.RealizesTerminalEvolution Ω γ hΩ B b S K) (T : ℝ)
    {U : KineticPoint d → ℝ}
    (hU : IsClassicalTerminalSolution Ω γ B b T (0 : BoundedBorel (EvolutionAmbientState d)) U)
    {p : KineticPoint d} (hp : p ∈ evolutionPastClosedCylinder Ω γ T) : U p = 0 := by
  obtain ⟨u, _, _, huniq⟩ := hreal.1 T 0 (isSmoothCompactTerminalDatum_zero Ω γ T)
  exact (huniq U hU hp).trans ((huniq _ (isClassicalTerminalSolution_zero Ω γ B b T) hp).symm)

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
