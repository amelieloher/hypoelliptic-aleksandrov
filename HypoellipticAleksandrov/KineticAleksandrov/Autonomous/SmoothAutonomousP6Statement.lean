module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Setting
public import HypoellipticAleksandrov.KineticAleksandrov.Operator
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Setting

/-! # The preliminary autonomous p-six hypothesis

This is exactly the statement body of PLAN-AUTONOMOUS section 62, not its proof.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open MeasureTheory

/-- The preliminary comparison constant is chosen before the coefficient and solution. -/
def SmoothAutonomousP6Statement (lam Lam : ℝ) : Prop :=
  ∃ C_A : ℝ, 0 < C_A ∧ ∀ (A : SmoothAutonomous lam Lam)
    (O : Set Point) (_hO : IsOpen O) (u : Point → ℝ),
    Parabolic.IsKineticC112On u O →
    (∀ᵐ p ∂volume.restrict O, autonomousScalarOperator A.a u p = 0) →
    Holder.IsAdmissibleSolution (autonomousCoefficient A.a) O 6 C_A u

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
