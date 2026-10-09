module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TerminalMomentBoundsKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FourthMomentsPolynomials
import Mathlib.Tactic

/-! # Regularity of the concrete polynomial supersolutions in evolution coordinates -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic

/-- Raw coordinate smoothness of the quadratic velocity barrier. -/
theorem velocitySecondBarrier_raw_smooth (Lam v0 tau : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (rawLift (velocitySecondBarrier Lam v0 tau ∘ terminalPhysicalPoint)) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × (PDE.Vec 1 × PDE.Vec 1) =>
    (q.2.1 0-v0)^2+2*Lam*(tau-q.1))
  fun_prop

/-- Raw coordinate smoothness of the quadratic position barrier. -/
theorem positionSecondBarrier_raw_smooth (Lam X0 tau : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (rawLift (positionSecondBarrier Lam X0 tau ∘ terminalPhysicalPoint)) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × (PDE.Vec 1 × PDE.Vec 1) =>
    (q.2.2 0-X0+(tau-q.1)*q.2.1 0)^2+(2/3:ℝ)*Lam*(tau-q.1)^3)
  fun_prop

/-- Raw coordinate smoothness of the quartic velocity barrier. -/
theorem velocityFourthBarrier_raw_smooth (Lam v0 tau : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (rawLift (velocityFourthBarrier Lam v0 tau ∘ terminalPhysicalPoint)) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × (PDE.Vec 1 × PDE.Vec 1) =>
    (q.2.1 0-v0)^4+12*Lam*(tau-q.1)*(q.2.1 0-v0)^2+
      12*Lam^2*(tau-q.1)^2)
  fun_prop

/-- Raw coordinate smoothness of the quartic position barrier. -/
theorem positionFourthBarrier_raw_smooth (Lam X0 tau : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (rawLift (positionFourthBarrier Lam X0 tau ∘ terminalPhysicalPoint)) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × (PDE.Vec 1 × PDE.Vec 1) =>
    (q.2.2 0-X0+(tau-q.1)*q.2.1 0)^4+
      4*Lam*(tau-q.1)^3*(q.2.2 0-X0+(tau-q.1)*q.2.1 0)^2+
      (4/3:ℝ)*Lam^2*(tau-q.1)^6)
  fun_prop

/-- Raw smoothness supplies global continuity on the native point carrier. -/
theorem terminal_raw_continuous (W : Point → ℝ)
    (hW : ContDiff ℝ (⊤ : ℕ∞) (rawLift W)) : Continuous W := by
  exact hW.continuous.comp (KineticPoint.homeomorphProd 1).continuous_toFun

/-- Raw smoothness supplies all comparison slices. -/
theorem terminal_raw_regular (W : Point → ℝ)
    (hW : ContDiff ℝ (⊤ : ℕ∞) (rawLift W)) (p : Point) : IsSliceRegularAt W p := by
  apply IsSliceRegularAt.of_contDiffAt
  exact (hW.of_le (by norm_num)).contDiffAt

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
