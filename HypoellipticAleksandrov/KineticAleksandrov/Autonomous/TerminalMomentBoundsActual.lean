module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TerminalMomentBoundsTruncation
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TerminalMomentBoundsRegularity
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Tactic

/-! # Actual terminal moments of every realizing autonomous full-space kernel

Compact polynomial tests, epsilon-Lyapunov comparison and Fatou establish the
unbounded terminal moments without a diffusion realization or coefficient derivatives.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set MeasureTheory Filter
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal Topology

/-- The actual velocity terminal moment, with the polynomial's sharp start value. -/
theorem kernelXV_velocity_2_moment {lam Lam : ℝ} (hlam : 0 < lam)
    (A : SmoothAutonomous lam Lam) (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (z : Z) (T : NNReal) :
    (∫⁻ w, ENNReal.ofReal ((w.2-z.2)^2) ∂kernelXV E T z) ≤
      ENNReal.ofReal (2*Lam*(T : ℝ)) := by
  have hLam : 0 ≤ Lam := (hlam.le.trans (A.bounds 0 0).1).trans (A.bounds 0 0).2
  let W := velocitySecondBarrier Lam z.2 T ∘ terminalPhysicalPoint
  let g := fun x : EvolutionAmbientState 1 => (x.1 0-z.2)^2
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := by dsimp only [g]; fun_prop
  have hw := velocitySecondBarrier_raw_smooth Lam z.2 T
  have h := terminal_polynomial_lintegral_le hlam A E hE g hg
    (fun x => sq_nonneg _) W (terminal_raw_continuous W hw)
    (terminal_raw_regular W hw) T
    (fun p hp => velocitySecondBarrier_nonneg hLam z.2 T (terminalPhysicalPoint p) hp)
    (fun p hp => by
      rw [terminalPhysicalPoint_operator]
      exact velocitySecondBarrier_operator_nonpos A.a Lam z.2 T (terminalPhysicalPoint p)
        (A.bounds _ _).2)
    (fun p hp => by
      dsimp only [g, W, Function.comp_apply, terminalPhysicalPoint]
      rw [← hp]
      exact (velocitySecondBarrier_terminal Lam z.2 (terminalPhysicalPoint p)).symm)
    (wholeQuery T z) rfl
  rw [kernelXV, lintegral_map (by fun_prop) nativeToXV_measurable]
  simpa only [g, W, wholeQuery, wholeSpaceQuery, terminalPhysicalPoint,
    Function.comp_apply, nativeToXV, velocitySecondBarrier_start] using h

/-- The actual position terminal moment, with the polynomial's sharp start value. -/
theorem kernelXV_position_2_moment {lam Lam : ℝ} (hlam : 0 < lam)
    (A : SmoothAutonomous lam Lam) (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (z : Z) (T : NNReal) :
    (∫⁻ w, ENNReal.ofReal ((w.1-z.1)^2) ∂kernelXV E T z) ≤
      ENNReal.ofReal (z.2^2*(T : ℝ)^2+(2/3 : ℝ)*Lam*(T : ℝ)^3) := by
  have hLam : 0 ≤ Lam := (hlam.le.trans (A.bounds 0 0).1).trans (A.bounds 0 0).2
  let W := positionSecondBarrier Lam z.1 T ∘ terminalPhysicalPoint
  let g := fun x : EvolutionAmbientState 1 => (x.2 0-z.1)^2
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := by dsimp only [g]; fun_prop
  have hw := positionSecondBarrier_raw_smooth Lam z.1 T
  have h := terminal_polynomial_lintegral_le hlam A E hE g hg
    (fun x => sq_nonneg _) W (terminal_raw_continuous W hw)
    (terminal_raw_regular W hw) T
    (fun p hp => positionSecondBarrier_nonneg hLam z.1 T (terminalPhysicalPoint p) hp)
    (fun p hp => by
      rw [terminalPhysicalPoint_operator]
      exact positionSecondBarrier_operator_nonpos A.a Lam z.1 T (terminalPhysicalPoint p)
        (A.bounds _ _).2)
    (fun p hp => by
      dsimp only [g, W, Function.comp_apply, terminalPhysicalPoint]
      rw [← hp]
      exact (positionSecondBarrier_terminal Lam z.1 (terminalPhysicalPoint p)).symm)
    (wholeQuery T z) rfl
  rw [kernelXV, lintegral_map (by fun_prop) nativeToXV_measurable]
  simpa only [g, W, wholeQuery, wholeSpaceQuery, terminalPhysicalPoint,
    Function.comp_apply, nativeToXV, positionSecondBarrier_start] using h

/-- The actual velocity terminal moment, with the polynomial's sharp start value. -/
theorem kernelXV_velocity_4_moment {lam Lam : ℝ} (hlam : 0 < lam)
    (A : SmoothAutonomous lam Lam) (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (z : Z) (T : NNReal) :
    (∫⁻ w, ENNReal.ofReal ((w.2-z.2)^4) ∂kernelXV E T z) ≤
      ENNReal.ofReal (12*Lam^2*(T : ℝ)^2) := by
  have hLam : 0 ≤ Lam := (hlam.le.trans (A.bounds 0 0).1).trans (A.bounds 0 0).2
  let W := velocityFourthBarrier Lam z.2 T ∘ terminalPhysicalPoint
  let g := fun x : EvolutionAmbientState 1 => (x.1 0-z.2)^4
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := by dsimp only [g]; fun_prop
  have hw := velocityFourthBarrier_raw_smooth Lam z.2 T
  have h := terminal_polynomial_lintegral_le hlam A E hE g hg
    (fun x => by dsimp only [g]; positivity) W (terminal_raw_continuous W hw)
    (terminal_raw_regular W hw) T
    (fun p hp => velocityFourthBarrier_nonneg hLam z.2 T (terminalPhysicalPoint p) hp)
    (fun p hp => by
      rw [terminalPhysicalPoint_operator]
      exact velocityFourthBarrier_operator_nonpos A.a hLam z.2 T (terminalPhysicalPoint p) hp
        (A.bounds _ _).2)
    (fun p hp => by
      dsimp only [g, W, Function.comp_apply, terminalPhysicalPoint]
      rw [← hp]
      exact (velocityFourthBarrier_terminal Lam z.2 (terminalPhysicalPoint p)).symm)
    (wholeQuery T z) rfl
  rw [kernelXV, lintegral_map (by fun_prop) nativeToXV_measurable]
  simpa only [g, W, wholeQuery, wholeSpaceQuery, terminalPhysicalPoint,
    Function.comp_apply, nativeToXV, velocityFourthBarrier_start] using h

/-- The actual position terminal moment, with the polynomial's sharp start value. -/
theorem kernelXV_position_4_moment {lam Lam : ℝ} (hlam : 0 < lam)
    (A : SmoothAutonomous lam Lam) (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (z : Z) (T : NNReal) :
    (∫⁻ w, ENNReal.ofReal ((w.1-z.1)^4) ∂kernelXV E T z) ≤
      ENNReal.ofReal (z.2^4*(T : ℝ)^4+4*Lam*z.2^2*(T : ℝ)^5+
        (4/3 : ℝ)*Lam^2*(T : ℝ)^6) := by
  have hLam : 0 ≤ Lam := (hlam.le.trans (A.bounds 0 0).1).trans (A.bounds 0 0).2
  let W := positionFourthBarrier Lam z.1 T ∘ terminalPhysicalPoint
  let g := fun x : EvolutionAmbientState 1 => (x.2 0-z.1)^4
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := by dsimp only [g]; fun_prop
  have hw := positionFourthBarrier_raw_smooth Lam z.1 T
  have h := terminal_polynomial_lintegral_le hlam A E hE g hg
    (fun x => by dsimp only [g]; positivity) W (terminal_raw_continuous W hw)
    (terminal_raw_regular W hw) T
    (fun p hp => positionFourthBarrier_nonneg hLam z.1 T (terminalPhysicalPoint p) hp)
    (fun p hp => by
      rw [terminalPhysicalPoint_operator]
      exact positionFourthBarrier_operator_nonpos A.a hLam z.1 T (terminalPhysicalPoint p) hp
        (A.bounds _ _).2)
    (fun p hp => by
      dsimp only [g, W, Function.comp_apply, terminalPhysicalPoint]
      rw [← hp]
      exact (positionFourthBarrier_terminal Lam z.1 (terminalPhysicalPoint p)).symm)
    (wholeQuery T z) rfl
  rw [kernelXV, lintegral_map (by fun_prop) nativeToXV_measurable]
  simpa only [g, W, wholeQuery, wholeSpaceQuery, terminalPhysicalPoint,
    Function.comp_apply, nativeToXV, positionFourthBarrier_start] using h

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
