module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Green
public import HypoellipticAleksandrov.Parabolic.ScalarClassical
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Literal parabolic occupation-density characterization

These are the definitions used for the occupation estimate. Density existence and
finite norm estimates are separate proof steps.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal

/-- The stationary whole-space kinetic kernel underlying the parabolic marginal. -/
abbrev WholeKernel (d : ℕ) :=
  MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))

/-- The stationary whole-space terminal operator family. -/
abbrev WholeFamily (d : ℕ) :=
  TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d))

/-- The bounded-Borel characterization of the elapsed-time velocity density. -/
def IsOccupationDensity {d : ℕ} (K : WholeKernel d)
    (σ₀ T : ℝ) (ρ : Measure (PDE.Vec d)) (g : TimeVelocity d → ℝ) : Prop :=
  Measurable g ∧ (∀ q, 0 ≤ g q) ∧
    ∀ φ : BoundedBorel (TimeVelocity d),
      (∫ q, φ q * g q ∂volume.restrict (Ioo (0 : ℝ) T ×ˢ univ)) =
        ∫ v, ∫ τ : ElapsedTime (ENNReal.ofReal T),
          ∫ w, φ (τ.1, w) ∂K.firstMarginal
            (wholeSpaceQuery σ₀ (σ₀ + τ.1)
              (le_add_of_nonneg_right τ.2.1.le) v 0)
          ∂elapsedVolume (ENNReal.ofReal T) ∂ρ

/-- The unnormalised real-valued occupation norm; finite-norm results also assert `MemLp`. -/
def occupationLpNorm {d : ℕ} (T γ : ℝ) (g : TimeVelocity d → ℝ) : ℝ :=
  (eLpNorm g (ENNReal.ofReal γ)
    (volume.restrict (Ioo (0 : ℝ) T ×ˢ univ))).toReal

/-- The source parabolic scaling exponent. -/
def occupationBeta (d : ℕ) (γ : ℝ) : ℝ :=
  ((d : ℝ) + 2) / (2 * γ) - (d : ℝ) / 2

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
