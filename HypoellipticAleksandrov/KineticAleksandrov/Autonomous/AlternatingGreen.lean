module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AlternatingGreenAlgebra

/-! # Alternating Green decomposition conditional on the pending AU-06 splits

AU-06 must provide Borel physical Green/exit kernels for the active domain, the
possibly disconnected waiting domain, and the outer strip, extended by zero off
valid poles. It must prove the initial waiting split and the two nested-domain
identities below for the actual entrance and outgoing measures. Those analytic
identities are explicit premises of this distinctly named conditional theorem.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory
open scoped Classical

/-- Occupation before the first entrance; zero if the initial point is already inside. -/
def visitInitialGreen (P : Point) (I : Interval)
    (greenWaiting : Kernel Point Point) : Measure Point :=
  if P.velocity 0 ∈ closure I.carrier then 0 else greenWaiting P

/-- The finite alternating identity under the exact three consumed AU-06 Green splits.
Index `N` in the remainder is the source's entrance number `N + 1`. -/
theorem alternating_green_of_nested_splitting
    (P : Point) (I : Interval) (Sin Sout : Set Point)
    (exitActive exitWaiting greenActive greenWaiting greenOuter : Kernel Point Point)
    (hinitial : greenOuter P = visitInitialGreen P I greenWaiting +
      greenOuter ∘ₘ visitGamma P I Sin Sout exitActive exitWaiting 0)
    (hactive : ∀ n,
      greenOuter ∘ₘ visitGamma P I Sin Sout exitActive exitWaiting n =
        greenActive ∘ₘ visitGamma P I Sin Sout exitActive exitWaiting n +
          greenOuter ∘ₘ visitBeta P I Sin Sout exitActive exitWaiting n)
    (hwaiting : ∀ n,
      greenOuter ∘ₘ visitBeta P I Sin Sout exitActive exitWaiting n =
        greenWaiting ∘ₘ visitBeta P I Sin Sout exitActive exitWaiting n +
          greenOuter ∘ₘ visitGamma P I Sin Sout exitActive exitWaiting (n + 1))
    (N : ℕ) :
    greenOuter P = visitInitialGreen P I greenWaiting +
      ∑ n ∈ Finset.range N,
        (greenActive ∘ₘ visitGamma P I Sin Sout exitActive exitWaiting n +
          greenWaiting ∘ₘ visitBeta P I Sin Sout exitActive exitWaiting n) +
      greenOuter ∘ₘ visitGamma P I Sin Sout exitActive exitWaiting N := by
  apply alternating_measure_telescope _ _ _ _ hinitial
  intro n
  rw [hactive n, hwaiting n]
  ac_rfl

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
