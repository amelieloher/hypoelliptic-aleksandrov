module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AlternatingGreenAlgebra

/-! # Alternating exit decomposition conditional on the pending AU-06 splits

The consumed kernels have the same physical domains as in `AlternatingGreen`.
AU-06 must supply the three literal nested exit identities used as premises.
Only the exits on the outer face contribute to the partial sum; internal exits
continue through the next entrance measure. No claim of analytic closure is made.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory
open scoped Classical

/-- Exit onto the outer face before the first entrance, with zero for an initial visit. -/
def visitInitialExit (P : Point) (I : Interval) (outer : Set Point)
    (exitWaiting : Kernel Point Point) : Measure Point :=
  if P.velocity 0 ∈ closure I.carrier then 0 else (exitWaiting P).restrict outer

/-- The finite alternating exit identity under the exact consumed AU-06 exit splits. -/
theorem alternating_exit_of_nested_splitting
    (P : Point) (I : Interval) (Sin Sout outer : Set Point)
    (exitActive exitWaiting exitOuter : Kernel Point Point)
    (hinitial : exitOuter P = visitInitialExit P I outer exitWaiting +
      exitOuter ∘ₘ visitGamma P I Sin Sout exitActive exitWaiting 0)
    (hactive : ∀ n,
      exitOuter ∘ₘ visitGamma P I Sin Sout exitActive exitWaiting n =
        (exitActive ∘ₘ visitGamma P I Sin Sout exitActive exitWaiting n).restrict outer +
          exitOuter ∘ₘ visitBeta P I Sin Sout exitActive exitWaiting n)
    (hwaiting : ∀ n,
      exitOuter ∘ₘ visitBeta P I Sin Sout exitActive exitWaiting n =
        (exitWaiting ∘ₘ visitBeta P I Sin Sout exitActive exitWaiting n).restrict outer +
          exitOuter ∘ₘ visitGamma P I Sin Sout exitActive exitWaiting (n + 1))
    (N : ℕ) :
    exitOuter P = visitInitialExit P I outer exitWaiting +
      ∑ n ∈ Finset.range N,
        ((exitActive ∘ₘ visitGamma P I Sin Sout exitActive exitWaiting n).restrict outer +
          (exitWaiting ∘ₘ visitBeta P I Sin Sout exitActive exitWaiting n).restrict outer) +
      exitOuter ∘ₘ visitGamma P I Sin Sout exitActive exitWaiting N := by
  apply alternating_measure_telescope _ _ _ _ hinitial
  intro n
  rw [hactive n, hwaiting n]
  ac_rfl

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
