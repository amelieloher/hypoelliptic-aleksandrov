module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyNorm

/-!
# Derivative-only parabolic Morrey norms

This module records the raw `L^(d + 1)` norms of the time derivative and
ordered velocity-Hessian components used on the right-hand side of parabolic
Morrey dyadic estimates.  It also proves that these raw norms cannot increase
under restriction when the corresponding global `MemLp` certificates are
available.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped BigOperators ENNReal

/-- The global raw `L^(d + 1)` norm of the time derivative and all ordered
velocity-Hessian components used by parabolic Morrey dyadic estimates. -/
noncomputable def parabolicMorreyDerivativeLpNorm (d : Nat)
    (u : TimeVelocity d -> Real) : Real :=
  parabolicLpNorm d (timeDerivative u) +
    ∑ i : Fin d, ∑ j : Fin d,
      parabolicLpNorm d (fun z => velocityHessian u z i j)

/-- The raw restricted counterpart of `parabolicMorreyDerivativeLpNorm`. -/
noncomputable def parabolicMorreyDerivativeLpNormOn (d : Nat)
    (u : TimeVelocity d -> Real) (Q : Set (TimeVelocity d)) : Real :=
  parabolicLpNormOn d (timeDerivative u) Q +
    ∑ i : Fin d, ∑ j : Fin d,
      parabolicLpNormOn d (fun z => velocityHessian u z i j) Q

/-- A globally `L^(d + 1)` scalar has no larger raw restricted norm. -/
theorem parabolicLpNormOn_le_parabolicLpNorm
    {d : Nat} (f : TimeVelocity d -> Real) (Q : Set (TimeVelocity d))
    (hf : MemLp f (parabolicExponent d) volume) :
    parabolicLpNormOn d f Q <= parabolicLpNorm d f := by
  unfold parabolicLpNormOn parabolicLpNorm parabolicELpNormOn parabolicELpNorm
  exact ENNReal.toReal_mono hf.eLpNorm_ne_top
    (eLpNorm_mono_measure f Measure.restrict_le_self)

/-- Under componentwise global selected-jet integrability, restricting the
time/Hessian Morrey right-hand side cannot increase it. -/
theorem parabolicMorreyDerivativeLpNormOn_le
    {d : Nat} (u : TimeVelocity d -> Real) (Q : Set (TimeVelocity d))
    (hu : ParabolicSmoothJetMemLp d u) :
    parabolicMorreyDerivativeLpNormOn d u Q <=
      parabolicMorreyDerivativeLpNorm d u := by
  unfold parabolicMorreyDerivativeLpNormOn parabolicMorreyDerivativeLpNorm
  refine add_le_add ?_ ?_
  · exact parabolicLpNormOn_le_parabolicLpNorm (timeDerivative u) Q hu.2.1
  · refine Finset.sum_le_sum fun i _ => ?_
    exact Finset.sum_le_sum fun j _ =>
      parabolicLpNormOn_le_parabolicLpNorm
        (fun z => velocityHessian u z i j) Q (hu.2.2.2 i j)

end HypoellipticAleksandrov.Parabolic
