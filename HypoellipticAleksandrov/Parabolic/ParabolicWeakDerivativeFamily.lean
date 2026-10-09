module

public import HypoellipticAleksandrov.Parabolic.ParabolicDerivativeIndex
public import HypoellipticAleksandrov.Parabolic.WeakDerivatives

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped ENNReal

/-- A coherent finite family of selected original-time weak derivatives
through parabolic weight `L`, all locally represented in `L²`. -/
structure ParabolicWeakDerivativeFamily
    (d L : ℕ) (U : Set (TimeVelocity d))
    (u : TimeVelocity d → ℝ) where
  /-- Selected raw representative for each bounded parabolic multi-index. -/
  representative :
    ParabolicDerivativeIndex d L → TimeVelocity d → ℝ

  /-- Every selected entry belongs to restricted-product-volume `L²`. -/
  memLp : ∀ beta : ParabolicDerivativeIndex d L,
    ParabolicMemLpOn U (2 : ℝ≥0∞) (representative beta)

  /-- The zero-index entry represents the supplied root function. -/
  zero_ae :
    representative (ParabolicDerivativeIndex.zero d L)
      =ᵐ[timeVelocityVolumeOn U] u

  /-- The selected time-successor entry is the original-time weak time
  derivative of the predecessor entry. -/
  hasWeakTimeSucc :
    ∀ (beta : ParabolicDerivativeIndex d L)
      (h : beta.1.parabolicWeight + 2 ≤ L),
      HasWeakTimeDerivOn U
        (representative beta)
        (representative (ParabolicDerivativeIndex.timeSucc beta h))

  /-- The selected velocity-successor entry is the weak derivative of the
  predecessor entry in the displayed velocity coordinate. -/
  hasWeakVelocitySucc :
    ∀ (beta : ParabolicDerivativeIndex d L) (i : Fin d)
      (h : beta.1.parabolicWeight + 1 ≤ L),
      HasWeakVelocityPartialDerivOn U i
        (representative beta)
        (representative (ParabolicDerivativeIndex.velocitySucc beta i h))

end HypoellipticAleksandrov.Parabolic
