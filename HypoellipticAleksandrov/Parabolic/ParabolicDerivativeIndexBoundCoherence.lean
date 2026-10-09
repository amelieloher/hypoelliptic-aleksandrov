module

public import HypoellipticAleksandrov.Parabolic.ParabolicDerivativeIndex

/-!
# Bound coherence for parabolic derivative indices

This file records that enlarging the parabolic-weight bound preserves the
underlying index and commutes with the fixed-bound successor operations.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic.ParabolicDerivativeIndex

/-- Enlarging the parabolic bound preserves the zero index exactly. -/
@[simp] theorem castLE_zero
    {d M L : ℕ} (hML : M ≤ L) :
    castLE hML (zero d M) = zero d L := by
  apply Subtype.ext
  rfl

/-- Enlarging the parabolic bound commutes with a fixed-bound time
successor. -/
@[simp] theorem castLE_timeSucc
    {d M L : ℕ} (hML : M ≤ L)
    (beta : ParabolicDerivativeIndex d M)
    (h : beta.1.parabolicWeight + 2 ≤ M) :
    castLE hML (timeSucc beta h) =
      timeSucc (castLE hML beta) (h.trans hML) := by
  apply Subtype.ext
  rfl

/-- Enlarging the parabolic bound commutes with a fixed-bound velocity
successor. -/
@[simp] theorem castLE_velocitySucc
    {d M L : ℕ} (hML : M ≤ L)
    (beta : ParabolicDerivativeIndex d M) (i : Fin d)
    (h : beta.1.parabolicWeight + 1 ≤ M) :
    castLE hML (velocitySucc beta i h) =
      velocitySucc (castLE hML beta) i (h.trans hML) := by
  apply Subtype.ext
  rfl

end HypoellipticAleksandrov.Parabolic.ParabolicDerivativeIndex
