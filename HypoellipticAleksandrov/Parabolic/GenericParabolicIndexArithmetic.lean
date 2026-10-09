module

public import HypoellipticAleksandrov.Parabolic.ParabolicDerivativeIndex
public import HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndexLeibniz

/-!
# Generic parabolic-index arithmetic

This file provides bounded parabolic indices for source derivatives and for the
two sides of a multi-index split. It also embeds total-order derivative indices
into parabolic-weight derivative indices.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open scoped BigOperators

namespace TimeVelocityMultiIndex

/-- The right side of a split is coordinatewise bounded by the original index. -/
@[simp] theorem Split.right_le {d : ℕ} {beta : TimeVelocityMultiIndex d}
    (gamma : Split beta) : gamma.right ≤ beta := by
  intro c
  exact Nat.sub_le _ _

/-- The orders of the two sides of a split add to the order of the original index. -/
@[simp] theorem Split.order_left_add_order_right {d : ℕ}
    {beta : TimeVelocityMultiIndex d} (gamma : Split beta) :
    gamma.left.order + gamma.right.order = beta.order := by
  rw [← order_add, gamma.left_add_right]

/-- The parabolic weights of the two sides of a split add to the original weight. -/
@[simp] theorem Split.parabolicWeight_left_add_parabolicWeight_right {d : ℕ}
    {beta : TimeVelocityMultiIndex d} (gamma : Split beta) :
    gamma.left.parabolicWeight + gamma.right.parabolicWeight =
      beta.parabolicWeight := by
  rw [← parabolicWeight_add, gamma.left_add_right]

/-- The order of the left side of a split is bounded by the original order. -/
theorem Split.order_left_le {d : ℕ} {beta : TimeVelocityMultiIndex d}
    (gamma : Split beta) : gamma.left.order ≤ beta.order := by
  calc
    gamma.left.order ≤ gamma.left.order + gamma.right.order := Nat.le_add_right _ _
    _ = beta.order := gamma.order_left_add_order_right

/-- The order of the right side of a split is bounded by the original order. -/
theorem Split.order_right_le {d : ℕ} {beta : TimeVelocityMultiIndex d}
    (gamma : Split beta) : gamma.right.order ≤ beta.order := by
  calc
    gamma.right.order ≤ gamma.left.order + gamma.right.order := Nat.le_add_left _ _
    _ = beta.order := gamma.order_left_add_order_right

/-- The parabolic weight of the left side is bounded by the original weight. -/
theorem Split.parabolicWeight_left_le {d : ℕ}
    {beta : TimeVelocityMultiIndex d} (gamma : Split beta) :
    gamma.left.parabolicWeight ≤ beta.parabolicWeight := by
  calc
    gamma.left.parabolicWeight ≤
        gamma.left.parabolicWeight + gamma.right.parabolicWeight := Nat.le_add_right _ _
    _ = beta.parabolicWeight := gamma.parabolicWeight_left_add_parabolicWeight_right

/-- The parabolic weight of the right side is bounded by the original weight. -/
theorem Split.parabolicWeight_right_le {d : ℕ}
    {beta : TimeVelocityMultiIndex d} (gamma : Split beta) :
    gamma.right.parabolicWeight ≤ beta.parabolicWeight := by
  calc
    gamma.right.parabolicWeight ≤
        gamma.left.parabolicWeight + gamma.right.parabolicWeight := Nat.le_add_left _ _
    _ = beta.parabolicWeight := gamma.parabolicWeight_left_add_parabolicWeight_right

end TimeVelocityMultiIndex

namespace ParabolicDerivativeIndex

/-- Lower the ambient weight bound using a proof of the sharper actual bound. -/
def restrictLE {d L M : ℕ} (beta : ParabolicDerivativeIndex d L)
    (hbeta : beta.1.parabolicWeight ≤ M) : ParabolicDerivativeIndex d M :=
  ⟨beta.1, hbeta⟩

/-- Restricting the ambient bound does not change the underlying multi-index. -/
@[simp] theorem coe_restrictLE {d L M : ℕ}
    (beta : ParabolicDerivativeIndex d L)
    (hbeta : beta.1.parabolicWeight ≤ M) :
    (restrictLE beta hbeta).1 = beta.1 := rfl

/-- Restriction followed by inclusion recovers the original bounded index. -/
@[simp] theorem castLE_restrictLE {d L M : ℕ} (hML : M ≤ L)
    (beta : ParabolicDerivativeIndex d L)
    (hbeta : beta.1.parabolicWeight ≤ M) :
    castLE hML (restrictLE beta hbeta) = beta := rfl

/-- Include a source index of bound `L - 2` into the target bound `L`. -/
def sourceCast {d L : ℕ} (beta : ParabolicDerivativeIndex d (L - 2)) :
    ParabolicDerivativeIndex d L := castLE (Nat.sub_le L 2) beta

/-- Add one time derivative to a source index. -/
def sourceTime {d L : ℕ} (hL : 2 ≤ L)
    (beta : ParabolicDerivativeIndex d (L - 2)) : ParabolicDerivativeIndex d L :=
  timeSucc (sourceCast beta) (by
    change beta.1.parabolicWeight + 2 ≤ L
    omega)

/-- Add one velocity derivative to a source index. -/
def sourceVelocity {d L : ℕ} (hL : 2 ≤ L)
    (beta : ParabolicDerivativeIndex d (L - 2)) (i : Fin d) :
    ParabolicDerivativeIndex d L :=
  velocitySucc (sourceCast beta) i (by
    change beta.1.parabolicWeight + 1 ≤ L
    omega)

/-- Add the ordered pair of velocity derivatives `j`, then `i`, to a source index. -/
def sourceVelocityTwo {d L : ℕ} (hL : 2 ≤ L)
    (beta : ParabolicDerivativeIndex d (L - 2)) (j i : Fin d) :
    ParabolicDerivativeIndex d L :=
  ⟨beta.1 + Pi.single (velocityCoord j) 1 + Pi.single (velocityCoord i) 1, by
    simp only [TimeVelocityMultiIndex.parabolicWeight_add,
      TimeVelocityMultiIndex.parabolicWeight_single_velocity]
    omega⟩

/-- `sourceCast` preserves the underlying multi-index. -/
@[simp] theorem coe_sourceCast {d L : ℕ}
    (beta : ParabolicDerivativeIndex d (L - 2)) :
    (sourceCast beta).1 = beta.1 := rfl

/-- The underlying index of `sourceTime` is the source plus the time unit index. -/
@[simp] theorem coe_sourceTime {d L : ℕ} (hL : 2 ≤ L)
    (beta : ParabolicDerivativeIndex d (L - 2)) :
    (sourceTime hL beta).1 = beta.1 + Pi.single (timeCoord d) 1 := by
  classical
  funext c
  rcases c with _ | i
  · simp [sourceTime, sourceCast, timeSucc, TimeVelocityMultiIndex.ofTimeVelocity,
      TimeVelocityMultiIndex.timeOrder, timeCoord]
  · simp [sourceTime, sourceCast, timeSucc, TimeVelocityMultiIndex.ofTimeVelocity,
      TimeVelocityMultiIndex.velocity, timeCoord, velocityCoord]

/-- The underlying index of `sourceVelocity` is the source plus a velocity unit index. -/
@[simp] theorem coe_sourceVelocity {d L : ℕ} (hL : 2 ≤ L)
    (beta : ParabolicDerivativeIndex d (L - 2)) (i : Fin d) :
    (sourceVelocity hL beta i).1 = beta.1 + Pi.single (velocityCoord i) 1 := by
  classical
  funext c
  rcases c with _ | j
  · simp [sourceVelocity, sourceCast, velocitySucc, TimeVelocityMultiIndex.ofTimeVelocity,
      TimeVelocityMultiIndex.timeOrder, timeCoord, velocityCoord]
  · by_cases hji : j = i
    · subst j
      simp [sourceVelocity, sourceCast, velocitySucc,
        TimeVelocityMultiIndex.ofTimeVelocity, TimeVelocityMultiIndex.velocity,
        velocityCoord]
    · simp [sourceVelocity, sourceCast, velocitySucc,
        TimeVelocityMultiIndex.ofTimeVelocity, TimeVelocityMultiIndex.velocity,
        velocityCoord, hji]

/-- The underlying index of `sourceVelocityTwo` has the fixed ordered pair of additions. -/
@[simp] theorem coe_sourceVelocityTwo {d L : ℕ} (hL : 2 ≤ L)
    (beta : ParabolicDerivativeIndex d (L - 2)) (j i : Fin d) :
    (sourceVelocityTwo hL beta j i).1 =
      beta.1 + Pi.single (velocityCoord j) 1 +
        Pi.single (velocityCoord i) 1 := rfl

/-- Regard the left side of a split as a bounded parabolic derivative index. -/
def splitLeft {d L : ℕ} (beta : ParabolicDerivativeIndex d L)
    (gamma : TimeVelocityMultiIndex.Split beta.1) :
    ParabolicDerivativeIndex d L :=
  ⟨gamma.left, gamma.parabolicWeight_left_le.trans beta.2⟩

/-- Regard the right side of a split as a bounded parabolic derivative index. -/
def splitRight {d L : ℕ} (beta : ParabolicDerivativeIndex d L)
    (gamma : TimeVelocityMultiIndex.Split beta.1) :
    ParabolicDerivativeIndex d L :=
  ⟨gamma.right, gamma.parabolicWeight_right_le.trans beta.2⟩

/-- `splitLeft` has the left split index as its underlying multi-index. -/
@[simp] theorem coe_splitLeft {d L : ℕ} (beta : ParabolicDerivativeIndex d L)
    (gamma : TimeVelocityMultiIndex.Split beta.1) :
    (splitLeft beta gamma).1 = gamma.left := rfl

/-- `splitRight` has the right split index as its underlying multi-index. -/
@[simp] theorem coe_splitRight {d L : ℕ} (beta : ParabolicDerivativeIndex d L)
    (gamma : TimeVelocityMultiIndex.Split beta.1) :
    (splitRight beta gamma).1 = gamma.right := rfl

end ParabolicDerivativeIndex

namespace TimeVelocityDerivativeIndex

/-- Embed a total-order index of bound `m` into parabolic-weight bound `2 * m`. -/
def toParabolic {d m : ℕ} (beta : TimeVelocityDerivativeIndex d m) :
    ParabolicDerivativeIndex d (2 * m) :=
  ⟨beta.1, beta.1.parabolicWeight_le_two_mul beta.2⟩

/-- `toParabolic` preserves the underlying multi-index. -/
@[simp] theorem coe_toParabolic {d m : ℕ}
    (beta : TimeVelocityDerivativeIndex d m) :
    (toParabolic beta).1 = beta.1 := rfl

/-- `toParabolic` sends the zero total-order index to the zero parabolic index. -/
@[simp] theorem toParabolic_zero (d m : ℕ) :
    toParabolic (TimeVelocityDerivativeIndex.zero d m) =
      ParabolicDerivativeIndex.zero d (2 * m) := rfl

/-- `toParabolic` commutes with enlarging the ambient total-order bound. -/
@[simp] theorem toParabolic_castLE {d m n : ℕ} (hmn : m ≤ n)
    (beta : TimeVelocityDerivativeIndex d m) :
    toParabolic (castLE hmn beta) =
      ParabolicDerivativeIndex.castLE
        (Nat.mul_le_mul_left 2 hmn) (toParabolic beta) := rfl

end TimeVelocityDerivativeIndex

end HypoellipticAleksandrov.Parabolic
