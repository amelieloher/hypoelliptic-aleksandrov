module

public import HypoellipticAleksandrov.Parabolic.GenericParabolicIndexArithmetic
public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyLocality

/-!
# Ordinary weak-derivative-family view

This file selects the ordinary total-order portion of a parabolic weak-derivative
family and transports its time and velocity successor relations.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped ENNReal

namespace TimeVelocityDerivativeIndex

/-- Add one time derivative while remaining at the ordinary order bound. -/
def timeSucc {d m : ℕ} (beta : TimeVelocityDerivativeIndex d m)
    (h : beta.1.order + 1 ≤ m) : TimeVelocityDerivativeIndex d m :=
  ⟨TimeVelocityMultiIndex.ofTimeVelocity
      (beta.1.timeOrder + 1) beta.1.velocity, by
    change beta.1.timeOrder + 1 + beta.1.velocity.order ≤ m
    change beta.1.timeOrder + beta.1.velocity.order + 1 ≤ m at h
    omega⟩

/-- Add one velocity derivative while remaining at the ordinary order bound. -/
def velocitySucc {d m : ℕ} (beta : TimeVelocityDerivativeIndex d m)
    (i : Fin d) (h : beta.1.order + 1 ≤ m) :
    TimeVelocityDerivativeIndex d m :=
  ⟨TimeVelocityMultiIndex.ofTimeVelocity beta.1.timeOrder
      (Function.update beta.1.velocity i (beta.1.velocity i + 1)), by
    have hs :
        (∑ j, Function.update beta.1.velocity i
            (beta.1.velocity i + 1) j) =
          (∑ j, beta.1.velocity j) + 1 := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ i),
        Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i)]
      omega
    change beta.1.timeOrder +
      (∑ j, Function.update beta.1.velocity i
        (beta.1.velocity i + 1) j) ≤ m
    change beta.1.timeOrder + (∑ j, beta.1.velocity j) + 1 ≤ m at h
    omega⟩

/-- The time successor has the expected underlying time--velocity multi-index. -/
@[simp] theorem coe_timeSucc {d m : ℕ}
    (beta : TimeVelocityDerivativeIndex d m)
    (h : beta.1.order + 1 ≤ m) :
    (timeSucc beta h).1 =
      TimeVelocityMultiIndex.ofTimeVelocity
        (beta.1.timeOrder + 1) beta.1.velocity := rfl

/-- The velocity successor has the expected underlying time--velocity multi-index. -/
@[simp] theorem coe_velocitySucc {d m : ℕ}
    (beta : TimeVelocityDerivativeIndex d m) (i : Fin d)
    (h : beta.1.order + 1 ≤ m) :
    (velocitySucc beta i h).1 =
      TimeVelocityMultiIndex.ofTimeVelocity beta.1.timeOrder
        (Function.update beta.1.velocity i
          (beta.1.velocity i + 1)) := rfl

/-- The ordinary-to-parabolic embedding commutes with the time successor. -/
theorem toParabolic_timeSucc {d m : ℕ}
    (beta : TimeVelocityDerivativeIndex d m)
    (h : beta.1.order + 1 ≤ m) :
    toParabolic (timeSucc beta h) =
      ParabolicDerivativeIndex.timeSucc (toParabolic beta)
        (by
          change beta.1.parabolicWeight + 2 ≤ 2 * m
          have hw := beta.1.parabolicWeight_le_two_mul_order
          omega) := by
  apply Subtype.ext
  rfl

/-- The ordinary-to-parabolic embedding commutes with a velocity successor. -/
theorem toParabolic_velocitySucc {d m : ℕ}
    (beta : TimeVelocityDerivativeIndex d m) (i : Fin d)
    (h : beta.1.order + 1 ≤ m) :
    toParabolic (velocitySucc beta i h) =
      ParabolicDerivativeIndex.velocitySucc (toParabolic beta) i
        (by
          change beta.1.parabolicWeight + 1 ≤ 2 * m
          have hw := beta.1.parabolicWeight_le_two_mul_order
          omega) := by
  apply Subtype.ext
  rfl

end TimeVelocityDerivativeIndex

namespace ParabolicWeakDerivativeFamily

/-- The literal ordinary-order view of the selected parabolic representatives. -/
def ordinaryRepresentative
    {d m : ℕ} {U : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (2 * m) U u)
    (beta : TimeVelocityDerivativeIndex d m) :
    TimeVelocity d → ℝ :=
  D.representative beta.toParabolic

/-- Every selected ordinary representative belongs locally to the supplied `L²` family. -/
theorem ordinaryRepresentative_memLp
    {d m : ℕ} {U : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (2 * m) U u)
    (beta : TimeVelocityDerivativeIndex d m) :
    ParabolicMemLpOn U (2 : ℝ≥0∞)
      (D.ordinaryRepresentative beta) :=
  D.memLp beta.toParabolic

/-- The zero ordinary representative agrees almost everywhere with the root function. -/
theorem ordinaryRepresentative_zero_ae
    {d m : ℕ} {U : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (2 * m) U u) :
    D.ordinaryRepresentative (TimeVelocityDerivativeIndex.zero d m)
      =ᵐ[timeVelocityVolumeOn U] u := by
  simpa only [ordinaryRepresentative,
    TimeVelocityDerivativeIndex.toParabolic_zero] using D.zero_ae

/-- The selected time successor is the weak time derivative of an ordinary representative. -/
theorem hasWeakTimeDerivOn_ordinaryRepresentative_timeSucc
    {d m : ℕ} {U : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (2 * m) U u)
    (beta : TimeVelocityDerivativeIndex d m)
    (h : beta.1.order + 1 ≤ m) :
    HasWeakTimeDerivOn U
      (D.ordinaryRepresentative beta)
      (D.ordinaryRepresentative
        (TimeVelocityDerivativeIndex.timeSucc beta h)) := by
  simpa only [ordinaryRepresentative,
    TimeVelocityDerivativeIndex.toParabolic_timeSucc] using
      D.hasWeakTimeSucc beta.toParabolic (by
        change beta.1.parabolicWeight + 2 ≤ 2 * m
        have hw := beta.1.parabolicWeight_le_two_mul_order
        omega)

/-- A selected velocity successor is the corresponding weak velocity derivative. -/
theorem hasWeakVelocityPartialDerivOn_ordinaryRepresentative_velocitySucc
    {d m : ℕ} {U : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (2 * m) U u)
    (beta : TimeVelocityDerivativeIndex d m) (i : Fin d)
    (h : beta.1.order + 1 ≤ m) :
    HasWeakVelocityPartialDerivOn U i
      (D.ordinaryRepresentative beta)
      (D.ordinaryRepresentative
        (TimeVelocityDerivativeIndex.velocitySucc beta i h)) := by
  simpa only [ordinaryRepresentative,
    TimeVelocityDerivativeIndex.toParabolic_velocitySucc] using
      D.hasWeakVelocitySucc beta.toParabolic i (by
        change beta.1.parabolicWeight + 1 ≤ 2 * m
        have hw := beta.1.parabolicWeight_le_two_mul_order
        omega)

/-- Restriction preserves the selected ordinary representatives literally. -/
@[simp] theorem ordinaryRepresentative_restrict
    {d m : ℕ} {U V : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (2 * m) U u)
    (hVU : V ⊆ U) (beta : TimeVelocityDerivativeIndex d m) :
    (D.restrict hVU).ordinaryRepresentative beta =
      D.ordinaryRepresentative beta := rfl

end ParabolicWeakDerivativeFamily

end HypoellipticAleksandrov.Parabolic
