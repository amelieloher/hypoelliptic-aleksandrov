module

public import HypoellipticAleksandrov.Parabolic.GenericParabolicIndexArithmetic
public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamily
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique

/-!
# Shifts and extensionality for parabolic weak derivative families

This module re-roots a coherent bounded family of weak derivatives at a selected
entry and proves that coherent families with almost-everywhere equal roots have
almost-everywhere equal representatives at every bounded parabolic index.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped ENNReal

namespace ParabolicDerivativeIndex

/-- Add a bounded right index to a fixed left index while staying inside the
original parabolic-weight bound. -/
def addWithin
    {d L M : ℕ}
    (alpha : ParabolicDerivativeIndex d L)
    (beta : ParabolicDerivativeIndex d M)
    (hαM : alpha.1.parabolicWeight + M ≤ L) :
    ParabolicDerivativeIndex d L :=
  ⟨alpha.1 + beta.1, by
    rw [TimeVelocityMultiIndex.parabolicWeight_add]
    exact (Nat.add_le_add_left beta.2 _).trans hαM⟩

/-- The underlying multi-index of `addWithin` is literal addition. -/
@[simp] theorem coe_addWithin
    {d L M : ℕ}
    (alpha : ParabolicDerivativeIndex d L)
    (beta : ParabolicDerivativeIndex d M)
    (hαM : alpha.1.parabolicWeight + M ≤ L) :
    (ParabolicDerivativeIndex.addWithin alpha beta hαM).1 =
      alpha.1 + beta.1 :=
  rfl

/-- Adding the bounded zero index leaves the fixed left index unchanged. -/
@[simp] theorem addWithin_zero
    {d L M : ℕ}
    (alpha : ParabolicDerivativeIndex d L)
    (hαM : alpha.1.parabolicWeight + M ≤ L) :
    ParabolicDerivativeIndex.addWithin alpha
        (ParabolicDerivativeIndex.zero d M) hαM = alpha := by
  apply Subtype.ext
  exact add_zero alpha.1

private theorem addWithin_timeSucc
    {d L M : ℕ}
    (alpha : ParabolicDerivativeIndex d L)
    (beta : ParabolicDerivativeIndex d M)
    (hαM : alpha.1.parabolicWeight + M ≤ L)
    (hβ : beta.1.parabolicWeight + 2 ≤ M)
    (hL : (addWithin alpha beta hαM).1.parabolicWeight + 2 ≤ L) :
    addWithin alpha (timeSucc beta hβ) hαM =
      timeSucc (addWithin alpha beta hαM) hL := by
  apply Subtype.ext
  funext c
  rcases c with _ | i
  · change alpha.1 (timeCoord d) + (beta.1 (timeCoord d) + 1) =
      alpha.1 (timeCoord d) + beta.1 (timeCoord d) + 1
    omega
  · rfl

private theorem addWithin_velocitySucc
    {d L M : ℕ}
    (alpha : ParabolicDerivativeIndex d L)
    (beta : ParabolicDerivativeIndex d M)
    (i : Fin d)
    (hαM : alpha.1.parabolicWeight + M ≤ L)
    (hβ : beta.1.parabolicWeight + 1 ≤ M)
    (hL : (addWithin alpha beta hαM).1.parabolicWeight + 1 ≤ L) :
    addWithin alpha (velocitySucc beta i hβ) hαM =
      velocitySucc (addWithin alpha beta hαM) i hL := by
  apply Subtype.ext
  funext c
  rcases c with _ | j
  · rfl
  · by_cases hji : j = i
    · subst j
      simp [addWithin, velocitySucc, TimeVelocityMultiIndex.ofTimeVelocity,
        TimeVelocityMultiIndex.velocity, velocityCoord, Nat.add_assoc]
    · simp [addWithin, velocitySucc, TimeVelocityMultiIndex.ofTimeVelocity,
        TimeVelocityMultiIndex.velocity, velocityCoord, hji]

end ParabolicDerivativeIndex

namespace ParabolicWeakDerivativeFamily

/-- Re-root a coherent weak derivative family at a fixed selected derivative,
retaining `M` further parabolic weights. -/
def shift
    {d L M : ℕ} {U : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d L U u)
    (alpha : ParabolicDerivativeIndex d L)
    (hαM : alpha.1.parabolicWeight + M ≤ L) :
    ParabolicWeakDerivativeFamily d M U (D.representative alpha) where
  representative := fun beta =>
    D.representative (ParabolicDerivativeIndex.addWithin alpha beta hαM)
  memLp := fun beta => D.memLp _
  zero_ae := by
    rw [ParabolicDerivativeIndex.addWithin_zero]
  hasWeakTimeSucc := by
    intro beta hβ
    have hL : (ParabolicDerivativeIndex.addWithin alpha beta hαM).1.parabolicWeight +
        2 ≤ L := by
      change (alpha.1 + beta.1).parabolicWeight + 2 ≤ L
      rw [TimeVelocityMultiIndex.parabolicWeight_add]
      exact (Nat.add_le_add_left hβ _).trans hαM
    rw [ParabolicDerivativeIndex.addWithin_timeSucc alpha beta hαM hβ hL]
    exact D.hasWeakTimeSucc _ hL
  hasWeakVelocitySucc := by
    intro beta i hβ
    have hL : (ParabolicDerivativeIndex.addWithin alpha beta hαM).1.parabolicWeight +
        1 ≤ L := by
      change (alpha.1 + beta.1).parabolicWeight + 1 ≤ L
      rw [TimeVelocityMultiIndex.parabolicWeight_add]
      exact (Nat.add_le_add_left hβ _).trans hαM
    rw [ParabolicDerivativeIndex.addWithin_velocitySucc alpha beta i hαM hβ hL]
    exact D.hasWeakVelocitySucc _ i hL

/-- A shifted family selects the literal sum of its root and increment indices. -/
@[simp] theorem shift_representative
    {d L M : ℕ} {U : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d L U u)
    (alpha : ParabolicDerivativeIndex d L)
    (hαM : alpha.1.parabolicWeight + M ≤ L)
    (beta : ParabolicDerivativeIndex d M) :
    (D.shift alpha hαM).representative beta =
      D.representative
        (ParabolicDerivativeIndex.addWithin alpha beta hαM) :=
  rfl

/-- Coherent restricted-`L²` weak derivative families on an open carrier are
determined almost everywhere by their root functions. -/
theorem representative_ae_eq_of_root_ae
    {d L : ℕ} {U : Set (TimeVelocity d)} (hU : IsOpen U)
    {u v : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d L U u)
    (E : ParabolicWeakDerivativeFamily d L U v)
    (hroot : u =ᵐ[timeVelocityVolumeOn U] v)
    (beta : ParabolicDerivativeIndex d L) :
    D.representative beta =ᵐ[timeVelocityVolumeOn U]
      E.representative beta := by
  induction beta using ParabolicDerivativeIndex.inductionOn with
  | hzero => exact D.zero_ae.trans (hroot.trans E.zero_ae.symm)
  | htime gamma hstay ih =>
      exact HasWeakTimeDerivOn.ae_eq_of_memLp hU (by norm_num)
        (D.memLp _) (E.memLp _) (D.hasWeakTimeSucc gamma hstay)
        ((E.hasWeakTimeSucc gamma hstay).congr_value_ae ih.symm)
  | hvelocity gamma i hstay ih =>
      exact HasWeakVelocityPartialDerivOn.ae_eq_of_memLp hU (by norm_num)
        (D.memLp _) (E.memLp _) (D.hasWeakVelocitySucc gamma i hstay)
        ((E.hasWeakVelocitySucc gamma i hstay).congr_value_ae ih.symm)

end ParabolicWeakDerivativeFamily

end HypoellipticAleksandrov.Parabolic
