module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicStep
public import Mathlib.Tactic

/-!
# Closed one-step dyadic parabolic Morrey projection estimate

This module extends the open-child dyadic projection estimate to the literal
closed child box by continuity.  It proves neither a chain estimate nor a
representative result.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Set
open scoped Topology

private theorem continuous_parabolicMorreyBoxAffineProjection
    {d : Nat} (t : Real) (v : PDE.Vec d) (r : Real)
    (u : TimeVelocity d -> Real) :
    Continuous (parabolicMorreyBoxAffineProjection t v r u) := by
  unfold parabolicMorreyBoxAffineProjection
  apply Continuous.add continuous_const
  apply continuous_finset_sum
  intro i _
  exact continuous_const.mul ((continuous_apply i).comp continuous_snd |>.sub
    continuous_const)

/-- The open-child dyadic projection estimate extends continuously to
the literal closed forward child box, with the same dimension-only constant. -/
theorem exists_parabolicMorreyDyadicChildProjectionClosedConst (d : Nat)
    (hd : 1 <= d) :
    ∃ C : Real, 0 < C ∧
      ∀ (n : Nat) (index : ParabolicDyadicIndex d n)
        (child : ParabolicDyadicChild d) (u : TimeVelocity d -> Real),
        ContDiff Real 2 u ->
        ∀ z : TimeVelocity d,
          z ∈ parabolicClosedBox 1
              (parabolicDyadicSourceBox
                (parabolicDyadicChildIndex index child)).radius
              (parabolicDyadicSourceBox
                (parabolicDyadicChildIndex index child)).baseTime
              (parabolicDyadicSourceBox
                (parabolicDyadicChildIndex index child)).center ->
          |parabolicMorreyBoxAffineProjection
              (parabolicDyadicSourceBox
                (parabolicDyadicChildIndex index child)).baseTime
              (parabolicDyadicSourceBox
                (parabolicDyadicChildIndex index child)).center
              (parabolicDyadicSourceBox
                (parabolicDyadicChildIndex index child)).radius u z -
            parabolicMorreyBoxAffineProjection
              (parabolicDyadicSourceBox index).baseTime
              (parabolicDyadicSourceBox index).center
              (parabolicDyadicSourceBox index).radius u z| <=
            C * (parabolicDyadicSourceBox index).radius ^
                  parabolicMorreyExponent d *
              (parabolicLpNormOn d (timeDerivative u) (parabolicBox 1
                (parabolicDyadicSourceBox index).radius
                (parabolicDyadicSourceBox index).baseTime
                (parabolicDyadicSourceBox index).center) +
                ∑ i : Fin d, ∑ j : Fin d,
                  parabolicLpNormOn d (fun w => velocityHessian u w i j)
                    (parabolicBox 1 (parabolicDyadicSourceBox index).radius
                      (parabolicDyadicSourceBox index).baseTime
                      (parabolicDyadicSourceBox index).center)) := by
  obtain ⟨C, hCpos, hopen⟩ :=
    exists_parabolicMorreyDyadicChildProjectionConst d hd
  refine ⟨C, hCpos, ?_⟩
  intro n index child u hu z hz
  let qC := parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)
  let QC : Set (TimeVelocity d) := parabolicBox 1 qC.radius qC.baseTime qC.center
  let B : Real := C * (parabolicDyadicSourceBox index).radius ^
      parabolicMorreyExponent d *
    (parabolicLpNormOn d (timeDerivative u) (parabolicBox 1
      (parabolicDyadicSourceBox index).radius
      (parabolicDyadicSourceBox index).baseTime
      (parabolicDyadicSourceBox index).center) +
      ∑ i : Fin d, ∑ j : Fin d,
        parabolicLpNormOn d (fun w => velocityHessian u w i j)
          (parabolicBox 1 (parabolicDyadicSourceBox index).radius
            (parabolicDyadicSourceBox index).baseTime
            (parabolicDyadicSourceBox index).center))
  let F : TimeVelocity d -> Real := fun w =>
    |parabolicMorreyBoxAffineProjection qC.baseTime qC.center qC.radius u w -
      parabolicMorreyBoxAffineProjection
        (parabolicDyadicSourceBox index).baseTime
        (parabolicDyadicSourceBox index).center
        (parabolicDyadicSourceBox index).radius u w|
  have hqC : 0 < qC.radius :=
    parabolicDyadicSourceBox_radius_pos (parabolicDyadicChildIndex index child)
  have hclosure : closure QC = parabolicClosedBox 1 qC.radius qC.baseTime qC.center :=
    closure_parabolicBox_of_pos (d := d) (vartheta := (1 : Real))
      (r := qC.radius) (t0 := qC.baseTime) (v0 := qC.center) (by norm_num) hqC
  have hcontF : Continuous F :=
    ((continuous_parabolicMorreyBoxAffineProjection qC.baseTime qC.center qC.radius u).sub
      (continuous_parabolicMorreyBoxAffineProjection
        (parabolicDyadicSourceBox index).baseTime
        (parabolicDyadicSourceBox index).center
        (parabolicDyadicSourceBox index).radius u)).abs
  have hmaps : MapsTo F QC (Iic B) := by
    intro w hw
    exact hopen n index child u hu w (by simpa only [qC, QC] using hw)
  have hmapsClosure : MapsTo F (closure QC) (closure (Iic B)) :=
    hmaps.closure_of_continuousOn hcontF.continuousOn
  have hzClosure : z ∈ closure QC := by
    rw [hclosure]
    simpa only [qC] using hz
  have hFz := hmapsClosure hzClosure
  simpa only [isClosed_Iic.closure_eq, mem_Iic, F, B] using hFz

end HypoellipticAleksandrov.Parabolic
