module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyNestedProjection
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicClosedGeometry

/-!
# Closed nested parabolic Morrey projection comparison

This module extends the nested projection comparison from the open
small forward box to its literal closed forward box by continuity.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set

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

/-- The nested comparison extends to a point in the literal closed
small forward box, without changing its constant. -/
theorem parabolicMorreyNestedProjection_abs_sub_le_largeResidual_closed
    {d : Nat} (t_b : Real) (v_b : PDE.Vec d) {r_b : Real} (hr_b : 0 < r_b)
    (t_s : Real) (v_s : PDE.Vec d) {r_s : Real} (hr_s : 0 < r_s)
    (hsub : parabolicBox 1 r_s t_s v_s ⊆ parabolicBox 1 r_b t_b v_b)
    (u : TimeVelocity d -> Real) (z : TimeVelocity d)
    (hz : z ∈ parabolicClosedBox 1 r_s t_s v_s)
    (hbig : MemLp (fun w => u w -
      parabolicMorreyBoxAffineProjection t_b v_b r_b u w)
      (parabolicExponent d)
      (parabolicNormalizedVolumeOn (parabolicBox 1 r_b t_b v_b))) :
    |parabolicMorreyBoxAffineProjection t_s v_s r_s u z -
      parabolicMorreyBoxAffineProjection t_b v_b r_b u z| ≤
      (1 + 3 * (d : Real)) *
        (r_b / r_s) ^ (((d : Real) + 2) / ((d : Real) + 1)) *
        parabolicLpMeanNormOn d
          (fun w => u w -
            parabolicMorreyBoxAffineProjection t_b v_b r_b u w)
          (parabolicBox 1 r_b t_b v_b) hbig := by
  let Q : Set (TimeVelocity d) := parabolicBox 1 r_s t_s v_s
  let B : Real :=
    (1 + 3 * (d : Real)) *
      (r_b / r_s) ^ (((d : Real) + 2) / ((d : Real) + 1)) *
      parabolicLpMeanNormOn d
        (fun w => u w - parabolicMorreyBoxAffineProjection t_b v_b r_b u w)
        (parabolicBox 1 r_b t_b v_b) hbig
  let F : TimeVelocity d -> Real := fun w =>
    |parabolicMorreyBoxAffineProjection t_s v_s r_s u w -
      parabolicMorreyBoxAffineProjection t_b v_b r_b u w|
  have hclosure : closure Q = parabolicClosedBox 1 r_s t_s v_s :=
    closure_parabolicBox_of_pos (d := d) (vartheta := (1 : Real))
      (r := r_s) (t0 := t_s) (v0 := v_s) (by norm_num) hr_s
  have hcontF : Continuous F :=
    ((continuous_parabolicMorreyBoxAffineProjection t_s v_s r_s u).sub
      (continuous_parabolicMorreyBoxAffineProjection t_b v_b r_b u)).abs
  have hmaps : MapsTo F Q (Iic B) := by
    intro w hw
    exact parabolicMorreyNestedProjection_abs_sub_le_largeResidual
      t_b v_b hr_b t_s v_s hr_s hsub u w (by simpa only [Q] using hw) hbig
  have hmapsClosure : MapsTo F (closure Q) (Iic B) :=
    hmaps.closure_left hcontF isClosed_Iic
  have hzClosure : z ∈ closure Q := by
    rw [hclosure]
    exact hz
  exact hmapsClosure hzClosure

end HypoellipticAleksandrov.Parabolic
