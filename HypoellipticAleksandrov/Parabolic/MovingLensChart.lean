module

public import HypoellipticAleksandrov.Parabolic.MovingLensGeometry

/-!
# Moving-lens chart geometry

This module records the time-preserving chart which normalizes a moving lens
to the unit parabolic cylinder.  It is purely set-theoretic Euclidean geometry.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- The time-preserving chart which normalizes moving-lens velocity displacement. -/
def movingLensChart {d : Nat} (xi eps : Real) (y : PDE.Vec d) :
    TimeVelocity d → TimeVelocity d :=
  fun z => (z.1,
    (Real.sqrt (movingLensDenominator xi eps z.1))⁻¹ •
      movingLensDisplacement y z)

/-- The inverse time-preserving chart from the normalized velocity coordinate. -/
def movingLensChartInv {d : Nat} (xi eps : Real) (y : PDE.Vec d) :
    TimeVelocity d → TimeVelocity d :=
  fun z => (z.1,
    z.1 • y + Real.sqrt (movingLensDenominator xi eps z.1) • z.2)

private theorem movingLensDisplacement_chartInv {d : Nat} (xi eps : Real)
    (y : PDE.Vec d) (z : TimeVelocity d) :
    movingLensDisplacement y (movingLensChartInv xi eps y z) =
      Real.sqrt (movingLensDenominator xi eps z.1) • z.2 := by
  ext i
  simp only [movingLensDisplacement, movingLensChartInv,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem movingLensChart_velocity_sq {d : Nat} {xi eps : Real} {y : PDE.Vec d}
    {z : TimeVelocity d} (hxi : 0 ≤ xi) (heps : 0 < eps) (hz : 0 ≤ z.1) :
    PDE.vecNormSq (movingLensChart xi eps y z).2 =
      PDE.vecNormSq (movingLensDisplacement y z) /
        movingLensDenominator xi eps z.1 := by
  have hden : 0 < movingLensDenominator xi eps z.1 :=
    movingLensDenominator_pos hxi heps hz
  change PDE.vecNormSq
      ((Real.sqrt (movingLensDenominator xi eps z.1))⁻¹ •
        movingLensDisplacement y z) =
    PDE.vecNormSq (movingLensDisplacement y z) /
      movingLensDenominator xi eps z.1
  rw [PDE.vecNormSq_smul, inv_pow, Real.sq_sqrt hden.le, div_eq_mul_inv]
  ring

private theorem movingLensChartInv_displacement_sq {d : Nat} {xi eps : Real}
    {y : PDE.Vec d} {z : TimeVelocity d} (hxi : 0 ≤ xi) (heps : 0 < eps)
    (hz : 0 ≤ z.1) :
    PDE.vecNormSq (movingLensDisplacement y (movingLensChartInv xi eps y z)) =
      movingLensDenominator xi eps z.1 * PDE.vecNormSq z.2 := by
  have hden : 0 < movingLensDenominator xi eps z.1 :=
    movingLensDenominator_pos hxi heps hz
  rw [movingLensDisplacement_chartInv, PDE.vecNormSq_smul, Real.sq_sqrt hden.le]

/-- Applying the inverse chart after the moving-lens chart recovers a nonnegative-time
point. -/
@[simp] theorem movingLensChartInv_apply_movingLensChart
    {d : Nat} {xi eps : Real} {y : PDE.Vec d} {z : TimeVelocity d}
    (hxi : 0 ≤ xi) (heps : 0 < eps) (hz : 0 ≤ z.1) :
    movingLensChartInv xi eps y (movingLensChart xi eps y z) = z := by
  have hden : 0 < movingLensDenominator xi eps z.1 :=
    movingLensDenominator_pos hxi heps hz
  have hsqrt : 0 < Real.sqrt (movingLensDenominator xi eps z.1) :=
    Real.sqrt_pos.2 hden
  apply Prod.ext
  · rfl
  · ext i
    change (z.1 • y + Real.sqrt (movingLensDenominator xi eps z.1) •
        ((Real.sqrt (movingLensDenominator xi eps z.1))⁻¹ •
          (z.2 - z.1 • y))) i = z.2 i
    rw [smul_smul, mul_inv_cancel₀ hsqrt.ne', one_smul]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- Applying the moving-lens chart after its inverse recovers a nonnegative-time
normalized point. -/
@[simp] theorem movingLensChart_apply_movingLensChartInv
    {d : Nat} {xi eps : Real} {y : PDE.Vec d} {z : TimeVelocity d}
    (hxi : 0 ≤ xi) (heps : 0 < eps) (hz : 0 ≤ z.1) :
    movingLensChart xi eps y (movingLensChartInv xi eps y z) = z := by
  have hden : 0 < movingLensDenominator xi eps z.1 :=
    movingLensDenominator_pos hxi heps hz
  have hsqrt : 0 < Real.sqrt (movingLensDenominator xi eps z.1) :=
    Real.sqrt_pos.2 hden
  apply Prod.ext
  · rfl
  · ext i
    change ((Real.sqrt (movingLensDenominator xi eps z.1))⁻¹ •
        movingLensDisplacement y (movingLensChartInv xi eps y z)) i = z.2 i
    rw [movingLensDisplacement_chartInv, smul_smul, inv_mul_cancel₀ hsqrt.ne', one_smul]

/-- The chart maps the closed moving lens exactly onto the closed unit cylinder. -/
theorem movingLensChart_image_closed
    {d : Nat} {xi eps tau : Real} {y : PDE.Vec d}
    (hxi : 0 ≤ xi) (heps : 0 < eps) :
    movingLensChart xi eps y '' movingLensClosed xi eps tau y =
      closedParabolicCylinder tau (0 : PDE.Vec d) := by
  apply Set.Subset.antisymm
  · rintro q ⟨z, hz, rfl⟩
    rw [mem_closedParabolicCylinder_iff]
    refine ⟨hz.1, hz.2.1, ?_⟩
    have hden : 0 < movingLensDenominator xi eps z.1 :=
      movingLensDenominator_pos hxi heps hz.1
    have hvelocity : PDE.vecNormSq (movingLensChart xi eps y z).2 ≤ 1 := by
      rw [movingLensChart_velocity_sq hxi heps hz.1]
      exact (div_le_one₀ hden).mpr (by simpa using hz.2.2)
    simpa [PDE.euclideanClosedBall, PDE.euclideanSqDist] using hvelocity
  · intro q hq
    rw [mem_closedParabolicCylinder_iff] at hq
    refine ⟨movingLensChartInv xi eps y q, ?_, ?_⟩
    · refine ⟨hq.1, hq.2.1, ?_⟩
      have hden : 0 < movingLensDenominator xi eps q.1 :=
        movingLensDenominator_pos hxi heps hq.1
      have hvelocity : PDE.vecNormSq q.2 ≤ 1 := by
        simpa [PDE.euclideanClosedBall, PDE.euclideanSqDist] using hq.2.2
      change PDE.vecNormSq (movingLensDisplacement y (movingLensChartInv xi eps y q)) ≤
        movingLensDenominator xi eps q.1
      rw [movingLensChartInv_displacement_sq hxi heps hq.1]
      simpa using mul_le_mul_of_nonneg_left hvelocity hden.le
    · exact movingLensChart_apply_movingLensChartInv hxi heps hq.1

/-- The chart maps the active moving lens exactly onto the forward-reachable unit
parabolic cylinder, retaining its terminal interior face. -/
theorem movingLensChart_image_active
    {d : Nat} {xi eps tau : Real} {y : PDE.Vec d}
    (hxi : 0 ≤ xi) (heps : 0 < eps) :
    movingLensChart xi eps y '' movingLensActive xi eps tau y =
      parabolicReachable tau (0 : PDE.Vec d) := by
  apply Set.Subset.antisymm
  · rintro q ⟨z, hz, rfl⟩
    rw [mem_parabolicReachable_iff]
    refine ⟨hz.1, hz.2.1, ?_⟩
    have hden : 0 < movingLensDenominator xi eps z.1 :=
      movingLensDenominator_pos hxi heps hz.1.le
    have hvelocity : PDE.vecNormSq (movingLensChart xi eps y z).2 < 1 := by
      rw [movingLensChart_velocity_sq hxi heps hz.1.le]
      exact (div_lt_one₀ hden).mpr (by simpa using hz.2.2)
    simpa [PDE.euclideanBall, PDE.euclideanSqDist] using hvelocity
  · intro q hq
    rw [mem_parabolicReachable_iff] at hq
    refine ⟨movingLensChartInv xi eps y q, ?_, ?_⟩
    · refine ⟨hq.1, hq.2.1, ?_⟩
      have hden : 0 < movingLensDenominator xi eps q.1 :=
        movingLensDenominator_pos hxi heps hq.1.le
      have hvelocity : PDE.vecNormSq q.2 < 1 := by
        simpa [PDE.euclideanBall, PDE.euclideanSqDist] using hq.2.2
      change PDE.vecNormSq (movingLensDisplacement y (movingLensChartInv xi eps y q)) <
        movingLensDenominator xi eps q.1
      rw [movingLensChartInv_displacement_sq hxi heps hq.1.le]
      simpa using mul_lt_mul_of_pos_left hvelocity hden
    · exact movingLensChart_apply_movingLensChartInv hxi heps hq.1.le

/-- The chart transports the initial and lateral moving-lens boundary exactly to the
forward parabolic boundary. -/
theorem movingLensChart_image_causalBoundary
    {d : Nat} {xi eps tau : Real} {y : PDE.Vec d}
    (hxi : 0 ≤ xi) (heps : 0 < eps) (htau : 0 ≤ tau) :
    movingLensChart xi eps y ''
        (movingLensClosed xi eps tau y \ movingLensActive xi eps tau y) =
      forwardParabolicBoundary tau (0 : PDE.Vec d) := by
  apply Set.Subset.antisymm
  · rintro q ⟨z, hz, rfl⟩
    rw [mem_movingLensClosed_diff_active_iff] at hz
    rw [mem_forwardParabolicBoundary_iff]
    rcases hz with hinitial | hlateral
    · refine Or.inl ⟨hinitial.1, ?_⟩
      have hden : 0 < movingLensDenominator xi eps z.1 :=
        movingLensDenominator_pos hxi heps hinitial.1.ge
      have hvelocity : PDE.vecNormSq (movingLensChart xi eps y z).2 ≤ 1 := by
        rw [movingLensChart_velocity_sq hxi heps hinitial.1.ge]
        exact (div_le_one₀ hden).mpr (by simpa using hinitial.2.2)
      simpa [PDE.euclideanClosedBall, PDE.euclideanSqDist] using hvelocity
    · refine Or.inr ⟨hlateral.1, hlateral.2.1, ?_⟩
      have hden : 0 < movingLensDenominator xi eps z.1 :=
        movingLensDenominator_pos hxi heps hlateral.1
      have hvelocity : PDE.vecNormSq (movingLensChart xi eps y z).2 = 1 := by
        rw [movingLensChart_velocity_sq hxi heps hlateral.1]
        calc
          PDE.vecNormSq (movingLensDisplacement y z) /
              movingLensDenominator xi eps z.1 =
            movingLensDenominator xi eps z.1 /
              movingLensDenominator xi eps z.1 := by rw [hlateral.2.2]
          _ = 1 := div_self hden.ne'
      simpa [PDE.euclideanSphere, PDE.euclideanSqDist] using hvelocity
  · intro q hq
    rw [mem_forwardParabolicBoundary_iff] at hq
    rcases hq with hinitial | hlateral
    · refine ⟨movingLensChartInv xi eps y q, ?_, ?_⟩
      rw [mem_movingLensClosed_diff_active_iff]
      refine Or.inl ⟨?_, ?_, ?_⟩
      · simpa [movingLensChartInv] using hinitial.1
      · simpa [movingLensChartInv, hinitial.1] using htau
      · have htime : 0 ≤ q.1 := hinitial.1.ge
        have hden : 0 < movingLensDenominator xi eps q.1 :=
          movingLensDenominator_pos hxi heps htime
        have hvelocity : PDE.vecNormSq q.2 ≤ 1 := by
          simpa [PDE.euclideanClosedBall, PDE.euclideanSqDist] using hinitial.2
        change PDE.vecNormSq (movingLensDisplacement y (movingLensChartInv xi eps y q)) ≤
          movingLensDenominator xi eps q.1
        rw [movingLensChartInv_displacement_sq hxi heps htime]
        simpa using mul_le_mul_of_nonneg_left hvelocity hden.le
      · exact movingLensChart_apply_movingLensChartInv hxi heps hinitial.1.ge
    · refine ⟨movingLensChartInv xi eps y q, ?_, ?_⟩
      rw [mem_movingLensClosed_diff_active_iff]
      refine Or.inr ⟨hlateral.1, hlateral.2.1, ?_⟩
      have hden : 0 < movingLensDenominator xi eps q.1 :=
        movingLensDenominator_pos hxi heps hlateral.1
      have hvelocity : PDE.vecNormSq q.2 = 1 := by
        simpa [PDE.euclideanSphere, PDE.euclideanSqDist] using hlateral.2.2
      change PDE.vecNormSq (movingLensDisplacement y (movingLensChartInv xi eps y q)) =
        movingLensDenominator xi eps q.1
      rw [movingLensChartInv_displacement_sq hxi heps hlateral.1, hvelocity, mul_one]
      · exact movingLensChart_apply_movingLensChartInv hxi heps hlateral.1

/-- The moving-lens terminal center is sent to the normalized terminal origin. -/
@[simp] theorem movingLensChart_terminalCenter
    {d : Nat} {xi eps tau : Real} {y : PDE.Vec d}
    (hxi : 0 ≤ xi) (heps : 0 < eps) (htau : 0 ≤ tau) :
    movingLensChart xi eps y (tau, tau • y) = (tau, 0) := by
  have _ := movingLensDenominator_pos hxi heps htau
  ext <;> simp [movingLensChart, movingLensDisplacement]

end

end HypoellipticAleksandrov.Parabolic
