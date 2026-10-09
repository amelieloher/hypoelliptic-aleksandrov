module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PairGeometryCylinderClosure
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PairGeometryCompact
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometryDistance
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.LeakageGeometry
import Mathlib.Tactic

/-! # Both endpoints lie in the closed backward cylinder at the later endpoint -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set

/-- The source quasi-distance controls each literal time, velocity and transport component. -/
theorem quasiDistance_component_bounds {d : ℕ} (P Q : KineticPoint d) :
    |P.time - Q.time| ≤ quasiDistance P Q ^ 2 ∧
      PDE.vecEuclideanNorm (relativeVelocity Q P) ≤ quasiDistance P Q ∧
      PDE.vecEuclideanNorm (relativePosition Q P) ≤ quasiDistance P Q ^ 3 := by
  let A := max (PDE.vecEuclideanNorm (relativePosition P Q))
    (PDE.vecEuclideanNorm (relativePosition Q P))
  have hA : 0 ≤ A := (PDE.vecEuclideanNorm_nonneg _).trans (le_max_left _ _)
  have hs := Real.sqrt_nonneg |P.time - Q.time|
  have hv := PDE.vecEuclideanNorm_nonneg (relativeVelocity Q P)
  have hk := Real.rpow_nonneg hA (1 / 3 : ℝ)
  have hdef : quasiDistance P Q = Real.sqrt |P.time - Q.time| +
      PDE.vecEuclideanNorm (relativeVelocity Q P) + A ^ (1 / 3 : ℝ) := rfl
  have hsD : Real.sqrt |P.time - Q.time| ≤ quasiDistance P Q := by
    rw [hdef]; linarith only [hv, hk]
  have hvD : PDE.vecEuclideanNorm (relativeVelocity Q P) ≤ quasiDistance P Q := by
    rw [hdef]; linarith only [hs, hk]
  have hkD : A ^ (1 / 3 : ℝ) ≤ quasiDistance P Q := by
    rw [hdef]; linarith only [hs, hv]
  have hAeq : (A ^ (1 / 3 : ℝ)) ^ 3 = A := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hA]
    norm_num
  refine ⟨?_, hvD, ?_⟩
  · have he := pow_le_pow_left₀ hs hsD 2
    rw [Real.sq_sqrt (abs_nonneg _)] at he
    exact he
  · have he := pow_le_pow_left₀ hk hkD 3
    rw [hAeq] at he
    exact (le_max_right _ _).trans he

/-- Time-ordered distinct points belong to the closed cylinder at their later endpoint. -/
theorem pair_mem_closed_later_cylinder {d : ℕ}
    (P P' : KineticPoint d) (ht : P.time ≤ P'.time)
    (hpos : 0 < quasiDistance P P') :
    P ∈ closure (backwardCylinder P' (quasiDistance P P')) ∧
      P' ∈ closure (backwardCylinder P' (quasiDistance P P')) := by
  obtain ⟨htime, hv, hx⟩ := quasiDistance_component_bounds P P'
  refine ⟨mem_closure_backwardCylinder_of_bounds P' P hpos ?_
    (sub_nonpos.mpr ht) hx hv, ?_⟩
  · rw [abs_of_nonpos (sub_nonpos.mpr ht)] at htime
    linarith only [htime]
  · exact Covering.top_mem_closure_cylinder P' hpos
      (PDE.center_mem_euclideanBall _ hpos)

end HypoellipticAleksandrov.KineticAleksandrov.Holder
