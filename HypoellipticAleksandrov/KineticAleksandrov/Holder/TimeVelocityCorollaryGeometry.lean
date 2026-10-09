module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PairGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.Geometry
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.OscillationBasics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-! # Closure extension and distance comparison for the time–velocity corollary -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Holder
open Set LocalA

/-- The centered local increment is continuous in both endpoints. -/
theorem continuous_kineticIncrement_pair {d : ℕ} (P0 : KineticPoint d) :
    Continuous (fun z : KineticPoint d × KineticPoint d => kineticIncrement P0 z.1 z.2) := by
  have hf : Continuous (Prod.fst : KineticPoint d × KineticPoint d → KineticPoint d) :=
    continuous_fst
  have hs : Continuous (Prod.snd : KineticPoint d × KineticPoint d → KineticPoint d) :=
    continuous_snd
  have ht := (continuous_time.comp hf).sub
    (continuous_time.comp hs)
  have hv := (continuous_velocity.comp hf).sub
    (continuous_velocity.comp hs)
  have hx := ((continuous_position.comp hf).sub
    (continuous_position.comp hs)).sub (ht.smul (continuous_const (y := P0.velocity)))
  exact ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2)).comp ht.abs).add
    (PDE.continuous_vecEuclideanNorm.comp hv) |>.add
    ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 3)).comp
      (PDE.continuous_vecEuclideanNorm.comp hx))

/-- At the later endpoint, the local increment is bounded by the symmetric distance. -/
theorem kineticIncrement_later_le_distance {d : ℕ} (P Q : KineticPoint d) :
    kineticIncrement Q P Q ≤ quasiDistance P Q := by
  unfold kineticIncrement quasiDistance
  rw [← Real.sqrt_eq_rpow]
  have hr := Real.rpow_le_rpow
    (PDE.vecEuclideanNorm_nonneg
      (P.position - Q.position - (P.time - Q.time) • Q.velocity))
    (le_max_right
      (PDE.vecEuclideanNorm (Q.position - P.position - (Q.time - P.time) • P.velocity))
      (PDE.vecEuclideanNorm (P.position - Q.position - (P.time - Q.time) • Q.velocity)))
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  exact add_le_add_right hr _

/-- A continuous local estimate extends to both closed inner-cylinder endpoints. -/
theorem local_estimate_on_closure {d : ℕ} (P0 : KineticPoint d) {R C a : ℝ}
    (ha : 0 ≤ a) (u : KineticPoint d → ℝ)
    (hu : ContinuousOn u (closure (backwardCylinder P0 (R / 2))))
    (hlocal : ∀ P ∈ backwardCylinder P0 (R / 2),
      ∀ Q ∈ backwardCylinder P0 (R / 2),
        |u P - u Q| ≤ C * (kineticIncrement P0 P Q / R) ^ a)
    {P Q : KineticPoint d}
    (hP : P ∈ closure (backwardCylinder P0 (R / 2)))
    (hQ : Q ∈ closure (backwardCylinder P0 (R / 2))) :
    |u P - u Q| ≤ C * (kineticIncrement P0 P Q / R) ^ a := by
  let B := backwardCylinder P0 (R / 2)
  have huc : ContinuousOn (fun z : KineticPoint d × KineticPoint d => |u z.1 - u z.2|)
      (closure (B ×ˢ B)) := by
    rw [closure_prod_eq]
    exact ((hu.comp continuous_fst.continuousOn (fun _ h => h.1)).sub
      (hu.comp continuous_snd.continuousOn (fun _ h => h.2))).abs
  have hrc : Continuous
      (fun z : KineticPoint d × KineticPoint d => C * (kineticIncrement P0 z.1 z.2 / R) ^ a) :=
    continuous_const.mul ((Real.continuous_rpow_const ha).comp
      ((continuous_kineticIncrement_pair P0).div_const R))
  have hpq : (P, Q) ∈ closure (B ×ˢ B) := by
    rw [closure_prod_eq]
    exact ⟨hP, hQ⟩
  exact le_on_closure
    (f := fun z : KineticPoint d × KineticPoint d => |u z.1 - u z.2|)
    (g := fun z => C * (kineticIncrement P0 z.1 z.2 / R) ^ a)
    (s := B ×ˢ B) (fun z hz => hlocal z.1 hz.1 z.2 hz.2)
    huc hrc.continuousOn hpq

end HypoellipticAleksandrov.KineticAleksandrov.Holder
