module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PatchPower
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PairGeometry
import Mathlib.Tactic

/-! # Concrete nested open boxes in the return-time proof -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Set Holder

/-- Small nested open boxes around `(1,0,v)`, with physical Euclidean coordinate radii. -/
def returnBox (v R : ℝ) : Set Point :=
  {p | |p.time - 1| < R / 64 ∧ PDE.vecEuclideanNorm p.position < R / 64 ∧
    PDE.vecEuclideanNorm (p.velocity - fun _ => v) < R / 64}

/-- The reference boxes are open in the kinetic topology. -/
theorem returnBox_isOpen (v R : ℝ) : IsOpen (returnBox v R) :=
  (isOpen_lt ((continuous_time.sub continuous_const).abs) continuous_const).inter
    ((isOpen_lt (PDE.continuous_vecEuclideanNorm.comp continuous_position)
      continuous_const).inter (isOpen_lt
        (PDE.continuous_vecEuclideanNorm.comp (continuous_velocity.sub continuous_const))
        continuous_const))

/-- One-dimensional Euclidean norm is the absolute value of the unique coordinate. -/
theorem return_norm_one (w : PDE.Vec 1) : PDE.vecEuclideanNorm w = |w 0| := by
  simp [PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot,
    ← pow_two, Real.sqrt_sq_eq_abs]

/-- The centre lies in every positive-radius return box. -/
theorem returnBox_center (v R : ℝ) (hR : 0 < R) : point 1 0 v ∈ returnBox v R := by
  simp only [returnBox, point, mem_ofPred_eq, sub_self, abs_zero, return_norm_one,
    Pi.sub_apply]
  exact ⟨by positivity, by positivity, by positivity⟩

/-- Coordinate bounds for every point in the closure of a source backward cylinder. -/
theorem returnCylinder_bounds (z p : Point) (r : ℝ) (hr : 0 < r)
    (hp : p ∈ closure (backwardCylinder z r)) :
    |p.time - z.time| ≤ r ^ 2 ∧
      PDE.vecEuclideanNorm (p.velocity - z.velocity) ≤ r ∧
      PDE.vecEuclideanNorm (relativePosition z p) ≤ r ^ 3 := by
  have hclosed : IsClosed {q : Point | |q.time - z.time| ≤ r ^ 2 ∧
      PDE.vecEuclideanNorm (q.velocity - z.velocity) ≤ r ∧
      PDE.vecEuclideanNorm (relativePosition z q) ≤ r ^ 3} := by
    apply (isClosed_le ((continuous_time.sub continuous_const).abs) continuous_const).inter
    apply (isClosed_le
      (PDE.continuous_vecEuclideanNorm.comp (continuous_velocity.sub continuous_const))
      continuous_const).inter
    exact isClosed_le
      (PDE.continuous_vecEuclideanNorm.comp
        ((continuous_position.sub continuous_const).sub
          ((continuous_time.sub continuous_const).smul continuous_const)))
      (continuous_const : Continuous (fun _ : Point => r ^ 3))
  apply closure_minimal (s := backwardCylinder z r) ?_ hclosed hp
  intro q hq
  refine ⟨abs_le.mpr ⟨by linarith [hq.1], by nlinarith [hq.2.1, sq_nonneg r]⟩,
    ((PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr).mp hq.2.2.1).le, ?_⟩
  simpa only [sub_zero] using
    ((PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (pow_pos hr 3)).mp hq.2.2.2).le

/-- Every return box used in the iteration lies in the reference region. -/
theorem returnBox_subset_reference (v R : ℝ) (hv : |v| ≤ 1) (hR : R ≤ 1) :
    returnBox v R ⊆ returnReferenceRegion := by
  intro p hp
  have ht := abs_lt.mp hp.1
  have hvel := PDE.vecEuclideanNorm_add_le (p.velocity - fun _ => v) (fun _ => v)
  rw [sub_add_cancel, return_norm_one (fun _ => v)] at hvel
  exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩,
    by linarith [hp.2.1], by linarith [hp.2.2]⟩

/-- A radius proportional to the box gap leaves room for all surrounding cylinders. -/
theorem returnBox_cylinder_subset (v a b : ℝ) (hv : |v| ≤ 1)
    (ha : 1 / 2 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (z : Point) (hz : z ∈ returnBox v a) :
    closure (backwardCylinder z (2 * ((b - a) / 4096))) ⊆ returnBox v b := by
  let r := 2 * ((b - a) / 4096)
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by dsimp [r]; linarith
  have hrsq : r ^ 2 ≤ r := by nlinarith
  have hrcube : r ^ 3 ≤ r := by
    have hh := mul_le_mul_of_nonneg_right hrsq hr.le
    nlinarith
  have hvelz : PDE.vecEuclideanNorm z.velocity ≤ 2 :=
    ((returnBox_subset_reference v a hv (by linarith)) hz).2.2
  intro p hp
  obtain ⟨ht, hvp, hxp⟩ := returnCylinder_bounds z p r hr hp
  have htime := abs_add_le (p.time - z.time) (z.time - 1)
  have hve := PDE.vecEuclideanNorm_add_le (p.velocity - z.velocity)
    (z.velocity - fun _ => v)
  have hxe := PDE.vecEuclideanNorm_add_le (relativePosition z p)
    (z.position + (p.time - z.time) • z.velocity)
  have hxe' := PDE.vecEuclideanNorm_add_le z.position ((p.time - z.time) • z.velocity)
  rw [PDE.vecEuclideanNorm_smul] at hxe'
  have hmul := mul_le_mul ht hvelz (PDE.vecEuclideanNorm_nonneg _) (sq_nonneg r)
  have hpos : relativePosition z p +
      (z.position + (p.time - z.time) • z.velocity) = p.position := by
    unfold relativePosition
    module
  rw [hpos] at hxe
  have hvs : p.velocity - z.velocity + (z.velocity - fun _ => v) =
      p.velocity - fun _ => v := by abel
  rw [hvs] at hve
  have hts : p.time - z.time + (z.time - 1) = p.time - 1 := by ring
  rw [hts] at htime
  refine ⟨?_, ?_, ?_⟩ <;> dsimp [r] at * <;>
    linarith [hz.1, hz.2.1, hz.2.2]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
