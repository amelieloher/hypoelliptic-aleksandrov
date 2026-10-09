module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.Differentiation
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.NullFacesBoundary
import Mathlib.Tactic

/-! # A boundary-aware path of admissible cylinders

The path retains its point and reaches the prescribed radius cutoff. Only a spatial
shell of thickness twice the squared cutoff is excluded.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set MeasureTheory

/-- The unit backward cylinder used by the covering theorem. -/
def unitCylinder (d : ℕ) : Set (KineticPoint d) := backwardCylinder ⟨0, 0, 0⟩ 1

/-- Centers of a path retaining X while shrinking velocity toward the origin. -/
def saturationCenter {d : ℕ} (X : KineticPoint d) (r : ℝ) : KineticPoint d :=
  ⟨(1-r^2)*X.time, X.position+(((1-r^2)*X.time)-X.time) • ((1-r) • X.velocity),
    (1-r) • X.velocity⟩

/-- Native coordinate inequalities for membership in the unit cylinder. -/
theorem mem_unitCylinder_iff {d : ℕ} (X : KineticPoint d) :
    X ∈ unitCylinder d ↔ -1 < X.time ∧ X.time < 0 ∧
      PDE.vecEuclideanNorm X.velocity < 1 ∧ PDE.vecEuclideanNorm X.position < 1 := by
  simp only [unitCylinder, mem_backwardCylinder_iff, zero_sub, one_pow,
    PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt zero_lt_one, sub_zero,
    relativePosition, smul_zero]

/-- The point retained by the admissible path has zero relative position. -/
theorem relativePosition_saturationCenter {d : ℕ} (X : KineticPoint d) (r : ℝ) :
    relativePosition (saturationCenter X r) X = 0 := by
  ext i
  simp only [relativePosition, saturationCenter, Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
  ring

/-- Every positive-radius path cylinder contains its point. -/
theorem self_mem_saturationCylinder {d : ℕ} {X : KineticPoint d}
    (hX : X ∈ unitCylinder d) {r : ℝ} (hr : 0 < r) :
    X ∈ backwardCylinder (saturationCenter X r) r := by
  obtain ⟨htlo, hthi, hv, _⟩ := (mem_unitCylinder_iff X).mp hX
  have hr2 := sq_pos_of_pos hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (1-r^2)*X.time-r^2 < X.time
    nlinarith
  · change X.time < (1-r^2)*X.time
    nlinarith
  · rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr]
    have heq : X.velocity-(saturationCenter X r).velocity = r • X.velocity := by
      ext i
      simp only [saturationCenter, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [heq, PDE.vecEuclideanNorm_smul, abs_of_pos hr]
    nlinarith
  · rw [relativePosition_saturationCenter]
    exact PDE.center_mem_euclideanBall 0 (pow_pos hr 3)

/-- Points of a path cylinder stay within r² in time of its retained point. -/
theorem saturationCylinder_time_bound {d : ℕ} {X Y : KineticPoint d}
    (hX : X ∈ unitCylinder d) {r : ℝ} (hr : 0 < r)
    (hY : Y ∈ backwardCylinder (saturationCenter X r) r) :
    |Y.time-X.time| < r^2 :=
  abs_time_sub_lt_sq hY (self_mem_saturationCylinder hX hr)

/-- The path is contained in the unit cylinder away from a spatial shell. -/
theorem saturationCylinder_subset_unit {d : ℕ} {X : KineticPoint d}
    (hX : X ∈ unitCylinder d) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hR : R ≤ 1) (hx : PDE.vecEuclideanNorm X.position < 1-2*R^2) :
    backwardCylinder (saturationCenter X r) r ⊆ unitCylinder d := by
  have hRp : 0 < R := hr.trans_le hrR
  have hr1 : r ≤ 1 := hrR.trans hR
  obtain ⟨htlo, hthi, hv, _⟩ := (mem_unitCylinder_iff X).mp hX
  have hv0 := PDE.vecEuclideanNorm_nonneg X.velocity
  have hvc : PDE.vecEuclideanNorm (saturationCenter X r).velocity ≤ 1-r := by
    change PDE.vecEuclideanNorm ((1-r) • X.velocity) ≤ 1-r
    rw [PDE.vecEuclideanNorm_smul, abs_of_nonneg (sub_nonneg.mpr hr1)]
    nlinarith
  intro Y hY
  apply (mem_unitCylinder_iff Y).mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hbot : -1 ≤ (saturationCenter X r).time-r^2 := by
      change -1 ≤ (1-r^2)*X.time-r^2
      have : 0 ≤ 1-r^2 := by nlinarith
      nlinarith
    exact hbot.trans_lt hY.1
  · have htop : (saturationCenter X r).time ≤ 0 := by
      change (1-r^2)*X.time ≤ 0
      apply mul_nonpos_of_nonneg_of_nonpos <;> nlinarith
    exact hY.2.1.trans_le htop
  · have hy := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr).mp hY.2.2.1
    have heq : Y.velocity = (Y.velocity-(saturationCenter X r).velocity)+
        (saturationCenter X r).velocity := by abel
    rw [heq]
    exact (PDE.vecEuclideanNorm_add_le _ _).trans_lt (by linarith)
  · have hy := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
      (pow_pos hr 3)).mp hY.2.2.2
    rw [sub_zero] at hy
    have htime := saturationCylinder_time_bound hX hr hY
    have heq : Y.position = X.position+relativePosition (saturationCenter X r) Y+
        (Y.time-X.time) • (saturationCenter X r).velocity := by
      ext i
      simp only [relativePosition, saturationCenter, Pi.sub_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      ring
    have hnorm := PDE.vecEuclideanNorm_add_le X.position
      (relativePosition (saturationCenter X r) Y)
    have hnorm2 := PDE.vecEuclideanNorm_add_le
      (X.position+relativePosition (saturationCenter X r) Y)
      ((Y.time-X.time) • (saturationCenter X r).velocity)
    have hmul : |Y.time-X.time| *PDE.vecEuclideanNorm (saturationCenter X r).velocity ≤ r^2 :=
      calc
        _ ≤ r^2*(1-r) := mul_le_mul htime.le hvc
          (PDE.vecEuclideanNorm_nonneg _) (sq_nonneg r)
        _ ≤ r^2 := by nlinarith [sq_nonneg r]
    rw [PDE.vecEuclideanNorm_smul] at hnorm2
    have hs : r^2 ≤ R^2 := by nlinarith
    have hc : r^3 ≤ r^2 := by nlinarith [sq_nonneg r]
    rw [heq]
    linarith

/-- A path cylinder fits in the centered kinetic cylinder of twice its radius. -/
theorem saturationCylinder_subset_centered {d : ℕ} {X : KineticPoint d}
    (hX : X ∈ unitCylinder d) {r : ℝ} (hr : 0 < r) :
    backwardCylinder (saturationCenter X r) r ⊆ centeredCylinder X (2*r) := by
  have hv := ((mem_unitCylinder_iff X).mp hX).2.2.1
  intro Y hY
  apply (mem_centeredCylinder_iff X Y (by positivity : 0 < 2*r)).mpr
  have ht := saturationCylinder_time_bound hX hr hY
  have hyv := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr).mp hY.2.2.1
  have hyp := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
    (pow_pos hr 3)).mp hY.2.2.2
  rw [sub_zero] at hyp
  have heq : (saturationCenter X r).velocity-X.velocity = (-r) • X.velocity := by
    ext i
    simp only [saturationCenter, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hvc : PDE.vecEuclideanNorm ((saturationCenter X r).velocity-X.velocity) < r := by
    rw [heq, PDE.vecEuclideanNorm_smul, abs_neg, abs_of_pos hr]
    nlinarith
  have hvsum : Y.velocity-X.velocity =
      (Y.velocity-(saturationCenter X r).velocity)+
        ((saturationCenter X r).velocity-X.velocity) := by abel
  have hpsum : relativePosition X Y = relativePosition (saturationCenter X r) Y+
      (Y.time-X.time) • ((saturationCenter X r).velocity-X.velocity) := by
    ext i
    simp only [relativePosition, saturationCenter, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨by nlinarith [sq_pos_of_pos hr], ?_, ?_⟩
  · rw [hvsum]
    exact (PDE.vecEuclideanNorm_add_le _ _).trans_lt (by linarith)
  · rw [hpsum]
    have hsum := PDE.vecEuclideanNorm_add_le (relativePosition (saturationCenter X r) Y)
      ((Y.time-X.time) • ((saturationCenter X r).velocity-X.velocity))
    rw [PDE.vecEuclideanNorm_smul] at hsum
    have hmul : |Y.time-X.time| *
        PDE.vecEuclideanNorm ((saturationCenter X r).velocity-X.velocity) ≤ r^3 := by
      have h := mul_le_mul ht.le hvc.le (PDE.vecEuclideanNorm_nonneg _) (sq_nonneg r)
      nlinarith
    nlinarith [pow_pos hr 3]

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
