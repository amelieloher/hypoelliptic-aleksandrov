module

public import HypoellipticAleksandrov.KineticAleksandrov.Geometry
public import PDEFoundation.Geometry.EuclideanBall.Topology
import Mathlib.Tactic

/-! # Centered inflation and engulfing of backward kinetic cylinders

All vector bounds use the explicit Euclidean norm. Centered inflation moves the top face
along free transport, so it preserves relative position and velocity coordinates.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set

/-- The center of the time-centered inflation, transported along the center velocity. -/
def inflationCenter {d : ℕ} (P : KineticPoint d) (r k : ℝ) : KineticPoint d :=
  ⟨P.time + (k ^ 2 - 1) * r ^ 2 / 2,
    P.position + ((k ^ 2 - 1) * r ^ 2 / 2) • P.velocity, P.velocity⟩

/-- Centered kinetic inflation by the factor k. -/
def inflatedCylinder {d : ℕ} (P : KineticPoint d) (r k : ℝ) :
    Set (KineticPoint d) := backwardCylinder (inflationCenter P r k) (k * r)

/-- Inflation preserves the free-transport position coordinates. -/
theorem relativePosition_inflationCenter {d : ℕ} (P Z : KineticPoint d) (r k : ℝ) :
    relativePosition (inflationCenter P r k) Z = relativePosition P Z := by
  ext i
  simp only [relativePosition, inflationCenter, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

/-- Every backward kinetic cylinder is open in the transported product topology. -/
theorem isOpen_cylinder {d : ℕ} (P : KineticPoint d) (r : ℝ) :
    IsOpen (backwardCylinder P r) := by
  have hx : Continuous (relativePosition P) :=
    (continuous_position.sub continuous_const).sub
      ((continuous_time.sub continuous_const).smul continuous_const)
  exact (isOpen_lt continuous_const continuous_time).inter
    ((isOpen_lt continuous_time continuous_const).inter
      (((PDE.isOpen_euclideanBall P.velocity r).preimage continuous_velocity).inter
        ((PDE.isOpen_euclideanBall 0 (r ^ 3)).preimage hx)))

/-- Positive-radius cylinders have an explicit interior point. -/
theorem cylinder_nonempty {d : ℕ} (P : KineticPoint d) {r : ℝ} (hr : 0 < r) :
    (backwardCylinder P r).Nonempty := by
  refine ⟨⟨P.time - r ^ 2 / 2, P.position - (r ^ 2 / 2) • P.velocity, P.velocity⟩,
    ?_, ?_, PDE.center_mem_euclideanBall _ hr, ?_⟩
  · nlinarith [sq_pos_of_pos hr]
  · nlinarith [sq_pos_of_pos hr]
  · have heq : relativePosition P
        ⟨P.time - r ^ 2 / 2, P.position - (r ^ 2 / 2) • P.velocity, P.velocity⟩ = 0 := by
      ext i
      simp only [relativePosition, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      ring
    rw [heq]
    exact PDE.center_mem_euclideanBall 0 (pow_pos hr 3)

/-- Two points in the same backward cylinder differ in time by less than its squared radius. -/
theorem abs_time_sub_lt_sq {d : ℕ} {P X Y : KineticPoint d} {r : ℝ}
    (hX : X ∈ backwardCylinder P r) (hY : Y ∈ backwardCylinder P r) :
    |X.time - Y.time| < r ^ 2 := by
  rw [abs_lt]
  constructor <;> linarith only [hX.1, hX.2.1, hY.1, hY.2.1]

/-- Relative position at different centers can be compared using a shared point. -/
theorem relativePosition_change_center {d : ℕ} (P Q X Z : KineticPoint d) :
    relativePosition Q X = relativePosition P X - relativePosition P Z +
      relativePosition Q Z + (X.time - Z.time) • (P.velocity - Q.velocity) := by
  ext i
  simp only [relativePosition, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Euclidean velocity separation between intersecting cylinders. -/
theorem velocity_centers_lt {d : ℕ} {P Q Z : KineticPoint d} {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hZP : Z ∈ backwardCylinder P r)
    (hZQ : Z ∈ backwardCylinder Q s) :
    PDE.vecEuclideanNorm (P.velocity - Q.velocity) < r + s := by
  have hP := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr).mp hZP.2.2.1
  have hQ := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hs).mp hZQ.2.2.1
  have heq : P.velocity - Q.velocity =
      -(Z.velocity - P.velocity) + (Z.velocity - Q.velocity) := by abel
  rw [heq]
  calc
    _ ≤ PDE.vecEuclideanNorm (-(Z.velocity - P.velocity)) +
        PDE.vecEuclideanNorm (Z.velocity - Q.velocity) := PDE.vecEuclideanNorm_add_le _ _
    _ < r + s := by rw [PDE.vecEuclideanNorm_neg]; exact add_lt_add hP hQ

/-- A cylinder intersecting another of at least half its radius lies in its eightfold inflation. -/
theorem cylinder_subset_inflation_of_inter {d : ℕ} {P Q : KineticPoint d} {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ 2 * s)
    (hinter : (backwardCylinder P r ∩ backwardCylinder Q s).Nonempty) :
    backwardCylinder P r ⊆ inflatedCylinder Q s 8 := by
  obtain ⟨Z, hZP, hZQ⟩ := hinter
  have hr2 : r ^ 2 ≤ 4 * s ^ 2 := by
    have h := pow_le_pow_left₀ hr.le hrs 2
    nlinarith only [h]
  have hr3 : r ^ 3 ≤ 8 * s ^ 3 := by
    have h := pow_le_pow_left₀ hr.le hrs 3
    nlinarith only [h]
  have hvPQ := velocity_centers_lt hr hs hZP hZQ
  intro X hX
  have htime := abs_time_sub_lt_sq hX hZP
  have hXP := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (pow_pos hr 3)).mp hX.2.2.2
  have hZP' := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
    (pow_pos hr 3)).mp hZP.2.2.2
  have hZQ' := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
    (pow_pos hs 3)).mp hZQ.2.2.2
  simp only [sub_zero] at hXP hZP' hZQ'
  have hpos : PDE.vecEuclideanNorm (relativePosition Q X) < 29 * s ^ 3 := by
    rw [relativePosition_change_center P Q X Z]
    have htri := PDE.vecEuclideanNorm_add_le
      (relativePosition P X - relativePosition P Z + relativePosition Q Z)
      ((X.time - Z.time) • (P.velocity - Q.velocity))
    have htri' := PDE.vecEuclideanNorm_add_le
      (relativePosition P X - relativePosition P Z) (relativePosition Q Z)
    have htri'' := PDE.vecEuclideanNorm_add_le
      (relativePosition P X) (-(relativePosition P Z))
    rw [← sub_eq_add_neg, PDE.vecEuclideanNorm_neg] at htri''
    rw [PDE.vecEuclideanNorm_smul] at htri
    have hprod : |X.time - Z.time| *
        PDE.vecEuclideanNorm (P.velocity - Q.velocity) ≤ 12 * s ^ 3 := by
      calc
        _ ≤ (4 * s ^ 2) * (3 * s) :=
          mul_le_mul (htime.le.trans hr2) (by linarith only [hvPQ, hrs])
            (PDE.vecEuclideanNorm_nonneg _) (by positivity)
        _ = 12 * s ^ 3 := by ring
    linarith only [htri, htri', htri'', hXP, hZP', hZQ', hr3, hprod]
  change X ∈ backwardCylinder (inflationCenter Q s 8) (8 * s)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := (abs_lt.mp htime).1
    simp only [inflationCenter]
    nlinarith only [h, hZQ.1, hr2, sq_pos_of_pos hs]
  · have h := (abs_lt.mp htime).2
    simp only [inflationCenter]
    nlinarith only [h, hZQ.2.1, hr2, sq_pos_of_pos hs]
  · apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity : 0 < 8*s)).mpr
    change PDE.vecEuclideanNorm (X.velocity - Q.velocity) < 8 * s
    have hXPv := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr).mp hX.2.2.1
    have heq : X.velocity - Q.velocity =
        (X.velocity - P.velocity) + (P.velocity - Q.velocity) := by abel
    rw [heq]
    have htri := PDE.vecEuclideanNorm_add_le
      (X.velocity - P.velocity) (P.velocity - Q.velocity)
    linarith only [htri, hXPv, hvPQ, hrs, hs]
  · apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
      (pow_pos (by positivity : 0 < 8*s) 3)).mpr
    rw [sub_zero, relativePosition_inflationCenter]
    nlinarith only [hpos, pow_pos hs 3]

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
