module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.Inflation
import Mathlib.Tactic

/-! # The time-centered kinetic differentiation basis

The distinguished point is in the interior, rather than on a backward cylinder's top
face. The sets shrink in the ordinary product topology; their volume eccentricity is
not compared with product-metric balls.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set

/-- The top of a time-centered cylinder based at P. -/
def centeredTop {d : ℕ} (P : KineticPoint d) (r : ℝ) : KineticPoint d :=
  ⟨P.time + r ^ 2 / 2, P.position + (r ^ 2 / 2) • P.velocity, P.velocity⟩

/-- The literal time-centered cylinder used for differentiation. -/
def centeredCylinder {d : ℕ} (P : KineticPoint d) (r : ℝ) : Set (KineticPoint d) :=
  backwardCylinder (centeredTop P r) r

/-- Centering preserves the free-transport position coordinate. -/
theorem relativePosition_centeredTop {d : ℕ} (P X : KineticPoint d) (r : ℝ) :
    relativePosition (centeredTop P r) X = relativePosition P X := by
  ext i
  simp only [relativePosition, centeredTop, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

/-- Membership in the centered basis is stated in its physical Euclidean coordinates. -/
theorem mem_centeredCylinder_iff {d : ℕ} (P X : KineticPoint d) {r : ℝ}
    (hr : 0 < r) :
    X ∈ centeredCylinder P r ↔
      |X.time-P.time| < r ^ 2 / 2 ∧
      PDE.vecEuclideanNorm (X.velocity-P.velocity) < r ∧
      PDE.vecEuclideanNorm (relativePosition P X) < r ^ 3 := by
  rw [centeredCylinder, mem_backwardCylinder_iff,
    PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr,
    PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (pow_pos hr 3),
    relativePosition_centeredTop, sub_zero]
  simp only [centeredTop, abs_lt]
  constructor
  · rintro ⟨h1, h2, hv, hx⟩
    exact ⟨⟨by linarith only [h1], by linarith only [h2]⟩, hv, hx⟩
  · rintro ⟨⟨h1, h2⟩, hv, hx⟩
    exact ⟨by linarith only [h1], by linarith only [h2], hv, hx⟩

/-- The distinguished point belongs to each positive centered cylinder. -/
theorem self_mem_centeredCylinder {d : ℕ} (P : KineticPoint d) {r : ℝ}
    (hr : 0 < r) : P ∈ centeredCylinder P r := by
  rw [mem_centeredCylinder_iff P P hr]
  have hz : PDE.vecEuclideanNorm (0 : PDE.Vec d) = 0 :=
    PDE.vecEuclideanNorm_eq_zero_iff.mpr rfl
  simp only [sub_self, abs_zero, relativePosition_self, hz]
  exact ⟨half_pos (sq_pos_of_pos hr), hr, pow_pos hr 3⟩

/-- Relative position plus transport displacement is the physical position difference. -/
theorem position_sub_eq_relative {d : ℕ} (P X : KineticPoint d) :
    X.position-P.position = relativePosition P X + (X.time-P.time) • P.velocity := by
  simp only [relativePosition, sub_add_cancel]

/-- Small centered cylinders have uniformly small Euclidean coordinate displacements. -/
theorem centeredCylinder_coordinate_bounds {d : ℕ} (P : KineticPoint d) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) {X : KineticPoint d}
    (hX : X ∈ centeredCylinder P r) :
    |X.time-P.time| < r ∧
      PDE.vecEuclideanNorm (X.velocity-P.velocity) < r ∧
      PDE.vecEuclideanNorm (X.position-P.position) <
        r*(1+PDE.vecEuclideanNorm P.velocity) := by
  obtain ⟨ht, hv, hx⟩ := (mem_centeredCylinder_iff P X hr).mp hX
  have hr2 : r ^ 2 ≤ r := by nlinarith only [hr, hr1]
  have hr3 : r ^ 3 ≤ r := by
    calc
      r ^ 3 = r ^ 2 * r := by ring
      _ ≤ r * r := mul_le_mul_of_nonneg_right hr2 hr.le
      _ ≤ r := by nlinarith only [hr, hr1]
  have ht' : |X.time-P.time| < r := by linarith only [ht, hr2, hr]
  refine ⟨ht', hv, ?_⟩
  rw [position_sub_eq_relative]
  calc
    _ ≤ PDE.vecEuclideanNorm (relativePosition P X) +
        PDE.vecEuclideanNorm ((X.time-P.time) • P.velocity) :=
      PDE.vecEuclideanNorm_add_le _ _
    _ = PDE.vecEuclideanNorm (relativePosition P X) +
        |X.time-P.time| *PDE.vecEuclideanNorm P.velocity := by
      rw [PDE.vecEuclideanNorm_smul]
    _ < r + r*PDE.vecEuclideanNorm P.velocity :=
      add_lt_add_of_lt_of_le (hx.trans_le hr3)
        (mul_le_mul_of_nonneg_right ht'.le (PDE.vecEuclideanNorm_nonneg _))
    _ = r*(1+PDE.vecEuclideanNorm P.velocity) := by ring

/-- The centered kinetic basis eventually fits in every ordinary metric neighborhood. -/
theorem centeredCylinder_subset_ball {d : ℕ} (P : KineticPoint d) {eps : ℝ}
    (heps : 0 < eps) :
    ∃ r0 : ℝ, 0 < r0 ∧ ∀ r : ℝ, 0 < r → r < r0 →
      centeredCylinder P r ⊆ Metric.ball P eps := by
  let L := 1 + PDE.vecEuclideanNorm P.velocity
  have hL : 0 < L := by dsimp [L]; linarith [PDE.vecEuclideanNorm_nonneg P.velocity]
  have hL1 : 1 ≤ L := by dsimp [L]; linarith [PDE.vecEuclideanNorm_nonneg P.velocity]
  refine ⟨min 1 (eps/L), lt_min zero_lt_one (div_pos heps hL), ?_⟩
  intro r hr hrr X hX
  have hr1 : r ≤ 1 := (hrr.trans_le (min_le_left _ _)).le
  have hrL : r*L < eps := (lt_div_iff₀ hL).mp (hrr.trans_le (min_le_right _ _))
  obtain ⟨ht, hv, hx⟩ := centeredCylinder_coordinate_bounds P hr hr1 hX
  have hrle : r ≤ r*L := by nlinarith only [hr.le, hL1]
  have hpos : dist X.position P.position < eps := by
    rw [dist_eq_norm]
    exact (PDE.norm_le_vecEuclideanNorm _).trans_lt (hx.trans hrL)
  have hvel : dist X.velocity P.velocity < eps := by
    rw [dist_eq_norm]
    exact (PDE.norm_le_vecEuclideanNorm _).trans_lt (hv.trans_le hrle |>.trans hrL)
  rw [Metric.mem_ball, ← (KineticPoint.isometryEquivProd d).dist_eq]
  change max (dist X.time P.time)
    (max (dist X.position P.position) (dist X.velocity P.velocity)) < eps
  rw [max_lt_iff, max_lt_iff, Real.dist_eq]
  exact ⟨ht.trans_le hrle |>.trans hrL, hpos, hvel⟩

/-- Every sufficiently small centered cylinder stays in a prescribed open neighborhood. -/
theorem centeredCylinder_eventually_subset_open {d : ℕ} {U : Set (KineticPoint d)}
    (hU : IsOpen U) {P : KineticPoint d} (hP : P ∈ U) :
    ∃ r0 : ℝ, 0 < r0 ∧ ∀ r : ℝ, 0 < r → r < r0 → centeredCylinder P r ⊆ U := by
  obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.mp hU P hP
  obtain ⟨r0, hr0, hsmall⟩ := centeredCylinder_subset_ball P heps
  exact ⟨r0, hr0, fun r hr hrr => (hsmall r hr hrr).trans hball⟩

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
