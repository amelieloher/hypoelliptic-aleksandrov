module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.BoundarySaturationGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.DelayedUnion
import Mathlib.Tactic

/-! # A geometric envelope for delayed stacks -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set MeasureTheory

/-- Round product boxes use native Euclidean spatial and velocity balls. -/
def roundBox (d : ℕ) (a b R : ℝ) : Set (KineticPoint d) :=
  {X | a < X.time ∧ X.time < b ∧
    X.position ∈ PDE.euclideanBall 0 R ∧ X.velocity ∈ PDE.euclideanBall 0 1}

/-- The top center with any interior velocity belongs to the cylinder closure. -/
theorem top_mem_closure_cylinder {d : ℕ} (P : KineticPoint d) {r : ℝ} (hr : 0 < r)
    {v : PDE.Vec d} (hv : v ∈ PDE.euclideanBall P.velocity r) :
    (⟨P.time, P.position, v⟩ : KineticPoint d) ∈ closure (backwardCylinder P r) := by
  let f : ℝ → KineticPoint d := fun t =>
    ⟨t, P.position+(t-P.time) • P.velocity, v⟩
  have hf : Continuous f := KineticPoint.continuous_mk continuous_id
    (continuous_const.add ((continuous_id.sub continuous_const).smul continuous_const))
    continuous_const
  have hsub : f '' Ioo (P.time-r^2) P.time ⊆ backwardCylinder P r := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨ht.1, ht.2, hv, ?_⟩
    have heq : relativePosition P (f t) = 0 := by
      ext i
      simp only [relativePosition, f, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.zero_apply,
        smul_eq_mul]
      ring
    rw [heq]
    exact PDE.center_mem_euclideanBall 0 (pow_pos hr 3)
  have ht : P.time ∈ closure (Ioo (P.time-r^2) P.time) := by
    rw [closure_Ioo (sub_lt_self _ (sq_pos_of_pos hr)).ne]
    exact ⟨by linarith [sq_nonneg r], le_rfl⟩
  have h := closure_mono hsub
    (hf.continuousOn.image_closure (mem_image_of_mem f ht))
  simpa only [f, sub_self, zero_smul, add_zero] using h

/-- A cylinder inside Q has bounded top time, position center, and velocity center. -/
theorem cylinder_subset_unit_center_bounds {d : ℕ} {P : KineticPoint d} {r : ℝ}
    (hr : 0 < r) (hsub : backwardCylinder P r ⊆ unitCylinder d) :
    -1 ≤ P.time ∧ P.time ≤ 0 ∧ PDE.vecEuclideanNorm P.position ≤ 1 ∧
      PDE.vecEuclideanNorm P.velocity < 1 := by
  have htop := closure_mono hsub
    (top_mem_closure_cylinder P hr (PDE.center_mem_euclideanBall _ hr))
  have hb := closure_cylinder_bounds (⟨0,0,0⟩ : KineticPoint d) 1 htop
  have hp : PDE.vecNormSq P.position ≤ 1 := by
    simpa only [relativePosition, sub_zero, smul_zero, one_pow] using hb.2.2.2
  have hpn := PDE.vecEuclideanNorm_nonneg P.position
  have hs := PDE.vecEuclideanNorm_sq P.position
  obtain ⟨Y, hY⟩ := cylinder_nonempty P hr
  let Z : KineticPoint d := ⟨Y.time, Y.position, P.velocity⟩
  have hZ : Z ∈ backwardCylinder P r :=
    ⟨hY.1, hY.2.1, PDE.center_mem_euclideanBall _ hr, hY.2.2.2⟩
  have hv := ((mem_unitCylinder_iff Z).mp (hsub hZ)).2.2.1
  refine ⟨?_, ?_, by nlinarith, hv⟩
  · simpa only [one_pow, zero_sub] using hb.1
  · exact hb.2.1

/-- Every velocity in the source velocity ball of a subcylinder lies in the unit ball. -/
theorem velocity_ball_subset_unit {d : ℕ} {P : KineticPoint d} {r : ℝ}
    (hr : 0 < r) (hsub : backwardCylinder P r ⊆ unitCylinder d)
    {v : PDE.Vec d} (hv : v ∈ PDE.euclideanBall P.velocity r) :
    PDE.vecEuclideanNorm v < 1 := by
  obtain ⟨Y, hY⟩ := cylinder_nonempty P hr
  let Z : KineticPoint d := ⟨Y.time, Y.position, v⟩
  have hZ : Z ∈ backwardCylinder P r := ⟨hY.1, hY.2.1, hv, hY.2.2.2⟩
  exact ((mem_unitCylinder_iff Z).mp (hsub hZ)).2.2.1

/-- A delayed stack lies in the time-spatial leakage envelope. -/
theorem forwardStack_subset_roundBox {d : ℕ} {P : KineticPoint d} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R ≤ 1)
    (hsub : backwardCylinder P r ⊆ unitCylinder d) (m : ℕ) (hm : 0 < m) :
    forwardStack P r m ⊆ roundBox d (-1) ((m : ℝ)*R^2) (1+4*(m : ℝ)*R^2) := by
  obtain ⟨htlo, hthi, hx, hv⟩ := cylinder_subset_unit_center_bounds hr hsub
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hr1 := hrR.le.trans hR
  intro Z hZ
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hz : 0 < Z.time-P.time := hZ.1
    linarith
  · have hz := hZ.2.1
    have hs : r^2 < R^2 := by nlinarith
    nlinarith
  · rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity), sub_zero]
    have hy := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
      (by positivity : 0 < ((m+2 : ℕ) : ℝ)*r^3)).mp hZ.2.2.2
    rw [sub_zero] at hy
    have heq : Z.position = P.position+relativePosition P Z+(Z.time-P.time) • P.velocity := by
      ext i
      simp only [relativePosition, Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
      ring
    have hn₁ := PDE.vecEuclideanNorm_add_le P.position (relativePosition P Z)
    have hn₂ := PDE.vecEuclideanNorm_add_le (P.position+relativePosition P Z)
      ((Z.time-P.time) • P.velocity)
    rw [PDE.vecEuclideanNorm_smul, abs_of_pos hZ.1] at hn₂
    have hprod : (Z.time-P.time)*PDE.vecEuclideanNorm P.velocity ≤ (m : ℝ)*r^2 := by
      nlinarith only [hZ.2.1, hv, hZ.1, PDE.vecEuclideanNorm_nonneg P.velocity]
    have hc : r^3 ≤ r^2 := by nlinarith [sq_nonneg r]
    have hs : r^2 ≤ R^2 := by nlinarith
    have hm1 : 1 ≤ (m : ℝ) := by exact_mod_cast hm
    push_cast at hy
    rw [heq]
    nlinarith
  · rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt zero_lt_one, sub_zero]
    exact velocity_ball_subset_unit hr hsub hZ.2.2.1

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
