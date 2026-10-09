module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.ReferenceGeometryBasic
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.LeakageGeometry
import Mathlib.Tactic

/-! # Center and radius bounds for cylinders in the reference sampling cylinder -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

open Set

/-- The free-transport center at the bottom time belongs to the cylinder closure. -/
theorem bottom_mem_closure_cylinder {d : ℕ} (P : KineticPoint d) {r : ℝ} (hr : 0 < r) :
    (⟨P.time - r ^ 2, P.position + (-r ^ 2) • P.velocity, P.velocity⟩ : KineticPoint d) ∈
      closure (backwardCylinder P r) := by
  let f : ℝ → KineticPoint d := fun t =>
    ⟨t, P.position + (t - P.time) • P.velocity, P.velocity⟩
  have hf : Continuous f := KineticPoint.continuous_mk continuous_id
    (continuous_const.add ((continuous_id.sub continuous_const).smul continuous_const))
    continuous_const
  have hsub : f '' Ioo (P.time - r ^ 2) P.time ⊆ backwardCylinder P r := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨ht.1, ht.2, PDE.center_mem_euclideanBall _ hr, ?_⟩
    have heq : relativePosition P (f t) = 0 := by
      ext i
      simp only [relativePosition, f, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
        Pi.zero_apply, smul_eq_mul]
      ring
    rw [heq]
    exact PDE.center_mem_euclideanBall 0 (pow_pos hr 3)
  have ht : P.time - r ^ 2 ∈ closure (Ioo (P.time - r ^ 2) P.time) := by
    rw [closure_Ioo (sub_lt_self _ (sq_pos_of_pos hr)).ne]
    exact ⟨le_rfl, sub_le_self _ (sq_nonneg r)⟩
  have h := closure_mono hsub
    (hf.continuousOn.image_closure (mem_image_of_mem f ht))
  simpa only [f, sub_sub_cancel_left] using h

/-- Subcylinders have radius at most one and centers in the bounded sampling closure. -/
theorem sampling_subcylinder_bounds {d : ℕ} (m : ℕ) (P : KineticPoint d) {r : ℝ}
    (hr : 0 < r) (hsub : backwardCylinder P r ⊆ samplingCylinder d m) :
    r ≤ 1 ∧ -((m : ℝ) + 3) ≤ P.time ∧ P.time ≤ -((m : ℝ) + 2) ∧
      PDE.vecEuclideanNorm P.position ≤ 1 ∧ PDE.vecEuclideanNorm P.velocity ≤ 1 := by
  have hc := closure_mono hsub
    (Covering.top_mem_closure_cylinder P hr (PDE.center_mem_euclideanBall _ hr))
  have hb := sampling_closure_bounds d m P hc
  have hbottom := (sampling_closure_bounds d m _
    (closure_mono hsub (bottom_mem_closure_cylinder P hr))).1
  have hr2 : r ^ 2 ≤ 1 := by linarith only [hbottom, hb.2.1]
  exact ⟨by nlinarith only [hr2, hr], hb⟩

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
