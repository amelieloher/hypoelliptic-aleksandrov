module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.ReferenceGeometryAffine
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.ReferenceGeometry
import Mathlib.Tactic

/-! # Physical sampling cylinders and comparison regions in the unit domain -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

open Set

/-- The physical sampling cylinder is the affine image of its literal reference cylinder. -/
theorem physical_sampling_image {d : ℕ} (P0 : KineticPoint d) {scale : ℝ}
    (hscale : 0 < scale) (m : ℕ) :
    kineticAffine P0 scale '' samplingCylinder d m =
      backwardCylinder (kineticAffine P0 scale (samplingCenter d m)) scale := by
  rw [samplingCylinder, kineticAffine_image_cylinder P0 _ scale 1 hscale zero_lt_one,
    mul_one]

/-- Every physical sampling subcylinder has an exact positive-radius reference preimage. -/
theorem physical_sampling_subcylinder {d : ℕ} (P0 P : KineticPoint d)
    {scale r : ℝ} (hscale : 0 < scale) (hr : 0 < r) (m : ℕ)
    (hsub : backwardCylinder P r ⊆
      backwardCylinder (kineticAffine P0 scale (samplingCenter d m)) scale) :
    backwardCylinder (kineticAffineInverse P0 scale P) (r / scale) ⊆
      samplingCylinder d m := by
  have hi := kineticAffine_image_cylinder P0 (kineticAffineInverse P0 scale P)
    scale (r / scale) hscale (div_pos hr hscale)
  rw [kineticAffine_apply_inverse P0 hscale.ne', mul_div_cancel₀ r hscale.ne'] at hi
  intro Z hZ
  have hp := hsub (hi ▸ (mem_image_of_mem (kineticAffine P0 scale) hZ))
  rw [← physical_sampling_image P0 hscale m] at hp
  have hp' := (mem_kineticAffine_image_iff P0 _ hscale.ne' _).mp hp
  simpa only [kineticAffineInverse_apply P0 hscale.ne'] using hp'

/-- The local stack-comparison closure lies in the same physical reference closure. -/
theorem physical_sampling_comparison_image_subset {d : ℕ} (P0 P : KineticPoint d)
    {scale r : ℝ} (hscale : 0 < scale) (hr : 0 < r) (m : ℕ)
    (hsub : backwardCylinder P r ⊆
      backwardCylinder (kineticAffine P0 scale (samplingCenter d m)) scale) :
    kineticAffine P r '' stackComparisonRegion d m ⊆
      kineticAffine P0 scale '' referenceRegion d m (referenceBound m) := by
  let Q := kineticAffineInverse P0 scale P
  have hQ := physical_sampling_subcylinder P0 P hscale hr m hsub
  have hi := sampling_comparison_image_subset m Q (div_pos hr hscale) hQ
  have hc : kineticAffine P r = kineticAffine P0 scale ∘ kineticAffine Q (r / scale) := by
    rw [kineticAffine_comp, kineticAffine_apply_inverse P0 hscale.ne',
      mul_div_cancel₀ r hscale.ne']
  rw [hc]
  rintro Z ⟨Y, hY, rfl⟩
  exact ⟨kineticAffine Q (r / scale) Y, hi ⟨Y, hY, rfl⟩, rfl⟩

/-- The local stack-comparison closure lies in the same physical reference closure. -/
theorem physical_sampling_comparison_subset {d : ℕ} (P0 P : KineticPoint d)
    {scale r : ℝ} (hscale : 0 < scale) (hr : 0 < r) (m : ℕ)
    (hsub : backwardCylinder P r ⊆
      backwardCylinder (kineticAffine P0 scale (samplingCenter d m)) scale) :
    closure (kineticAffine P r '' stackComparisonRegion d m) ⊆
      closure (kineticAffine P0 scale '' referenceRegion d m (referenceBound m)) := by
  exact closure_mono (physical_sampling_comparison_image_subset P0 P hscale hr m hsub)

/-- The comparison region contains each entire forward stack, including its top face. -/
theorem forwardStack_subset_comparison {d : ℕ} (P : KineticPoint d) {r : ℝ}
    (hr : 0 < r) (m : ℕ) :
    forwardStack P r m ⊆ kineticAffine P r '' stackComparisonRegion d m := by
  rw [← kineticAffine_image_forwardStack P hr m]
  apply image_mono
  exact subset_closure.trans (stackComparisonRegion_geometry d m).2.2.2

/-- Sampling-cylinder closures remain inside the buffered comparison closure. -/
theorem physical_sampling_closure_subset {d : ℕ} (P0 : KineticPoint d) {scale : ℝ}
    (hscale : 0 < scale) (m : ℕ) :
    closure (backwardCylinder (kineticAffine P0 scale (samplingCenter d m)) scale) ⊆
      closure (kineticAffine P0 scale '' referenceRegion d m (referenceBound m)) := by
  rw [← physical_sampling_image P0 hscale m]
  apply closure_mono
  apply image_mono
  exact subset_closure.trans (sampling_closure_subset_reference d m (referenceBound_large m))

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
