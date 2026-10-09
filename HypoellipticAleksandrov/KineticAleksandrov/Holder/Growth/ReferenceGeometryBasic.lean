module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.ReferenceGeometryBuffer
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Tactic

/-! # Literal sampling cylinder and topology of the buffered reference box -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

open Set

/-- The source's reference sampling center before its small dilation. -/
def samplingCenter (d m : ℕ) : KineticPoint d := ⟨-((m : ℝ) + 2), 0, 0⟩

/-- The source's reference sampling cylinder before its small dilation. -/
def samplingCylinder (d m : ℕ) : Set (KineticPoint d) :=
  backwardCylinder (samplingCenter d m) 1

/-- The buffered reference region is open in physical coordinates. -/
theorem isOpen_referenceRegion (d m : ℕ) (L : ℝ) : IsOpen (referenceRegion d m L) :=
  (isOpen_lt continuous_const continuous_time).inter
    ((isOpen_lt continuous_time continuous_const).inter
      ((isOpen_lt (PDE.continuous_vecEuclideanNorm.comp continuous_position)
        continuous_const).inter
        (isOpen_lt (PDE.continuous_vecEuclideanNorm.comp continuous_velocity)
          continuous_const)))

/-- A finite rectangular envelope bounds the reference region. -/
theorem isBounded_referenceRegion (d m : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    Bornology.IsBounded (referenceRegion d m L) := by
  let E : Set (KineticPoint d) := (KineticPoint.equivProd d) ⁻¹'
    (Icc (-((m : ℝ) + 5)) 0 ×ˢ
      (PDE.euclideanClosedBall (0 : PDE.Vec d) L ×ˢ
        PDE.euclideanClosedBall (0 : PDE.Vec d) L))
  have hc : IsCompact E := (KineticPoint.homeomorphProd d).isCompact_preimage.mpr
    (isCompact_Icc.prod ((PDE.isCompact_euclideanClosedBall _ hL).prod
      (PDE.isCompact_euclideanClosedBall _ hL)))
  apply hc.isBounded.subset
  intro P hP
  refine ⟨⟨hP.1.le, hP.2.1.le⟩, ?_, ?_⟩
  · apply (PDE.mem_euclideanClosedBall_iff_vecEuclideanNorm_le hL).mpr
    change PDE.vecEuclideanNorm (P.position - 0) ≤ L
    simpa only [sub_zero] using hP.2.2.1.le
  · apply (PDE.mem_euclideanClosedBall_iff_vecEuclideanNorm_le hL).mpr
    change PDE.vecEuclideanNorm (P.velocity - 0) ≤ L
    simpa only [sub_zero] using hP.2.2.2.le

/-- Sampling closure coordinates have the exact unit Euclidean bounds. -/
theorem sampling_closure_bounds (d m : ℕ) (P : KineticPoint d)
    (hP : P ∈ closure (samplingCylinder d m)) :
    -((m : ℝ) + 3) ≤ P.time ∧ P.time ≤ -((m : ℝ) + 2) ∧
      PDE.vecEuclideanNorm P.position ≤ 1 ∧ PDE.vecEuclideanNorm P.velocity ≤ 1 := by
  have hb := Covering.closure_cylinder_bounds (samplingCenter d m) 1 hP
  simp only [samplingCenter, relativePosition, sub_zero, smul_zero, one_pow] at hb
  refine ⟨by linarith only [hb.1], hb.2.1, ?_, ?_⟩
  · have hn := PDE.vecEuclideanNorm_nonneg P.position
    have hs := PDE.vecEuclideanNorm_sq P.position
    nlinarith only [hn, hs, hb.2.2.2]
  · have hn := PDE.vecEuclideanNorm_nonneg P.velocity
    have hs := PDE.vecEuclideanNorm_sq P.velocity
    nlinarith only [hn, hs, hb.2.2.1]

/-- The added time buffer strictly encloses the entire sampling-cylinder closure. -/
theorem sampling_closure_subset_reference (d m : ℕ) {L : ℝ} (hL : 1 < L) :
    closure (samplingCylinder d m) ⊆ referenceRegion d m L := by
  intro P hP
  obtain ⟨htlo, htup, hx, hv⟩ := sampling_closure_bounds d m P hP
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  exact ⟨by linarith only [htlo], by linarith only [htup, hm],
    hx.trans_lt hL, hv.trans_lt hL⟩

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
