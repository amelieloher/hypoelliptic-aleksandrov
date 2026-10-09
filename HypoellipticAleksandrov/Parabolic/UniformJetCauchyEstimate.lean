module

public import HypoellipticAleksandrov.Parabolic.SobolevGridFTC
public import HypoellipticAleksandrov.Parabolic.FiniteSupportL1L2

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped ENNReal

/-- Coordinate iterated derivatives do not enlarge topological support. -/
theorem coordinateIteratedFDeriv_tsupport_subset
    {d : ℕ} (alpha : TimeVelocityMultiIndex d)
    (f : TimeVelocity d → ℝ) :
    tsupport (TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha f) ⊆
      tsupport f := by
  apply closure_minimal _ isClosed_closure
  intro z hz
  apply support_iteratedFDeriv_subset (f := f) (𝕜 := ℝ) alpha.coordinateList.length
  intro hzero
  exact hz (by
    unfold TimeVelocityMultiIndex.coordinateIteratedFDeriv
    rw [hzero]
    exact ContinuousMultilinearMap.zero_apply _)

/-- The grid-FTC sup estimate with the exact common compact-support constant. -/
theorem abs_le_sqrt_volume_mul_eLpNorm_coordinateIteratedFDeriv_allOnes
    (d : ℕ)
    (K : Set (TimeVelocity d))
    (hK : IsCompact K)
    (f : TimeVelocity d → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfsupp : tsupport f ⊆ K)
    (z : TimeVelocity d) :
    |f z| ≤ Real.sqrt (volume.real K) *
      ENNReal.toReal
        (eLpNorm
          (TimeVelocityMultiIndex.coordinateIteratedFDeriv
            (TimeVelocityMultiIndex.allOnes d) f)
          (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d))) := by
  let g := TimeVelocityMultiIndex.coordinateIteratedFDeriv
    (TimeVelocityMultiIndex.allOnes d) f
  have hfcompact : HasCompactSupport f :=
    hK.of_isClosed_subset (isClosed_tsupport (f := f)) hfsupp
  have hgsupp : Function.support g ⊆ K :=
    (subset_tsupport g).trans
      ((coordinateIteratedFDeriv_tsupport_subset _ f).trans hfsupp)
  have hgcontdiff : ContDiff ℝ (⊤ : ℕ∞) g := by
    rw [contDiff_infty]
    intro m
    unfold g TimeVelocityMultiIndex.coordinateIteratedFDeriv
    have hi := (contDiff_infty.mp hf
      (m + (TimeVelocityMultiIndex.allOnes d).order)).iteratedFDeriv_right
      (m := m)
      (i := (TimeVelocityMultiIndex.allOnes d).coordinateList.length) (by simp)
    exact (contDiff_const (c := ContinuousMultilinearMap.apply ℝ _ _
      (fun i ↦ timeVelocityBasis
        ((TimeVelocityMultiIndex.allOnes d).coordinateList.get i)))).clm_apply hi
  have hgcontinuous : Continuous g := hgcontdiff.continuous
  have hgcompact : HasCompactSupport g :=
    HasCompactSupport.of_support_subset_isCompact hK hgsupp
  have hgmem : MemLp g (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d)) :=
    hgcontinuous.memLp_of_hasCompactSupport hgcompact
  exact (abs_le_integral_abs_coordinateIteratedFDeriv_allOnes d f hf hfcompact z).trans
    (integral_abs_le_sqrt_volume_mul_eLpNorm K hK.measurableSet
      hK.measure_lt_top g hgmem hgsupp)

end HypoellipticAleksandrov.Parabolic
