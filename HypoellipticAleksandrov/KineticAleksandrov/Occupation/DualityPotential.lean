module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.DualityMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelGreen
public import HypoellipticAleksandrov.Measure.TimeVelocity
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Occupation integration and the parabolic potential

The projected measure's smooth-source pairing is the initial-measure integral of the
Duhamel potential at time zero. The endpoint conjugate norm is exactly the source ABP norm.
-/

@[expose] public section
noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set SectionTwo
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open scoped ENNReal

variable {d : ℕ}

/-- Smooth-source occupation integration is integration of the zero-time potential. -/
theorem integral_unitOccupationMeasure_eq_potential (K : WholeKernel d)
    (ρ : Measure (PDE.Vec d)) [IsFiniteMeasure ρ] (F : TimeVelocity d → ℝ)
    (hFs : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F) :
    (∫ q, F q ∂unitOccupationMeasure K ρ) =
      ∫ v, parabolicDuhamelPotential K MeasurableSet.univ 1 F (0, v) ∂ρ := by
  have hΩm : MeasurableSet (wholeSpace d) := MeasurableSet.univ
  have hFm := hFs.continuous.measurable
  obtain ⟨M, hM⟩ := hFs.continuous.bounded_above_of_compact_support hFc
  rw [integral_unitOccupationMeasure K ρ F hFm ⟨M, fun q => by simpa using hM q⟩]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun v => ?_
  change (∫ τ : ElapsedTime (ENNReal.ofReal (1 : ℝ)),
    ∫ w, F (τ.1, w) ∂K.firstMarginal
      (wholeSpaceQuery 0 (0 + τ.1) (le_add_of_nonneg_right τ.2.1.le) v 0)
    ∂elapsedVolume (ENNReal.ofReal (1 : ℝ))) =
    parabolicDuhamelPotential K hΩm 1 F (0, v)
  have hint (τ : ElapsedTime (ENNReal.ofReal (1 : ℝ))) :
      (∫ w, F (τ.1, w) ∂K.firstMarginal
        (wholeSpaceQuery 0 (0 + τ.1) (le_add_of_nonneg_right τ.2.1.le) v 0)) =
      parabolicDuhamelIntegrand K MeasurableSet.univ F (0, v) τ.1 := by
    rw [parabolicDuhamelIntegrand_of_valid K MeasurableSet.univ F (0, v) τ.1
      ⟨τ.2.1.le, by rw [movingDomain_wholeSpace]; exact mem_univ v⟩,
      parabolicSourceIntegral_eq_master K MeasurableSet.univ F 0 τ.1 τ.2.1.le
        ⟨v, by rw [movingDomain_wholeSpace]; exact mem_univ v⟩
        (hFm.comp (measurable_const.prodMk measurable_id))]
    unfold MovingFiberKernel.firstMarginal
    rw [ProbabilityTheory.Kernel.fst_apply,
      integral_map (f := fun w => F (τ.1, w)) measurable_fst.aemeasurable
      (hFm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable]
    simp only [parabolicMasterIntegral, wholeSpaceQuery, zero_add]
  rw [integral_congr_ae (Filter.Eventually.of_forall hint)]
  have htime : Measurable (fun r => parabolicDuhamelIntegrand K
      MeasurableSet.univ F (0, v) r) := by
    exact (measurable_parabolicDuhamelIntegrand K MeasurableSet.univ
      continuous_const F hFm).comp (measurable_const.prodMk measurable_id)
  rw [integral_elapsed_eq 1 zero_lt_one _ htime]
  change (∫ r in Ioo 0 1, parabolicDuhamelIntegrand K hΩm F (0, v) r) =
    ∫ r in Ioc 0 1, parabolicDuhamelIntegrand K hΩm F (0, v) r
  exact (integral_Ioc_eq_integral_Ioo).symm

/-- The endpoint density exponent is strictly greater than one in positive dimension. -/
theorem occupation_endpoint_gt_one (hd : 0 < d) : 1 < ((d : ℝ) + 1) / d := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  exact (lt_div_iff₀ hdR).2 (by linarith)

/-- The endpoint conjugate exponent is exactly `d+1`. -/
theorem occupation_endpoint_conjugate (hd : 0 < d) :
    (((d : ℝ) + 1) / d) / ((((d : ℝ) + 1) / d) - 1) = (d : ℝ) + 1 := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp
  ring

/-- An interior-supported source has the same full-space and slab conjugate norms. -/
theorem parabolicLpNorm_eq_slab (hd : 0 < d) (F : TimeVelocity d → ℝ)
    (hF : tsupport F ⊆ Ioo (0 : ℝ) 1 ×ˢ univ) :
    parabolicLpNorm d F =
      (eLpNorm F (ENNReal.ofReal
        ((((d : ℝ) + 1) / d) / ((((d : ℝ) + 1) / d) - 1)))
        (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ univ))).toReal := by
  rw [occupation_endpoint_conjugate hd]
  have he : ENNReal.ofReal ((d : ℝ) + 1) = parabolicExponent d := by
    simp [parabolicExponent, ENNReal.ofReal_add, Nat.cast_nonneg]
  rw [he]
  have hind : (Ioo (0 : ℝ) 1 ×ˢ univ).indicator F = F :=
    indicator_eq_self.2 ((Function.support_subset_iff').2 fun q hq =>
      image_eq_zero_of_notMem_tsupport (fun h => hq (hF h)))
  unfold parabolicLpNorm parabolicELpNorm
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_Ioo.prod MeasurableSet.univ), hind]

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
