module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoxConcentrationSetting
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! # The finite physical occupation measure of the actual full-space kernel -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The actual physical terminal kernel as a measurable function of elapsed real time. -/
def physicalElapsedKernel (E : FullSpaceEvolution) (z : Z) : Kernel ℝ Z where
  toFun t := kernelXV E (Real.toNNReal t) z
  measurable' := Measure.measurable_of_measurable_coe _
    (fun s hs => kernelXV_realTime_measurable E z s hs)

/-- The elapsed physical kernel is uniformly sub-Markov, hence finite. -/
instance physicalElapsedKernel_isFinite (E : FullSpaceEvolution) (z : Z) :
    IsFiniteKernel (physicalElapsedKernel E z) :=
  ⟨⟨1, ENNReal.one_lt_top, fun t => kernelXV_mass_le_one E (Real.toNNReal t) z⟩⟩

/-- Occupation is integration of the actual terminal kernel over the source time window. -/
def physicalOccupationMeasure (E : FullSpaceEvolution) (z : Z) (T : ℝ) : Measure Z :=
  physicalElapsedKernel E z ∘ₘ volume.restrict (Ioc 0 T)

/-- Source boxes are evaluated by the exact time integral of physical kernel masses. -/
theorem physicalOccupationMeasure_apply (E : FullSpaceEvolution) (z : Z) (T : ℝ)
    (s : Set Z) (hs : MeasurableSet s) :
    physicalOccupationMeasure E z T s =
      ∫⁻ t in Ioc 0 T, kernelXV E (Real.toNNReal t) z s :=
  Measure.bind_apply hs (physicalElapsedKernel E z).aemeasurable

/-- The actual occupation measure has total mass at most the observation time. -/
theorem physicalOccupationMeasure_mass_le (E : FullSpaceEvolution) (z : Z) (T : ℝ) :
    physicalOccupationMeasure E z T univ ≤ ENNReal.ofReal T := by
  rw [physicalOccupationMeasure_apply _ _ _ _ MeasurableSet.univ]
  apply (lintegral_mono (fun t => kernelXV_mass_le_one E (Real.toNNReal t) z)).trans_eq
  simp only [lintegral_const, one_mul, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]

/-- The conservative full-space kernel gives occupation mass exactly equal to elapsed time. -/
theorem physicalOccupationMeasure_mass_eq {lam Lam : ℝ} (hlam : 0 < lam)
    (A : SmoothAutonomous lam Lam) (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (z : Z) (T : ℝ) : physicalOccupationMeasure E z T univ = ENNReal.ofReal T := by
  rw [physicalOccupationMeasure_apply _ _ _ _ MeasurableSet.univ]
  simp only [kernelXV_mass_one hlam A E hE, lintegral_const, one_mul,
    Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]

/-- Every finite observation window gives a genuinely finite occupation measure. -/
instance physicalOccupationMeasure_isFinite (E : FullSpaceEvolution) (z : Z) (T : ℝ) :
    IsFiniteMeasure (physicalOccupationMeasure E z T) :=
  ⟨(physicalOccupationMeasure_mass_le E z T).trans_lt ENNReal.ofReal_lt_top⟩

/-- Nonnegative occupation integrals equal the literal iterated kernel integral. -/
theorem physicalOccupationMeasure_lintegral (E : FullSpaceEvolution) (z : Z) (T : ℝ)
    (f : Z → ENNReal) (hf : Measurable f) :
    (∫⁻ w, f w ∂physicalOccupationMeasure E z T) =
      ∫⁻ t in Ioc 0 T, ∫⁻ w, f w ∂kernelXV E (Real.toNNReal t) z :=
  Measure.lintegral_bind (physicalElapsedKernel E z).aemeasurable hf.aemeasurable

/-- Integrable signed occupation tests equal the actual iterated kernel integral. -/
theorem physicalOccupationMeasure_integral (E : FullSpaceEvolution) (z : Z) (T : ℝ)
    (f : Z → ℝ) (hf : Integrable f (physicalOccupationMeasure E z T)) :
    (∫ w, f w ∂physicalOccupationMeasure E z T) =
      ∫ t in Ioc 0 T, ∫ w, f w ∂kernelXV E (Real.toNNReal t) z := by
  rw [physicalOccupationMeasure, Measure.comp_eq_comp_const_apply] at hf ⊢
  simpa only [Kernel.const_apply, physicalElapsedKernel, Kernel.coe_mk] using
    ProbabilityTheory.Kernel.integral_comp hf

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
