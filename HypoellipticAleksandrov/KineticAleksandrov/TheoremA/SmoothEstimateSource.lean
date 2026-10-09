module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! # Full and localized source norms on an open cylinder -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.TheoremA
open Set MeasureTheory
open scoped ENNReal

/-- Localizing a nonnegative source to the positive set does not increase its real Lp norm. -/
theorem localized_positive_source_norm_le {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [BorelSpace α] (μ : Measure α) {Q : Set α} (hQ : IsOpen Q)
    (u f : α → ℝ) (hu : ContinuousOn u Q) (p : ℝ≥0∞)
    (hLp : MemLp (fun x => max (f x) 0) p (μ.restrict Q)) :
    (eLpNorm ({x | 0 < u x}.indicator (fun x => max (f x) 0)) p (μ.restrict Q)).toReal ≤
      (eLpNorm (fun x => max (f x) 0) p (μ.restrict Q)).toReal := by
  classical
  have hs : MeasurableSet (Q ∩ {x | 0 < u x}) :=
    (hu.isOpen_inter_preimage hQ isOpen_Ioi).measurableSet
  have heq : (Q ∩ {x | 0 < u x}).indicator (fun x => max (f x) 0)
      =ᵐ[μ.restrict Q] {x | 0 < u x}.indicator (fun x => max (f x) 0) := by
    filter_upwards [ae_restrict_mem hQ.measurableSet] with x hx
    simp only [indicator, mem_inter_iff, hx, true_and]
  rw [← eLpNorm_congr_ae heq]
  exact ENNReal.toReal_mono hLp.eLpNorm_ne_top
    (eLpNorm_indicator_le _ hs)

end HypoellipticAleksandrov.KineticAleksandrov.TheoremA
