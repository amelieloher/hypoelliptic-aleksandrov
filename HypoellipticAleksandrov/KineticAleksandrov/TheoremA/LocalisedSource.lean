module

public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.AssemblySource

/-! # Localized source norms under zero extension -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.TheoremA
open MeasureTheory Set
open scoped ENNReal

/-- Localization to positive solution values commutes with source zero extension on Q. -/
theorem eLpNorm_localized_source_indicator
    {d : ℕ} {Q : Set (KineticPoint d)} (hQ : MeasurableSet Q)
    (f u : KineticPoint d → ℝ) (p : ℝ≥0∞) :
    eLpNorm ({P | 0 < u P}.indicator (fun P => max (Q.indicator f P) 0))
      p (volume.restrict Q) =
    eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0))
      p (volume.restrict Q) := by
  classical
  apply eLpNorm_congr_ae
  filter_upwards [source_indicator_ae_eq hQ f] with P hP
  by_cases hu : 0 < u P
  · simp only [Set.mem_ofPred_eq, hu, Set.indicator_of_mem, hP]
  · simp only [Set.mem_ofPred_eq, hu, not_false_eq_true, Set.indicator_of_notMem]

end HypoellipticAleksandrov.KineticAleksandrov.TheoremA
