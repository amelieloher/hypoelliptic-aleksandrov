module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifyNativeMeasure
import Mathlib.Tactic.NormNum

/-! # Retaining a strict height margin under approximate identities -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory Filter
open scoped Topology
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [MeasureSpace G] [BorelSpace G] [FiniteDimensional ℝ G]
  [Measure.IsAddHaarMeasure (volume : Measure G)]

/-- Every continuous spatial trace with a strict height margin retains height one
quarter at the same point for every sufficiently small member of the concrete sequence. -/
theorem mollify_preserves_height_eventually (f : G → ℝ) (hf : Continuous f)
    (q : G) (hq : 5 / 16 < f q) :
    ∀ᶠ n in atTop, 1 / 4 < spatialMollify (standardMollifierSequence n) f q := by
  have he := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := volume) standardMollifierSequence_rOut_tendsto hf q
  apply he.eventually (Ioi_mem_nhds ?_)
  exact lt_trans (by norm_num : (1 / 4 : ℝ) < 5 / 16) hq

/-- Height can be retained while the kernel radius is below any prescribed collar width. -/
theorem exists_mollifier_preserving_height_and_collar (f : G → ℝ) (hf : Continuous f)
    (q : G) (hq : 5 / 16 < f q) (delta : ℝ) (hdelta : 0 < delta) :
    ∃ n : ℕ, 1 / 4 < spatialMollify (standardMollifierSequence n) f q ∧
      (standardMollifierSequence (G := G) n).rOut < delta := by
  have hh := mollify_preserves_height_eventually f hf q hq
  have hr := standardMollifierSequence_rOut_tendsto (G := G)
  have hd := hr.eventually (Iio_mem_nhds hdelta)
  exact (hh.and hd).exists

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
