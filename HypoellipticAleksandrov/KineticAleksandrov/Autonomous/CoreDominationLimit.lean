module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationRemainder
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Removing a positive measure remainder from finite decompositions -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter
open scoped Topology

/-- Finite positive decompositions become an exact measure sum when remainder mass vanishes. -/
theorem measure_eq_sum_of_remainder_mass_tendsto_zero (mu : Measure Point)
    (piece remainder : ℕ → Measure Point)
    (hsplit : ∀ N, mu = ∑ n ∈ Finset.range N, piece n + remainder N)
    (hr : Tendsto (fun N => remainder N univ) atTop (𝓝 0)) :
    mu = Measure.sum piece := by
  ext B hB
  have hrB : Tendsto (fun N => remainder N B) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hr
      (fun _ => zero_le) (fun _ => measure_mono (subset_univ B))
  have hsum := (ENNReal.tendsto_nat_tsum (fun n => piece n B)).add hrB
  have he (N : ℕ) : mu B = (∑ n ∈ Finset.range N, piece n B) + remainder N B := by
    rw [hsplit N, Measure.add_apply, Measure.finsetSum_apply]
  have hc : Tendsto (fun _N : ℕ => mu B) atTop (𝓝 ((∑' n, piece n B) + 0)) :=
    hsum.congr (fun N => (he N).symm)
  rw [Measure.sum_apply _ hB]
  simpa only [add_zero] using tendsto_nhds_unique tendsto_const_nhds hc

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
