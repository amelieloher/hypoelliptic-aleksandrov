module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ClassicalTerminalWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.PastGluingLocality
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! # Extension from interior limits and uniform boundary traces -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov Set Filter Classical
open scoped Topology

/-- An interior continuous function extends continuously when its boundary traces converge
uniformly to a supplied continuous boundary function. -/
theorem continuousOn_interior_patch {α : Type*} [TopologicalSpace α]
    (U S : Set α) (hU : IsOpen U) (hUS : U ⊆ S) (V w : α → ℝ)
    (hV : ContinuousOn V U) (hw : ContinuousOn w S)
    (htrace : ∀ p ∈ S, p ∉ U → ∀ η : ℝ, 0 < η →
      ∃ O : Set α, IsOpen O ∧ p ∈ O ∧ ∀ q ∈ O ∩ U, |V q - w p| ≤ η) :
    ContinuousOn (fun p => if p ∈ U then V p else w p) S := by
  classical
  intro p hp
  by_cases hi : p ∈ U
  · have he : (fun q => if q ∈ U then V q else w q) =ᶠ[𝓝 p] V := by
      filter_upwards [hU.mem_nhds hi] with q hq
      simp only [ite_eq_left hq]
    exact ((hV p hi).continuousAt (hU.mem_nhds hi)).continuousWithinAt.congr_of_eventuallyEq
      (he.filter_mono nhdsWithin_le_nhds) (by simp [hi])
  · have _hUS := hUS
    change Tendsto _ (𝓝[S] p) (𝓝 _)
    simp only [ite_eq_right hi]
    apply Metric.tendsto_nhds.mpr
    intro η hη
    obtain ⟨O, hO, hpO, hbound⟩ := htrace p hp hi (η / 2) (by positivity)
    have hw' := Metric.tendsto_nhds.mp (hw p hp) η hη
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hO.mem_nhds hpO), hw'] with q hq hqw
    by_cases hqi : q ∈ U
    · rw [ite_eq_left hqi, Real.dist_eq]
      exact (hbound q ⟨hq, hqi⟩).trans_lt (by linarith)
    · simpa only [ite_eq_right hqi] using hqw

end HypoellipticAleksandrov.KineticAleksandrov
