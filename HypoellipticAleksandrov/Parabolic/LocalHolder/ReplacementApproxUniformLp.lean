module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxL2
public import HypoellipticAleksandrov.Parabolic.HarnackUnitCylinder.CompactLp
public import Mathlib.Topology.ContinuousMap.Compact

/-! # Local L2 convergence of continuous closed-cylinder limits

The ambient extension is used only to name the same continuous function on the closed
carrier. Uniform convergence there gives strong L2 convergence on every interior collar.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set
open scoped Topology

/-- Extend a continuous closed-carrier function by zero to name its ambient values. -/
def continuousMapZeroExtension {d : ℕ} {K : Set (TimeVelocity d)}
    (V : C(K, ℝ)) (z : TimeVelocity d) : ℝ := by
  classical
  exact if hz : z ∈ K then V ⟨z, hz⟩ else 0

/-- The ambient extension retains the prescribed continuous closed-carrier restriction. -/
theorem continuousOn_continuousMapZeroExtension {d : ℕ} {K : Set (TimeVelocity d)}
    (V : C(K, ℝ)) : ContinuousOn (continuousMapZeroExtension V) K := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert V.continuous using 1
  funext z
  simp only [Set.domRestrict_apply, continuousMapZeroExtension, dite_eq_left z.property]

/-- Uniform closed-carrier convergence implies strong restricted L2 convergence. -/
theorem tendsto_local_toLp_of_continuousMap_tendsto {d : ℕ}
    (K S : Set (TimeVelocity d)) [CompactSpace K]
    (hS : IsOpen S) (hSc : IsCompact (closure S)) (hSK : closure S ⊆ K)
    (U : ℕ → C(K, ℝ)) (V : C(K, ℝ)) (hlim : Tendsto U atTop (𝓝 V))
    (u : ℕ → TimeVelocity d → ℝ) (hu : ∀ n, ParabolicMemLpOn S 2 (u n))
    (hueq : ∀ (n : ℕ) (z : K), U n z = u n z) :
    ∃ hv : ParabolicMemLpOn S 2 (continuousMapZeroExtension V),
      Tendsto (fun n => (hu n).toLp (u n)) atTop
        (𝓝 (hv.toLp (continuousMapZeroExtension V))) := by
  have hv := memLp_on_of_continuousOn_compact_closure
    (continuousOn_continuousMapZeroExtension V) hS hSc hSK 2
  let : IsFiniteMeasure (timeVelocityVolumeOn S) := ⟨by
    simpa only [timeVelocityVolumeOn, Measure.restrict_apply_univ] using
      lt_of_le_of_lt (measure_mono subset_closure) hSc.measure_lt_top⟩
  refine ⟨hv, tendsto_toLp_two_of_ae_sub_le (timeVelocityVolumeOn S) u hu
    (continuousMapZeroExtension V) hv (fun n => ‖U n - V‖)
    (fun _ => norm_nonneg _) (tendsto_iff_norm_sub_tendsto_zero.mp hlim) ?_⟩
  intro n
  apply ae_restrict_of_forall_mem hS.measurableSet
  intro z hz
  have hzK := hSK (subset_closure hz)
  have he : u n z - continuousMapZeroExtension V z = (U n - V) ⟨z, hzK⟩ := by
    simp only [continuousMapZeroExtension, dite_eq_left hzK, ContinuousMap.sub_apply,
      hueq n ⟨z, hzK⟩]
  rw [he, ← Real.norm_eq_abs]
  exact (U n - V).norm_coe_le_norm ⟨z, hzK⟩

end HypoellipticAleksandrov.Parabolic.LocalHolder
