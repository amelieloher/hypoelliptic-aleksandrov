module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileGeTwoHomogeneity
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileHomogeneousBounds
import Mathlib.Tactic.Linarith

/-! # Local integrability of the higher-dimensional profile jets -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Set

/-- All classical profile jets are locally integrable, including at the origin. -/
theorem profile_classical_jets_locallyIntegrable (d : ℕ) (hd : 1 ≤ d)
    (H : XV d → ℝ) (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1)
    (hhom : ∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q)
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ : Set (XV d))) :
    (∀ i, LocallyIntegrable (fun q => dx H q i) volume) ∧
    (∀ i, LocallyIntegrable (fun q => dv H q i) volume) ∧
    (∀ i k, LocallyIntegrable (fun q => dvv H q i k) volume) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply homogeneous_component_locallyIntegrable_off_origin d hd (fun q => dx H q i)
      ((measurable_pi_apply i).comp (measurable_dx H))
      (alpha - 3) (by linarith) (by linarith)
    · intro r hr q hq
      exact homogeneous_dx_identity H alpha r hr (hhom r hr) q
        (differentiableAt_profile_off_origin H hs q hq)
        (differentiableAt_profile_off_origin H hs _ (dilate_ne_zero r hr q hq)) i
    · intro K hK hz
      obtain ⟨M, hM⟩ := profile_jets_compact_bound H hs K hK hz
      refine ⟨M, ?_⟩
      intro q hq
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (dx H q) i).trans (hM q hq).1
  · intro i
    apply homogeneous_component_locallyIntegrable_off_origin d hd (fun q => dv H q i)
      ((measurable_pi_apply i).comp (measurable_dv H))
      (alpha - 1) (by linarith) (by linarith)
    · intro r hr q hq
      exact homogeneous_dv_identity H alpha r hr (hhom r hr) q
        (differentiableAt_profile_off_origin H hs q hq)
        (differentiableAt_profile_off_origin H hs _ (dilate_ne_zero r hr q hq)) i
    · intro K hK hz
      obtain ⟨M, hM⟩ := profile_jets_compact_bound H hs K hK hz
      refine ⟨M, ?_⟩
      intro q hq
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (dv H q) i).trans (hM q hq).2.1
  · intro i k
    apply homogeneous_component_locallyIntegrable_off_origin d hd (fun q => dvv H q i k)
      (measurable_dvv H i k) (alpha - 2) (by linarith) (by linarith)
    · intro r hr q hq
      exact homogeneous_dvv_off_origin H alpha r hr (hhom r hr) hs q hq i k
    · intro K hK hz
      obtain ⟨M, hM⟩ := profile_jets_compact_bound H hs K hK hz
      exact ⟨M, fun q hq => (hM q hq).2.2 i k⟩

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
