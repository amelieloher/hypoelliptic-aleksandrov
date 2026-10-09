module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripRepresentation
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.DomainDominationMeasure
import Mathlib.Topology.Algebra.Support

/-! # Physical finite measures determined by compact interior nonnegative tests -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open Evolution

/-- Physical finite measures supported in an open set agree when all smooth interior tests agree. -/
theorem nested_physical_measure_eq {μ ν : Measure Point} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (D : Set Point) (hD : IsOpen D) (hμ : ∀ᵐ p ∂μ, p ∈ D) (hν : ∀ᵐ p ∂ν, p ∈ D)
    (hprobe : ∀ f : exitProbeSubmodule, tsupport (exitProbePhysical f) ⊆ D →
      (∀ p, 0 ≤ exitProbePhysical f p) →
      (∫ p, exitProbePhysical f p ∂μ) = ∫ p, exitProbePhysical f p ∂ν) : μ = ν := by
  let e := reconstructionPhysicalHomeomorph
  let U := e ⁻¹' D
  let a := μ.map e.symm
  let b := ν.map e.symm
  have hU : IsOpen U := hD.preimage e.continuous
  have hsupport (ρ : Measure Point) (hρ : ∀ᵐ p ∂ρ, p ∈ D) :
      (ρ.map e.symm).restrict U = ρ.map e.symm := by
    apply Measure.restrict_eq_self_of_ae_mem
    apply e.symm.measurableEmbedding.ae_map_iff.mpr
    filter_upwards [hρ] with p hp
    change e (e.symm p) ∈ D
    rwa [e.apply_symm_apply]
  have htest (f : EvolutionVec 1 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
      (hc : HasCompactSupport f) (hs : tsupport f ⊆ U) (hn : ∀ x, 0 ≤ f x) :
      (∫ x, f x ∂a) = ∫ x, f x ∂b := by
    let F : exitProbeSubmodule := ⟨f, hf, hc⟩
    have hFs : tsupport (exitProbePhysical F) ⊆ D := by
      rw [exitProbePhysical, tsupport_comp_eq_preimage]
      intro p hp
      have h := hs hp
      change e (e.symm p) ∈ D at h
      simpa only [e.apply_symm_apply] using h
    have hi := hprobe F hFs (fun p => hn _)
    have hmap (ρ : Measure Point) : (∫ x, f x ∂ρ.map e.symm) =
        ∫ p, exitProbePhysical F p ∂ρ :=
      integral_map e.symm.continuous.measurable.aemeasurable
        hf.continuous.measurable.aestronglyMeasurable
    exact (hmap μ).trans (hi.trans (hmap ν).symm)
  have heq : a = b := by
    apply le_antisymm
    · apply measure_le_of_smooth_integral_le hU (hsupport μ hμ)
      intro f hf hc hs hn
      exact (htest f hf hc hs hn).le
    · apply measure_le_of_smooth_integral_le hU (hsupport ν hν)
      intro f hf hc hs hn
      exact (htest f hf hc hs hn).symm.le
  have hback (ρ : Measure Point) : (ρ.map e.symm).map e = ρ := by
    rw [Measure.map_map e.continuous.measurable e.symm.continuous.measurable]
    have hid : e ∘ e.symm = (id : Point → Point) := funext e.apply_symm_apply
    rw [hid, Measure.map_id]
  exact (hback μ).symm.trans
    ((congrArg (fun ρ : Measure (EvolutionVec 1) => ρ.map e) heq).trans (hback ν))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
