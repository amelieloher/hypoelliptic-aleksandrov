module

public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.Tactic

/-! # Riesz reconstruction from limits of all compactly supported tests -/

@[expose] public section
noncomputable section
open Set MeasureTheory Filter Topology
open scoped CompactlySupported
namespace HypoellipticAleksandrov.KineticAleksandrov

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]

/-- Actual limits of compact tests reconstruct a positive Radon measure. -/
theorem bellman_riesz_of_test_limits (mu : ℕ → Measure X)
    [∀ n, IsFiniteMeasureOnCompacts (mu n)]
    (ht : ∀ f : C_c(X, ℝ), ∃ a : ℝ,
      Tendsto (fun n => ∫ x, f x ∂mu n) atTop (𝓝 a)) :
    ∃ nu : Measure X, IsFiniteMeasureOnCompacts nu ∧ Measure.InnerRegular nu ∧
      ∀ f : C_c(X, ℝ),
        Tendsto (fun n => ∫ x, f x ∂mu n) atTop (𝓝 (∫ x, f x ∂nu)) := by
  choose L hL using ht
  have hi (n : ℕ) (f : C_c(X, ℝ)) : Integrable f (mu n) :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  let ell : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
    { toFun := L
      map_add' := fun f g => by
        apply tendsto_nhds_unique (hL (f + g))
        convert! (hL f).add (hL g) using 1
        ext n
        exact integral_add (hi n f) (hi n g)
      map_smul' := fun c f => by
        apply tendsto_nhds_unique (hL (c • f))
        convert! (hL f).const_smul c using 1
        ext n
        exact integral_smul c f
      monotone' := fun f g hfg =>
        le_of_tendsto_of_tendsto' (hL f) (hL g) (fun n => integral_mono (hi n f) (hi n g) hfg) }
  let nu := RealRMK.rieszMeasure ell
  refine ⟨nu, inferInstance, ?_, ?_⟩
  · infer_instance
  · intro f
    rw [RealRMK.integral_rieszMeasure ell f]
    exact hL f

end HypoellipticAleksandrov.KineticAleksandrov
