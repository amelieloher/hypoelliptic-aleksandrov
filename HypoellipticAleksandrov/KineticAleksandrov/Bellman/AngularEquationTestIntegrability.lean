module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularCoordinatesRadial
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! # Integrability of the literal separated radial and angular test factors -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- A compact positive-radius test has compact support on the positive radial subtype. -/
theorem bellmanRadialTest_compact (ψ : ℝ → ℝ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    HasCompactSupport (fun s : BellmanPositiveTime => ψ s.val) := by
  have hk : IsCompact ((Subtype.val : BellmanPositiveTime → ℝ) ⁻¹' tsupport ψ) := by
    apply Topology.IsInducing.subtypeVal.isCompact_preimage' hc
    intro s hsψ
    exact ⟨⟨s, hs hsψ⟩, rfl⟩
  exact hk.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_comp_subset_preimage ψ continuous_subtype_val)

/-- Dividing a positive-radius compact test by a power of s is integrable for every degree. -/
theorem bellmanRadialTest_integrable (β : ℝ) (ψ : ℝ → ℝ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Ioi (0 : ℝ)) (n : ℕ) :
    Integrable (fun s : BellmanPositiveTime => ψ s.val / s.val ^ n)
      (bellmanRadialWeight β) := by
  have hcont : Continuous (fun s : BellmanPositiveTime => ψ s.val / s.val ^ n) :=
    (hψ.comp continuous_subtype_val).div (continuous_subtype_val.pow n)
      (fun s => pow_ne_zero n s.property.ne')
  apply hcont.integrable_of_hasCompactSupport
  convert! (bellmanRadialTest_compact ψ hc hs).mul_right
    (f' := fun s : BellmanPositiveTime => (s.val ^ n)⁻¹) using 1

/-- Multiplying a compact angular test by a polynomial is integrable for any Radon angular
measure. -/
theorem bellmanAngularTestFactor_integrable (F : Measure ℝ) [IsFiniteMeasureOnCompacts F]
    (ψ : ℝ → ℝ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (n : ℕ) :
    Integrable (fun y => y ^ n * ψ y) F := by
  exact ((continuous_id.pow n).mul hψ).integrable_of_hasCompactSupport hc.mul_left

end HypoellipticAleksandrov.KineticAleksandrov
