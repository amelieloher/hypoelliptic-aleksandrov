module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.RestartTailStatement
public import Mathlib.Probability.Kernel.RadonNikodym
public import Mathlib.MeasureTheory.Measure.WithDensityFinite

/-! # Jointly measurable densities for finite Green kernels

The finite equivalent reference measure is only a Radon–Nikodym construction
instrument. All resulting densities represent the original reference measure.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

/-- The joint extended density of a finite kernel relative to a sigma-finite reference. -/
def positionKernelDensity {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated X Y]
    (k : Kernel X Y) (m : Measure Y) [SigmaFinite m] : X → Y → ℝ≥0∞ :=
  fun x y => m.toFinite.rnDeriv m y * k.rnDeriv (Kernel.const X m.toFinite) x y

/-- This chosen kernel density is jointly measurable. -/
theorem measurable_positionKernelDensity {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated X Y]
    (k : Kernel X Y) (m : Measure Y) [SigmaFinite m] :
    Measurable (fun p : X × Y => positionKernelDensity k m p.1 p.2) :=
  ((Measure.measurable_rnDeriv m.toFinite m).comp measurable_snd).mul
    (Kernel.measurable_rnDeriv k (Kernel.const X m.toFinite))

/-- Absolute continuity identifies the joint density with each actual kernel measure. -/
theorem withDensity_positionKernelDensity {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace.CountableOrCountablyGenerated X Y]
    (k : Kernel X Y) [IsFiniteKernel k] (m : Measure Y) [SigmaFinite m]
    (x : X) (hx : k x ≪ m) :
    m.withDensity (positionKernelDensity k m x) = k x := by
  let eta := Kernel.const X m.toFinite
  have hxe : k x ≪ eta x := by
    simpa only [eta, Kernel.const_apply] using
      hx.trans (absolutelyContinuous_toFinite m)
  have hk := Kernel.withDensity_rnDeriv_eq (κ := k) (η := eta) hxe
  rw [Kernel.withDensity_apply _ (Kernel.measurable_rnDeriv k eta)] at hk
  change m.toFinite.withDensity (k.rnDeriv eta x) = k x at hk
  change m.withDensity (m.toFinite.rnDeriv m * k.rnDeriv eta x) = k x
  rw [withDensity_mul m (Measure.measurable_rnDeriv m.toFinite m)
    (Kernel.measurable_rnDeriv_right k eta x),
    Measure.withDensity_rnDeriv_eq m.toFinite m (toFinite_absolutelyContinuous m)]
  exact hk

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
