module

public import HypoellipticAleksandrov.Parabolic.Geometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Measures and norms on time--velocity space

This module records the product Lebesgue normalization on time--velocity
space, identifies cylinders differing only by their terminal time slice, and
defines the exact `L^(d + 1)` norms used by the parabolic ABP estimate.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- Product Lebesgue volume is an additive Haar measure on time--velocity space. -/
instance timeVelocityVolumeIsAddHaar (d : ℕ) :
    Measure.IsAddHaarMeasure (volume : Measure (TimeVelocity d)) := by
  rw [Measure.volume_eq_prod]
  exact Measure.prod.instIsAddHaarMeasure _ _

/-- Product Lebesgue volume on time--velocity space has its exact factorization. -/
theorem volume_timeVelocity_eq_prod (d : ℕ) :
    (volume : Measure (TimeVelocity d)) =
      (volume : Measure ℝ).prod (volume : Measure (PDE.Vec d)) :=
  Measure.volume_eq_prod ℝ (PDE.Vec d)

/-- The terminal open-ball slice of a parabolic cylinder has zero volume. -/
theorem terminalSlice_volume_zero {d : ℕ} (T : ℝ) (y₀ : PDE.Vec d) :
    volume ({T} ×ˢ PDE.euclideanBall y₀ 1 : Set (TimeVelocity d)) = 0 := by
  rw [Measure.volume_eq_prod]
  simp

/-- The analytic and reachable parabolic cylinders agree almost everywhere. -/
theorem parabolicInterior_ae_eq_reachable {d : ℕ} (T : ℝ) (y₀ : PDE.Vec d) :
    parabolicInterior T y₀ =ᵐ[volume] parabolicReachable T y₀ := by
  change (Ioo 0 T ×ˢ PDE.euclideanBall y₀ 1 : Set (TimeVelocity d)) =ᵐ[volume]
    Ioc 0 T ×ˢ PDE.euclideanBall y₀ 1
  rw [Measure.volume_eq_prod]
  exact Measure.set_prod_ae_eq Ioo_ae_eq_Ioc (EventuallyEq.rfl)

/-- Restricting volume to the analytic or reachable cylinder gives the same measure. -/
theorem parabolicInterior_restrict_eq_reachable {d : ℕ} (T : ℝ) (y₀ : PDE.Vec d) :
    (volume : Measure (TimeVelocity d)).restrict (parabolicInterior T y₀) =
      volume.restrict (parabolicReachable T y₀) :=
  Measure.restrict_congr_set (parabolicInterior_ae_eq_reachable T y₀)

/-- Nonnegative set integrals are unchanged by including the terminal time slice. -/
theorem setLIntegral_parabolicInterior_eq_reachable {d : ℕ}
    (T : ℝ) (y₀ : PDE.Vec d) (f : TimeVelocity d → ℝ≥0∞) :
    (∫⁻ z in parabolicInterior T y₀, f z ∂volume) =
      ∫⁻ z in parabolicReachable T y₀, f z ∂volume := by
  exact congrArg (fun μ : Measure (TimeVelocity d) => ∫⁻ z, f z ∂μ)
    (parabolicInterior_restrict_eq_reachable T y₀)

/-- Real-valued set integrals are unchanged by including the terminal time slice. -/
theorem setIntegral_parabolicInterior_eq_reachable {d : ℕ}
    (T : ℝ) (y₀ : PDE.Vec d) (f : TimeVelocity d → ℝ) :
    (∫ z in parabolicInterior T y₀, f z ∂volume) =
      ∫ z in parabolicReachable T y₀, f z ∂volume := by
  exact congrArg (fun μ : Measure (TimeVelocity d) => ∫ z, f z ∂μ)
    (parabolicInterior_restrict_eq_reachable T y₀)

/-- The finite exponent `d + 1` in the parabolic ABP estimate. -/
def parabolicExponent (d : ℕ) : ℝ≥0∞ := d + 1

/-- The extended-real `L^(d + 1)` norm on all time--velocity space. -/
def parabolicELpNorm (d : ℕ) (f : TimeVelocity d → ℝ) : ℝ≥0∞ :=
  eLpNorm f (parabolicExponent d) volume

/-- The `ENNReal.toReal` encoding of the extended-real `L^(d + 1)` norm on all
time--velocity space. It agrees with the usual finite real `L^(d + 1)` norm whenever
`parabolicELpNorm d f ≠ ∞`, in particular under `MemLp f (parabolicExponent d) volume`. -/
def parabolicLpNorm (d : ℕ) (f : TimeVelocity d → ℝ) : ℝ :=
  (parabolicELpNorm d f).toReal

/-- The extended-real `L^(d + 1)` norm restricted to a time--velocity set. -/
def parabolicELpNormOn (d : ℕ) (f : TimeVelocity d → ℝ)
    (s : Set (TimeVelocity d)) : ℝ≥0∞ :=
  eLpNorm f (parabolicExponent d) (volume.restrict s)

/-- The `ENNReal.toReal` encoding of the extended-real `L^(d + 1)` norm restricted to a
time--velocity set. It agrees with the usual finite real `L^(d + 1)` norm whenever
`parabolicELpNormOn d f s ≠ ∞`, in particular under
`MemLp f (parabolicExponent d) (volume.restrict s)`. -/
def parabolicLpNormOn (d : ℕ) (f : TimeVelocity d → ℝ)
    (s : Set (TimeVelocity d)) : ℝ :=
  (parabolicELpNormOn d f s).toReal

/-- The extended-real restricted norm is unchanged by including the terminal slice. -/
theorem parabolicELpNormOn_parabolicInterior_eq_reachable {d : ℕ}
    (T : ℝ) (y₀ : PDE.Vec d) (f : TimeVelocity d → ℝ) :
    parabolicELpNormOn d f (parabolicInterior T y₀) =
      parabolicELpNormOn d f (parabolicReachable T y₀) := by
  unfold parabolicELpNormOn
  rw [parabolicInterior_restrict_eq_reachable]

/-- The real restricted norm is unchanged by including the terminal slice. -/
theorem parabolicLpNormOn_parabolicInterior_eq_reachable {d : ℕ}
    (T : ℝ) (y₀ : PDE.Vec d) (f : TimeVelocity d → ℝ) :
    parabolicLpNormOn d f (parabolicInterior T y₀) =
      parabolicLpNormOn d f (parabolicReachable T y₀) := by
  unfold parabolicLpNormOn
  rw [parabolicELpNormOn_parabolicInterior_eq_reachable]

end

end HypoellipticAleksandrov.Parabolic
