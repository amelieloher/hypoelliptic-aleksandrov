module

public import PDEFoundation.Measure.LpSpace
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Compactly supported continuous functions in restricted scalar `L²`

This module packages a continuous compactly supported scalar function into the
canonical restricted scalar `L²` carrier on an arbitrary raw spatial set.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open MeasureTheory
open scoped ENNReal

/-- Package a continuous compactly supported scalar function in restricted
scalar `L²` on an arbitrary raw spatial carrier. -/
noncomputable def compactlySupportedContinuousToScalarLp
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (q : PDE.Vec d → ℝ) (hq : Continuous q) (hqcompact : HasCompactSupport q) :
    PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
  ((hq.memLp_of_hasCompactSupport hqcompact).restrict Ω).toLp q

/-- The canonical restricted scalar `L²` package agrees almost everywhere with
its supplied continuous compactly supported function. -/
theorem coeFn_compactlySupportedContinuousToScalarLp
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (q : PDE.Vec d → ℝ) (hq : Continuous q) (hqcompact : HasCompactSupport q) :
    ⇑(compactlySupportedContinuousToScalarLp (Ω := Ω) q hq hqcompact) =ᵐ[PDE.volumeOn Ω] q := by
  exact ((hq.memLp_of_hasCompactSupport hqcompact).restrict Ω).coeFn_toLp

/-- A uniformly bounded continuous field supported in a compact carrier has
the corresponding restricted-volume squared-energy bound. -/
theorem integral_sq_le_mul_volumeOn_of_tsupport_subset
    {d : ℕ} {Ω K : Set (PDE.Vec d)}
    (q : PDE.Vec d → ℝ) (hq : Continuous q)
    (hK : IsCompact K) (hqK : tsupport q ⊆ K)
    (C : ℝ) (hqC : ∀ y : PDE.Vec d, ‖q y‖ ≤ C) :
    (∫ y, q y ^ 2 ∂PDE.volumeOn Ω) ≤
      C ^ 2 * (PDE.volumeOn Ω).real K := by
  have hC : 0 ≤ C := by
    exact (norm_nonneg (q 0)).trans (hqC 0)
  have hqcompact : HasCompactSupport q :=
    hK.of_isClosed_subset (isClosed_tsupport q) hqK
  have hqSqInt : Integrable (fun y : PDE.Vec d => q y ^ 2) (PDE.volumeOn Ω) := by
    exact (hq.pow 2).integrable_of_hasCompactSupport (by
      simpa only [pow_two] using hqcompact.mul_left)
  have hKConstInt : IntegrableOn (fun _ : PDE.Vec d => C ^ 2) K (PDE.volumeOn Ω) :=
    integrableOn_const hK.measure_ne_top
  have hboundInt :
      Integrable (K.indicator fun _ : PDE.Vec d => C ^ 2) (PDE.volumeOn Ω) :=
    hKConstInt.integrable_indicator hK.measurableSet
  have hpoint : ∀ y : PDE.Vec d, q y ^ 2 ≤ K.indicator (fun _ => C ^ 2) y := by
    intro y
    by_cases hyK : y ∈ K
    · rw [Set.indicator_of_mem hyK, ← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg (q y)) hC).2 (by
        simpa only [Real.norm_eq_abs] using hqC y)
    · rw [Set.indicator_of_notMem hyK]
      have hyq : q y = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        exact fun hyqSupport => hyK (hqK hyqSupport)
      simp [hyq]
  calc
    (∫ y, q y ^ 2 ∂PDE.volumeOn Ω) ≤
        ∫ y, K.indicator (fun _ => C ^ 2) y ∂PDE.volumeOn Ω :=
      integral_mono hqSqInt hboundInt hpoint
    _ = (PDE.volumeOn Ω).real K * C ^ 2 := by
      simpa only [smul_eq_mul] using
        (integral_indicator_const (C ^ 2) hK.measurableSet)
    _ = C ^ 2 * (PDE.volumeOn Ω).real K := mul_comm _ _

end HypoellipticAleksandrov.Parabolic.Dirichlet
