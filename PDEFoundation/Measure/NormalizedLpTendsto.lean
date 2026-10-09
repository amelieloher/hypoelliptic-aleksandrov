module

public import PDEFoundation.Measure.NormalizedLp

/-!
# Convergence between normalized and unnormalized `L^p` norms

On a positive finite-volume domain, normalized and unnormalized `L^p`
convergence are equivalent. The proofs retain the exact volume factors.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open Filter MeasureTheory

/-- Unnormalized `L^p` convergence implies normalized `L^p` convergence on a
positive finite-volume domain. -/
theorem
    tendsto_eLpMeanNormOn_sub_zero_of_tendsto_eLpNormOn_sub_zero
    {ι E : Type*} [NormedAddCommGroup E]
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {F : ι → Vec d → E} {f : Vec d → E} {l : Filter ι}
    (hUPos : 0 < volume U) (hUTop : volume U < ∞)
    (h :
      Tendsto
        (fun i => eLpNormOn U p (F i - f))
        l (𝓝 0)) :
    Tendsto
      (fun i => eLpMeanNormOn U p (F i - f))
      l (𝓝 0) := by
  let C : ℝ≥0∞ :=
    (volume U)⁻¹ ^ (1 / p).toReal
  have hCTop : C ≠ ∞ := by
    dsimp only [C]
    exact
      (ENNReal.rpow_lt_top_of_nonneg
        (by positivity)
        (ENNReal.inv_ne_top.mpr hUPos.ne')).ne
  have hScaled :=
    ENNReal.Tendsto.const_mul
      (a := C) h (Or.inr hCTop)
  simpa only [C, mul_zero,
    eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn
      hUTop] using hScaled

/-- Normalized `L^p` convergence implies unnormalized `L^p` convergence on a
positive finite-volume domain. -/
theorem
    tendsto_eLpNormOn_sub_zero_of_tendsto_eLpMeanNormOn_sub_zero
    {ι E : Type*} [NormedAddCommGroup E]
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {F : ι → Vec d → E} {f : Vec d → E} {l : Filter ι}
    (hUPos : 0 < volume U) (hUTop : volume U < ∞)
    (h :
      Tendsto
        (fun i => eLpMeanNormOn U p (F i - f))
        l (𝓝 0)) :
    Tendsto
      (fun i => eLpNormOn U p (F i - f))
      l (𝓝 0) := by
  let C : ℝ≥0∞ :=
    volume U ^ (1 / p).toReal
  have hCTop : C ≠ ∞ := by
    dsimp only [C]
    exact
      (ENNReal.rpow_lt_top_of_nonneg
        (by positivity) hUTop.ne).ne
  have hScaled :=
    ENNReal.Tendsto.const_mul
      (a := C) h (Or.inr hCTop)
  simpa only [C, mul_zero,
    eLpNormOn_eq_volume_rpow_mul_eLpMeanNormOn
      hUPos hUTop] using hScaled

end PDE
