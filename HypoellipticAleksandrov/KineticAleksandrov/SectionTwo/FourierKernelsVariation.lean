module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.FourierKernelsComposition
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! # Total-variation product bound for Fourier kernel composition -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

/-- Temporal Fourier composition contracts total variation by the largest terminal norm. -/
theorem fourierKernel_totalVariation_composition {d : ℕ}
    (K : MovingFiberKernel (wholeSpace d) (fun _ => 0))
    (hcomp : K.HasComposition MeasurableSet.univ)
    (hcov : IsTranslationCovariantEvolution (wholeSpace d) (fun _ => 0)
      MeasurableSet.univ K)
    (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ) (ξ v : PDE.Vec d) :
    totalVariationNorm (fourierKernel K σ τ (hσr.trans hrτ) ξ v) ≤
      totalVariationNorm (fourierKernel K σ r hσr ξ v) *
        ⨆ v' : PDE.Vec d, totalVariationNorm (fourierKernel K r τ hrτ ξ v') := by
  classical
  let ν := fourierKernel K σ r hσr ξ v
  let ν' := fourierKernel K σ τ (hσr.trans hrτ) ξ v
  let C := ⨆ v' : PDE.Vec d, totalVariationNorm (fourierKernel K r τ hrτ ξ v')
  have hB : ‖ContinuousLinearMap.mul ℝ ℂ‖ₑ ≤ 1 := by
    rw [← ofReal_norm]
    exact (ENNReal.ofReal_le_ofReal
      (LinearMap.mkContinuous₂_norm_le (LinearMap.mul ℝ ℂ) zero_le_one
        (fun x y => by simpa only [LinearMap.mul_apply', one_mul] using norm_mul_le x y))).trans_eq
      ENNReal.ofReal_one
  by_contra hn
  have hlt : totalVariationNorm ν * C < ν'.variation univ := lt_of_not_ge hn
  obtain ⟨P, _, hPd, hPm, hPgt⟩ :=
    VectorMeasure.exists_lt_sum_of_lt_variation ν' MeasurableSet.univ hlt
  have hsum : ∑ E ∈ P, ‖ν' E‖ₑ ≤ totalVariationNorm ν * C := by
    calc
      _ ≤ ∑ E ∈ P, ∫⁻ v', ‖fourierKernel K r τ hrτ ξ v' E‖ₑ ∂ν.variation := by
        apply Finset.sum_le_sum
        intro E hEP
        rw [fourierKernel_composition K hcomp hcov σ r τ hσr hrτ ξ v E (hPm E hEP)]
        exact (VectorMeasure.enorm_integral_le_lintegral_enorm).trans
          (by
            simpa only [one_mul] using
              (mul_le_mul' hB (le_refl
                (∫⁻ v', ‖fourierKernel K r τ hrτ ξ v' E‖ₑ ∂ν.variation))))
      _ = ∫⁻ v', ∑ E ∈ P, ‖fourierKernel K r τ hrτ ξ v' E‖ₑ ∂ν.variation := by
        rw [lintegral_finsetSum P (fun E hEP =>
          (measurable_fourierKernel_apply K r τ hrτ ξ E (hPm E hEP)).enorm)]
      _ ≤ ∫⁻ v', C ∂ν.variation := by
        apply lintegral_mono
        intro v'
        exact (VectorMeasure.le_variation (fourierKernel K r τ hrτ ξ v')
          MeasurableSet.univ (fun E _ => subset_univ E) hPd).trans
          (le_iSup (fun x => totalVariationNorm (fourierKernel K r τ hrτ ξ x)) v')
      _ = totalVariationNorm ν * C := by
        rw [lintegral_const, mul_comm]
  exact (not_lt_of_ge hsum) hPgt

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
