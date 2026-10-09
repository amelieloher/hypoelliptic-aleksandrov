module

public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! # All-order bounds for convolution with a compact smooth Banach-valued density -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open MeasureTheory
open scoped Convolution

/-- Every convolution derivative is bounded by the corresponding density derivative integral. -/
theorem convolution_iteratedFDeriv_bound
    {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure V) [μ.IsAddHaarMeasure] [μ.IsNegInvariant]
    (f : V → E) (hf : LocallyIntegrable f μ) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ y, ‖f y‖ ≤ M) (n : ℕ)
    {E' F : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L : E →L[ℝ] E' →L[ℝ] F) (g : V → E')
    (hc : HasCompactSupport g) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x : V) :
    ‖iteratedFDeriv ℝ n (f ⋆[L, μ] g) x‖ ≤
      ‖L‖ * M * ∫ y, ‖iteratedFDeriv ℝ n g y‖ ∂μ := by
  induction n generalizing E' F with
  | zero =>
    simp only [norm_iteratedFDeriv_zero]
    calc
      ‖(f ⋆[L, μ] g) x‖ ≤ ∫ y, ‖L (f y) (g (x - y))‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ y, (‖L‖ * M) * ‖g (x - y)‖ ∂μ := by
        apply integral_mono
        · exact (hc.convolutionExists_right L hf hg.continuous x).norm
        · exact ((hg.continuous.integrable_of_hasCompactSupport hc).norm.comp_sub_left x)
            |>.const_mul _
        · intro y
          exact (L.le_opNorm₂ _ _).trans
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hb y) (norm_nonneg L)) (norm_nonneg _))
      _ = ‖L‖ * M * ∫ y, ‖g y‖ ∂μ := by
        rw [integral_const_mul]
        congr 1
        exact integral_sub_left_eq_self (fun y => ‖g y‖) μ x
  | succ n ih =>
    have hgd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ g) := hg.fderiv_right (by simp)
    have hdf : fderiv ℝ (f ⋆[L, μ] g) = f ⋆[L.precompR V, μ] fderiv ℝ g := by
      funext y
      exact (hc.hasFDerivAt_convolution_right L hf (hg.of_le (by simp)) y).fderiv
    rw [← norm_iteratedFDeriv_fderiv, hdf]
    have hi := ih (L.precompR V) (fderiv ℝ g) (hc.fderiv ℝ) hgd
    simp only [norm_iteratedFDeriv_fderiv] at hi
    exact hi.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (L.norm_precompR_le V) hM)
      (integral_nonneg fun _ => norm_nonneg _))

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
