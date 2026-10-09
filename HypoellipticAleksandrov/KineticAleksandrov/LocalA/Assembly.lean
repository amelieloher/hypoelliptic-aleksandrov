module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.AssemblyInner
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.AssemblyGeometry

/-! # The joint Borel estimate, conditional on the smooth joint statement

The constants are selected before all data. Compact correctors give the estimates
on shifted inner cylinders. Fixed fractions are exhausted below the terminal face;
all spatial orders refer to the same original solution.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic Filter Holder
open scoped Topology Matrix.Norms.Elementwise

/-- The smooth joint local estimate implies exactly the Borel joint statement. -/
theorem localTimeVelocityRegularity_of_smooth :
    SmoothLocalRegularityStatement → LocalTimeVelocityRegularityStatement := by
  intro hsmooth hH hLE d hd lam Lam hlam hLam
  obtain ⟨C_m, C, α, hCm, hC, hα, hα1, hest⟩ :=
    hsmooth hH hLE d hd lam Lam hlam hLam
  refine ⟨C_m, C, α, hCm, hC, hα, hα1, ?_⟩
  intro A hA hs hlo hhi P₀ R hR u hc hu he
  have hab : BddAbove (u '' backwardCylinder P₀ R) :=
    ((isCompact_closure_backwardCylinder P₀ R hR).bddAbove_image hc).mono
      (image_mono subset_closure)
  have hbb : BddBelow (u '' backwardCylinder P₀ R) :=
    ((isCompact_closure_backwardCylinder P₀ R hR).bddBelow_image hc).mono
      (image_mono subset_closure)
  have hKD n : closure (backwardCylinder (borelInnerCentre P₀ R n)
      (borelInnerRadius R hR n)) ⊆ backwardCylinder P₀ R := by
    have hh := closure_reflected_innerCylinder_subset P₀ R hR (borelInnerDelta R n)
      (borelInnerDelta_valid R hR n).1 (borelInnerDelta_valid R hR n).2
    rw [kineticReflection_image_innerCylinder] at hh
    exact hh
  have hi n := borel_inner_joint_estimates hH hLE hd lam Lam hlam hLam
    C_m hCm C α hest A hA hs hlo hhi P₀ R hR u hu he
    (borelInnerCentre P₀ R n) (borelInnerRadius R hR n)
    (borelInnerRadius_pos R hR n) (hKD n)
  have hosc n : oscillationOn u (backwardCylinder (borelInnerCentre P₀ R n)
      (borelInnerRadius R hR n)) ≤ oscillationOn u (backwardCylinder P₀ R) :=
    oscillationOn_mono (backwardCylinder_nonempty _ (borelInnerRadius_pos R hR n))
      (subset_closure.trans (hKD n)) hab hbb
  refine ⟨?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨P₁, r, hr, hsub, hPin⟩ :=
      exists_inner_margin_cylinder (isOpen_backwardCylinder P₀ R hR) hP
    exact (borel_inner_joint_estimates hH hLE hd lam Lam hlam hLam C_m hCm C α
      hest A hA hs hlo hhi P₀ R hR u hu he P₁ r hr hsub).1 P hPin |>.1
  · intro m hm P hP
    have hP' : P ∈ backwardCylinder P₀ ((3 / 4 : ℝ) * R) := by
      convert hP using 1; ring
    have hevent := borel_inner_fraction_exhaustion P₀ R hR (3 / 4) (by norm_num) P hP'
    have hb : ∀ᶠ n in atTop,
        (borelInnerRadius R hR n) ^ (3 * m) *
          ‖iteratedFDeriv ℝ m (physicalPositionSlice u P) P.position‖ ≤
            C_m m * oscillationOn u (backwardCylinder P₀ R) := by
      filter_upwards [hevent] with n hn
      have hn' : P ∈ backwardCylinder (borelInnerCentre P₀ R n)
          (3 * borelInnerRadius R hR n / 4) := by
        convert hn using 1; ring
      exact ((hi n).1 P hn').2 m hm |>.trans
        (mul_le_mul_of_nonneg_left (hosc n) (hCm m))
    have ht := ((borelInnerRadius_tendsto R hR).pow (3 * m)).mul_const
      ‖iteratedFDeriv ℝ m (physicalPositionSlice u P) P.position‖
    exact le_of_tendsto ht hb
  · intro P hP Q hQ
    have hP' : P ∈ backwardCylinder P₀ ((1 / 2 : ℝ) * R) := by
      convert hP using 1; ring
    have hQ' : Q ∈ backwardCylinder P₀ ((1 / 2 : ℝ) * R) := by
      convert hQ using 1; ring
    have hp := borel_inner_fraction_exhaustion P₀ R hR (1 / 2) (by norm_num) P hP'
    have hq := borel_inner_fraction_exhaustion P₀ R hR (1 / 2) (by norm_num) Q hQ'
    have hbound : ∀ᶠ n in atTop, |u P - u Q| ≤
        C * oscillationOn u (backwardCylinder P₀ R) *
          (kineticIncrement P₀ P Q / borelInnerRadius R hR n) ^ α := by
      filter_upwards [hp, hq] with n hnP hnQ
      have hnP' : P ∈ backwardCylinder (borelInnerCentre P₀ R n)
          (borelInnerRadius R hR n / 2) := by convert hnP using 1; ring
      have hnQ' : Q ∈ backwardCylinder (borelInnerCentre P₀ R n)
          (borelInnerRadius R hR n / 2) := by convert hnQ using 1; ring
      have hh := (hi n).2 P hnP' Q hnQ'
      have hincr : kineticIncrement (borelInnerCentre P₀ R n) P Q =
          kineticIncrement P₀ P Q := rfl
      rw [hincr] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hosc n) hC.le) (Real.rpow_nonneg
          (div_nonneg (by
            unfold kineticIncrement
            exact add_nonneg
              (add_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
                (PDE.vecEuclideanNorm_nonneg _))
              (Real.rpow_nonneg (PDE.vecEuclideanNorm_nonneg _) _))
            (borelInnerRadius_pos R hR n).le) α))
    have ht := ((tendsto_const_nhds (x := kineticIncrement P₀ P Q)).div
      (borelInnerRadius_tendsto R hR) (ne_of_gt hR)).rpow_const (Or.inr hα.le)
    exact ge_of_tendsto (ht.const_mul (C * oscillationOn u (backwardCylinder P₀ R))) hbound

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
