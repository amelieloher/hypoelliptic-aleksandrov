module

public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotient
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Directed spatial difference-quotient bounds

This module converts a bound on the Fréchet derivative in one native velocity
coordinate into a signed forward spatial difference-quotient bound.  The
zero-step case is included without assuming the bound is nonnegative.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open scoped Convex

/-- A signed spatial difference quotient is bounded by the corresponding directed
spatial Fréchet derivative along its coordinate segment. -/
theorem abs_spatialDifferenceQuotient_le_of_segment_spatialFDeriv_bound
    {d : ℕ} {f : TimeVelocity d → ℝ} {M h : ℝ}
    {k : Fin d} {z : TimeVelocity d}
    (hdiff : ∀ w ∈ [z -[ℝ] spatialShift k h z], DifferentiableAt ℝ f w)
    (hdir : ∀ w ∈ [z -[ℝ] spatialShift k h z],
      |(fderiv ℝ f w) (0, PDE.basisVec k)| ≤ M) :
    |spatialDifferenceQuotient k h f z| ≤ M := by
  by_cases hzero : h = 0
  · subst h
    have hMnonneg : 0 ≤ M :=
      (abs_nonneg ((fderiv ℝ f z) (0, PDE.basisVec k))).trans
        (hdir z (left_mem_segment ℝ z (spatialShift k 0 z)))
    simpa only [spatialDifferenceQuotient_apply, spatialTranslate_apply,
      spatialShift_zero, id_eq, sub_self, zero_div, abs_zero] using hMnonneg
  · obtain ⟨w, hw, hMVT⟩ :=
      domain_mvt (s := [z -[ℝ] spatialShift k h z]) (f := f) (f' := fderiv ℝ f)
        (fun w hw => (hdiff w hw).hasFDerivAt.hasFDerivWithinAt)
        (convex_segment z (spatialShift k h z))
        (left_mem_segment ℝ z (spatialShift k h z))
        (right_mem_segment ℝ z (spatialShift k h z))
    have hshift_sub : spatialShift k h z - z = h • (0, PDE.basisVec k) := by
      simp only [spatialShift, add_sub_cancel_left, Prod.smul_mk, smul_zero]
    have hMVT' : f (spatialShift k h z) - f z =
        h * (fderiv ℝ f w) (0, PDE.basisVec k) := by
      rw [hMVT, hshift_sub]
      simp only [map_smul, smul_eq_mul]
    rw [spatialDifferenceQuotient_apply, spatialTranslate_apply, abs_div, hMVT', abs_mul]
    calc
      (|h| * |(fderiv ℝ f w) (0, PDE.basisVec k)|) / |h| =
          |(fderiv ℝ f w) (0, PDE.basisVec k)| :=
        mul_div_cancel_left₀ _ (abs_ne_zero.mpr hzero)
      _ ≤ M := hdir w hw

/-- Directed spatial derivative bounds on a containing set give uniform signed
spatial difference-quotient bounds on a source carrier. -/
theorem abs_spatialDifferenceQuotient_le_of_spatialFDeriv_bound
    {d : ℕ} {S Q : Set (TimeVelocity d)} {f : TimeVelocity d → ℝ}
    {δ M : ℝ}
    (hseg : ∀ (k : Fin d) (h : ℝ) (z : TimeVelocity d),
      |h| ≤ δ → z ∈ S → [z -[ℝ] spatialShift k h z] ⊆ Q)
    (hdiff : ∀ w ∈ Q, DifferentiableAt ℝ f w)
    (hdir : ∀ (k : Fin d) (w : TimeVelocity d), w ∈ Q →
      |(fderiv ℝ f w) (0, PDE.basisVec k)| ≤ M) :
    ∀ (k : Fin d) (h : ℝ) (z : TimeVelocity d),
      |h| ≤ δ → z ∈ S → |spatialDifferenceQuotient k h f z| ≤ M := by
  intro k h z hh hz
  exact abs_spatialDifferenceQuotient_le_of_segment_spatialFDeriv_bound
    (fun w hw => hdiff w (hseg k h z hh hz hw))
    (fun w hw => hdir k w (hseg k h z hh hz hw))

end HypoellipticAleksandrov.Parabolic
