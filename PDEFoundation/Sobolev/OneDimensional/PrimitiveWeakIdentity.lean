module

public import PDEFoundation.Sobolev.OneDimensional.Primitive
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Scalar weak identity for one-dimensional interval primitives

This file proves the bounded scalar distributional identity underlying the
one-dimensional Sobolev bridge.  It is deliberately scalar: transport to the
native `Vec 1` weak-derivative interface belongs in a separate foundational
measure-equivalence file.
-/

@[expose] public section

namespace PDE

open MeasureTheory Set

noncomputable section

/-- On an oriented interval with ordered endpoints, the interval primitive is
the corresponding closed-interval set integral. -/
theorem intervalPrimitive_eq_setIntegral_Icc
    {r x : ℝ} (hrx : r ≤ x) (g : ℝ → ℝ) :
    intervalPrimitive r g x = ∫ y in Icc r x, g y := by
  rw [intervalPrimitive, intervalIntegral.integral_of_le hrx,
    ← integral_Icc_eq_integral_Ioc]

/-- Triangular Fubini on a closed real interval. -/
theorem setIntegral_setIntegral_Icc_swap
    {r R : ℝ} {g ψ : ℝ → ℝ}
    (hg : IntegrableOn g (Icc r R) volume)
    (hψ : ContinuousOn ψ (Icc r R)) :
    ∫ x in Icc r R, (∫ y in Icc r x, g y * ψ x) =
      ∫ y in Icc r R, (∫ x in Icc y R, g y * ψ x) := by
  let I : Set ℝ := Icc r R
  let μ : Measure ℝ := volume.restrict I
  let T : Set (ℝ × ℝ) := {z | z.1 ≤ z.2}
  have hT : MeasurableSet T :=
    (isClosed_le continuous_fst continuous_snd).measurableSet
  have hgμ : Integrable g μ := by
    simpa only [μ, I] using! hg
  have hψμ : Integrable ψ μ := by
    simpa only [μ, I] using! hψ.integrableOn_Icc
  have hprod : Integrable (fun z : ℝ × ℝ => g z.1 * ψ z.2) (μ.prod μ) :=
    hgμ.mul_prod hψμ
  have htriangle : Integrable (T.indicator (fun z : ℝ × ℝ => g z.1 * ψ z.2))
      (μ.prod μ) :=
    hprod.indicator hT
  have hleft :
      (∫ x, ∫ y, T.indicator (fun z : ℝ × ℝ => g z.1 * ψ z.2) (y, x) ∂μ ∂μ) =
        ∫ x in Icc r R, (∫ y in Icc r x, g y * ψ x) := by
    rw [show (∫ x, ∫ y, T.indicator (fun z : ℝ × ℝ => g z.1 * ψ z.2) (y, x) ∂μ ∂μ) =
        ∫ x in I, ∫ y, T.indicator (fun z : ℝ × ℝ => g z.1 * ψ z.2) (y, x) ∂μ ∂volume by
          rfl]
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    change (∫ y, T.indicator (fun z : ℝ × ℝ => g z.1 * ψ z.2) (y, x) ∂μ) = _
    have hsection :
        (fun y => T.indicator (fun z : ℝ × ℝ => g z.1 * ψ z.2) (y, x)) =
          (Iic x).indicator (fun y => g y * ψ x) := by
      funext y
      by_cases hyx : y ≤ x
      · rw [Set.indicator_of_mem (show (y, x) ∈ T by exact hyx),
          Set.indicator_of_mem (show y ∈ Iic x by exact hyx)]
      · rw [Set.indicator_of_notMem (show (y, x) ∉ T by exact hyx),
          Set.indicator_of_notMem (show y ∉ Iic x by exact hyx)]
    rw [hsection, integral_indicator measurableSet_Iic]
    change (∫ y, g y * ψ x ∂(volume.restrict I).restrict (Iic x)) = _
    rw [Measure.restrict_restrict measurableSet_Iic]
    have hIx : Iic x ∩ I = Icc r x := by
      ext y
      simp only [I, mem_inter_iff, mem_Icc, mem_Iic]
      constructor
      · intro hy
        exact ⟨hy.2.1, hy.1⟩
      · intro hy
        exact ⟨hy.2, ⟨hy.1, hy.2.trans hx.2⟩⟩
    rw [hIx]
  have hright :
      (∫ y, ∫ x, T.indicator (fun z : ℝ × ℝ => g z.1 * ψ z.2) (y, x) ∂μ ∂μ) =
        ∫ y in Icc r R, (∫ x in Icc y R, g y * ψ x) := by
    rw [show (∫ y, ∫ x, T.indicator (fun z : ℝ × ℝ => g z.1 * ψ z.2) (y, x) ∂μ ∂μ) =
        ∫ y in I, ∫ x, T.indicator (fun z : ℝ × ℝ => g z.1 * ψ z.2) (y, x) ∂μ ∂volume by
          rfl]
    apply setIntegral_congr_fun measurableSet_Icc
    intro y hy
    change (∫ x, T.indicator (fun z : ℝ × ℝ => g z.1 * ψ z.2) (y, x) ∂μ) = _
    have hsection :
        (fun x => T.indicator (fun z : ℝ × ℝ => g z.1 * ψ z.2) (y, x)) =
          (Ici y).indicator (fun x => g y * ψ x) := by
      funext x
      by_cases hyx : y ≤ x
      · rw [Set.indicator_of_mem (show (y, x) ∈ T by exact hyx),
          Set.indicator_of_mem (show x ∈ Ici y by exact hyx)]
      · rw [Set.indicator_of_notMem (show (y, x) ∉ T by exact hyx),
          Set.indicator_of_notMem (show x ∉ Ici y by exact hyx)]
    rw [hsection, integral_indicator measurableSet_Ici]
    change (∫ x, g y * ψ x ∂(volume.restrict I).restrict (Ici y)) = _
    rw [Measure.restrict_restrict measurableSet_Ici]
    have hIy : Ici y ∩ I = Icc y R := by
      ext x
      simp only [I, mem_inter_iff, mem_Icc, mem_Ici]
      constructor
      · intro hx
        exact ⟨hx.1, hx.2.2⟩
      · intro hx
        exact ⟨hx.1, ⟨hy.1.trans hx.1, hx.2⟩⟩
    rw [hIy]
  calc
    ∫ x in Icc r R, (∫ y in Icc r x, g y * ψ x) =
        ∫ x, ∫ y, T.indicator (fun z : ℝ × ℝ => g z.1 * ψ z.2) (y, x) ∂μ ∂μ :=
      hleft.symm
    _ = ∫ y, ∫ x, T.indicator (fun z : ℝ × ℝ => g z.1 * ψ z.2) (y, x) ∂μ ∂μ :=
      integral_integral_swap htriangle.swap
    _ = ∫ y in Icc r R, (∫ x in Icc y R, g y * ψ x) := hright

/-- A compactly supported `C¹` test function has the expected derivative
tail integral on a collar containing its support. -/
theorem setIntegral_deriv_tail_eq_neg
    {r R y : ℝ} (hy : y ∈ Icc r R) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hsupp : tsupport φ ⊆ Ioo r R) :
    ∫ x in Icc y R, deriv φ x = -φ y := by
  have hRzero : φ R = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hR
    exact (not_lt_of_ge le_rfl) (hsupp hR).2
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hy.2,
    intervalIntegral.integral_deriv_of_contDiffOn_Icc hφ.contDiffOn hy.2,
    hRzero]
  ring

/-- The bounded scalar distributional identity for an interval primitive.
This is intentionally not yet the native-vector weak-derivative theorem. -/
theorem intervalPrimitive_scalar_weak_identity_Icc
    {r R : ℝ} {g : ℝ → ℝ}
    (hg : IntegrableOn g (Icc r R) volume) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hsupp : tsupport φ ⊆ Ioo r R) :
    ∫ x in Icc r R, intervalPrimitive r g x * deriv φ x =
      -∫ x in Icc r R, g x * φ x := by
  rw [show (∫ x in Icc r R, intervalPrimitive r g x * deriv φ x) =
      ∫ x in Icc r R, ∫ y in Icc r x, g y * deriv φ x by
        apply setIntegral_congr_fun measurableSet_Icc
        intro x hx
        change intervalPrimitive r g x * deriv φ x =
          (∫ y in Icc r x, g y * deriv φ x)
        rw [intervalPrimitive_eq_setIntegral_Icc hx.1]
        rw [integral_mul_const]
    , setIntegral_setIntegral_Icc_swap hg
      (hφ.continuous_deriv (by simp)).continuousOn]
  have htail : ∀ y ∈ Icc r R, ∫ x in Icc y R, g y * deriv φ x = - (g y * φ y) := by
    intro y hy
    rw [integral_const_mul, setIntegral_deriv_tail_eq_neg hy hφ hsupp]
    ring
  rw [show (∫ y in Icc r R, ∫ x in Icc y R, g y * deriv φ x) =
      ∫ y in Icc r R, -(g y * φ y) by
        apply setIntegral_congr_fun measurableSet_Icc
        exact htail]
  rw [integral_neg]

/-- The bounded scalar weak identity on the open interval.  Atomlessness of
real volume makes the endpoint choice immaterial. -/
theorem intervalPrimitive_scalar_weak_identity_Ioo
    {a b : ℝ} {g : ℝ → ℝ}
    (hg : IntegrableOn g (Icc a b) volume) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hsupp : tsupport φ ⊆ Ioo a b) :
    ∫ x in Ioo a b, intervalPrimitive a g x * deriv φ x =
      -∫ x in Ioo a b, g x * φ x := by
  simpa only [restrict_Ioo_eq_restrict_Icc] using
    (intervalPrimitive_scalar_weak_identity_Icc hg hφ hsupp)

end

end PDE
