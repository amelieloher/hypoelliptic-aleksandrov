module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.MeasureDerivativeTriangle
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.MeasureDerivativePrimitiveIntegrable
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Tactic

/-! # The actual distributional derivative of a weighted measure primitive -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- A weighted measure primitive satisfies the weak derivative identity on a test collar. -/
theorem bellmanMeasurePrimitive_weak_Icc (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (g : ℝ → ℝ) (hg : Continuous g) (r R : ℝ) (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hs : tsupport φ ⊆ Ioo r R) :
    (∫ x in Icc r R, bellmanMeasurePrimitive μ g r x * deriv φ x) =
      -∫ z in Ioc r R, g z * φ z ∂μ := by
  have hφd := (contDiff_infty_iff_deriv.mp hφ).2
  have hR : φ R = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => (lt_irrefl R) (hs h).2)
  have he : (∫ x in Icc r R, bellmanMeasurePrimitive μ g r x * deriv φ x) =
      ∫ x in Icc r R, ∫ z in Ioc r x, g z * deriv φ x ∂μ := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    change bellmanMeasurePrimitive μ g r x * deriv φ x =
      ∫ z in Ioc r x, g z * deriv φ x ∂μ
    rw [bellmanMeasurePrimitive, intervalIntegral.integral_of_le hx.1, integral_mul_const]
  rw [he, bellman_measure_triangle_swap μ r R g (deriv φ) hg hφd.continuous]
  have ht : (∫ z in Ioc r R, (∫ x in Icc z R, g z * deriv φ x) ∂μ) =
      ∫ z in Ioc r R, -(g z * φ z) ∂μ := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro z hz
    change (∫ x in Icc z R, g z * deriv φ x) = -(g z * φ z)
    rw [integral_const_mul, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hz.2,
      intervalIntegral.integral_deriv_of_contDiffOn_Icc
        (hφ.of_le (by simp : (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞))).contDiffOn hz.2,
      hR]
    ring
  rw [ht, integral_neg]

/-- The primitive based at zero has exactly the weighted measure as its distributional
derivative. -/
theorem bellmanMeasurePrimitive_weak (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (g : ℝ → ℝ) (hg : Continuous g) (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcφ : HasCompactSupport φ) :
    (∫ x, bellmanMeasurePrimitive μ g 0 x * deriv φ x) = -∫ x, g x * φ x ∂μ := by
  by_cases hn : (tsupport φ).Nonempty
  · obtain ⟨r₀, _, hmin⟩ := hcφ.exists_isMinOn hn continuousOn_id
    obtain ⟨R₀, _, hmax⟩ := hcφ.exists_isMaxOn hn continuousOn_id
    let r := r₀ - 1
    let R := R₀ + 1
    have hs : tsupport φ ⊆ Ioo r R := by
      intro x hx
      have hl : r₀ ≤ x := hmin hx
      have hr : x ≤ R₀ := hmax hx
      dsimp [r, R]
      constructor <;> linarith
    have hdr : tsupport (deriv φ) ⊆ Ioo r R := tsupport_deriv_subset.trans hs
    have hφd := (contDiff_infty_iff_deriv.mp hφ).2
    have hr0 : φ r = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => (lt_irrefl r) (hs h).1)
    have hR0 : φ R = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => (lt_irrefl R) (hs h).2)
    have hlhs : (∫ x, bellmanMeasurePrimitive μ g 0 x * deriv φ x) =
        ∫ x in Icc r R, bellmanMeasurePrimitive μ g 0 x * deriv φ x := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (f := deriv φ)
        (fun hd => hx ⟨(hdr hd).1.le, (hdr hd).2.le⟩), mul_zero]
    have hrhs : (∫ x, g x * φ x ∂μ) = ∫ x in Ioc r R, g x * φ x ∂μ := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (f := φ)
        (fun hd => hx ⟨(hs hd).1, (hs hd).2.le⟩), mul_zero]
    have he : (∫ x in Icc r R, bellmanMeasurePrimitive μ g 0 x * deriv φ x) =
        ∫ x in Icc r R, bellmanMeasurePrimitive μ g r x * deriv φ x := by
      have hi : IntegrableOn (fun x => bellmanMeasurePrimitive μ g 0 x * deriv φ x)
          (Icc r R) volume :=
        ((bellmanMeasurePrimitive_locallyIntegrable μ g hg).integrableOn_isCompact
          isCompact_Icc).mul_continuousOn hφd.continuous.continuousOn isCompact_Icc
      have hc : IntegrableOn (fun x => bellmanMeasurePrimitive μ g 0 r * deriv φ x)
          (Icc r R) volume :=
        (hφd.continuous.continuousOn.integrableOn_Icc).const_mul _
      have hfun : (fun x => bellmanMeasurePrimitive μ g r x * deriv φ x) =
          (fun x => bellmanMeasurePrimitive μ g 0 x * deriv φ x -
            bellmanMeasurePrimitive μ g 0 r * deriv φ x) := by
        funext x
        have hp := bellmanMeasurePrimitive_sub μ g hg 0 r x
        change bellmanMeasurePrimitive μ g 0 x - bellmanMeasurePrimitive μ g 0 r =
          bellmanMeasurePrimitive μ g r x at hp
        rw [← hp]
        ring
      have hle : r ≤ R := by
        obtain ⟨x, hx⟩ := hn
        exact (hs hx).1.le.trans (hs hx).2.le
      have hdInt : (∫ x in Icc r R, deriv φ x) = 0 := by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle,
          intervalIntegral.integral_deriv_of_contDiffOn_Icc
            (hφ.of_le (by simp : (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞))).contDiffOn hle,
          hr0, hR0, sub_self]
      rw [hfun, integral_sub hi hc, integral_const_mul, hdInt, mul_zero, sub_zero]
    rw [hlhs, hrhs, he]
    exact bellmanMeasurePrimitive_weak_Icc μ g hg r R φ hφ hs
  · have hz : φ = 0 := by
      funext x
      exact image_eq_zero_of_notMem_tsupport (fun hx => hn ⟨x, hx⟩)
    rw [hz, deriv_zero]
    simp only [Pi.zero_apply, mul_zero, integral_zero, neg_zero]

end HypoellipticAleksandrov.KineticAleksandrov
