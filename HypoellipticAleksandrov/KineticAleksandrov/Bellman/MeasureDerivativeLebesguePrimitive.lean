module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDensitiesContinuity
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
import PDEFoundation.Sobolev.OneDimensional.PrimitiveWeakIdentity
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Tactic

/-! # Lebesgue primitives of locally integrable angular fluxes -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- The oriented Lebesgue primitive of a locally integrable function is locally absolutely
continuous. -/
theorem bellman_lebesguePrimitive_locallyAC (g : ℝ → ℝ) (hg : LocallyIntegrable g volume)
    (a b : ℝ) (hab : a ≤ b) :
    AbsolutelyContinuousOnInterval (fun x => ∫ z in 0..x, g z) a b := by
  let l := min 0 a
  let u := max 0 b
  have hlu : l ≤ u := (min_le_left 0 a).trans (le_max_left 0 b)
  have hi : IntervalIntegrable g volume l u :=
    (intervalIntegrable_iff').2 (hg.integrableOn_isCompact isCompact_uIcc)
  have hc := hi.absolutelyContinuousOnInterval_intervalIntegral
    (show (0 : ℝ) ∈ uIcc l u by
      rw [uIcc_of_le hlu]; exact ⟨min_le_left _ _, le_max_left _ _⟩)
  apply hc.mono
  rw [uIcc_of_le hab, uIcc_of_le hlu]
  exact Icc_subset_Icc (min_le_right _ _) (le_max_right _ _)

/-- The oriented Lebesgue primitive is globally continuous. -/
theorem bellman_lebesguePrimitive_continuous (g : ℝ → ℝ)
    (hg : LocallyIntegrable g volume) : Continuous (fun x => ∫ z in 0..x, g z) :=
  bellman_locallyAC_continuous (bellman_lebesguePrimitive_locallyAC g hg)

/-- Changing the base point of a Lebesgue primitive subtracts a constant. -/
theorem bellman_lebesguePrimitive_sub (g : ℝ → ℝ) (hg : LocallyIntegrable g volume)
    (r x : ℝ) : (∫ z in 0..x, g z) - (∫ z in 0..r, g z) = ∫ z in r..x, g z := by
  have hi (a b : ℝ) : IntervalIntegrable g volume a b :=
    (intervalIntegrable_iff').2 (hg.integrableOn_isCompact isCompact_uIcc)
  have he := intervalIntegral.integral_add_adjacent_intervals (hi 0 r) (hi r x)
  linarith

/-- A locally integrable Lebesgue primitive has its original function as weak derivative. -/
theorem bellman_lebesguePrimitive_weak (g : ℝ → ℝ) (hg : LocallyIntegrable g volume)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcφ : HasCompactSupport φ) :
    (∫ x, (∫ z in 0..x, g z) * deriv φ x) = -∫ x, g x * φ x := by
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
    have hlhs : (∫ x, (fun x => ∫ z in 0..x, g z) x * deriv φ x) =
        ∫ x in Icc r R, (fun x => ∫ z in 0..x, g z) x * deriv φ x := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (f := deriv φ)
        (fun hd => hx ⟨(hdr hd).1.le, (hdr hd).2.le⟩), mul_zero]
    have hrhs : (∫ x, g x * φ x ) = ∫ x in Icc r R, g x * φ x  := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (f := φ)
        (fun hd => hx ⟨(hs hd).1.le, (hs hd).2.le⟩), mul_zero]
    have he : (∫ x in Icc r R, (fun x => ∫ z in 0..x, g z) x * deriv φ x) =
        ∫ x in Icc r R, (fun x => ∫ z in r..x, g z) x * deriv φ x := by
      have hi : IntegrableOn (fun x => (fun x => ∫ z in 0..x, g z) x * deriv φ x)
          (Icc r R) volume :=
        (((bellman_lebesguePrimitive_continuous g hg).locallyIntegrable).integrableOn_isCompact
          isCompact_Icc).mul_continuousOn hφd.continuous.continuousOn isCompact_Icc
      have hc : IntegrableOn (fun x => (fun x => ∫ z in 0..x, g z) r * deriv φ x)
          (Icc r R) volume :=
        (hφd.continuous.continuousOn.integrableOn_Icc).const_mul _
      have hfun : (fun x => (fun x => ∫ z in r..x, g z) x * deriv φ x) =
          (fun x => (fun x => ∫ z in 0..x, g z) x * deriv φ x -
            (fun x => ∫ z in 0..x, g z) r * deriv φ x) := by
        funext x
        have hp := bellman_lebesguePrimitive_sub g hg r x
        change (fun x => ∫ z in 0..x, g z) x - (fun x => ∫ z in 0..x, g z) r =
          (fun x => ∫ z in r..x, g z) x at hp
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
    exact PDE.intervalPrimitive_scalar_weak_identity_Icc
      (hg.integrableOn_isCompact isCompact_Icc)
      (hφ.of_le (by simp : (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞))) hs
  · have hz : φ = 0 := by
      funext x
      exact image_eq_zero_of_notMem_tsupport (fun hx => hn ⟨x, hx⟩)
    rw [hz, deriv_zero]
    simp only [Pi.zero_apply, mul_zero, integral_zero, neg_zero]

end HypoellipticAleksandrov.KineticAleksandrov
