module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarWeakSlice
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarIntegrability
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarContinuity
import Mathlib.Tactic

/-!
# Scalar position weak identity

Fubini uses the exact native volume equivalence. Each scalar position slice is continuous
through zero, so its two half-line boundary terms cancel.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Filter Set
open scoped Topology

/-- Position integration by parts for a continuous native function with an actual off-axis jet. -/
theorem scalar_position_ibp (f g : XV 1 → ℝ) (hf : Continuous f)
    (hgi : LocallyIntegrable g volume)
    (hfd : ∀ q : XV 1, q.1 0 ≠ 0 → DifferentiableAt ℝ f q)
    (hfg : ∀ q : XV 1, q.1 0 ≠ 0 → fderiv ℝ f q (Pi.single 0 1, 0) = g q)
    (test : XV 1 → ℝ) (ht : ContDiff ℝ 1 test) (hs : HasCompactSupport test) :
    (∫ q, f q * dx test q 0) = -(∫ q, g q * test q) := by
  let L : XV 1 → ℝ := fun q => f q * dx test q 0
  let R : XV 1 → ℝ := fun q => g q * test q
  have hL : Integrable L volume := by
    simpa only [L, dx, smul_eq_mul, mul_comm] using
      hf.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
        ((ht.fderiv_right (m := 0) (by norm_num)).clm_apply contDiff_const).continuous
        (hs.fderiv_apply ℝ (Pi.single 0 1, 0))
  have hR : Integrable R volume := by
    simpa only [R, smul_eq_mul, mul_comm] using
      hgi.integrable_smul_left_of_hasCompactSupport ht.continuous hs
  have hLI := scalarNativeCoordinates_symm_measurePreserving.integrable_comp_of_integrable hL
  have hRI := scalarNativeCoordinates_symm_measurePreserving.integrable_comp_of_integrable hR
  rw [Measure.volume_eq_prod] at hLI hRI
  have hLC := scalarNativeCoordinates_symm_measurePreserving.integral_comp' L
  have hRC := scalarNativeCoordinates_symm_measurePreserving.integral_comp' R
  change (∫ q, L q) = -(∫ q, R q)
  rw [← hLC, ← hRC]
  simp only [Function.comp_def] at hLI hRI
  rw [Measure.volume_eq_prod, integral_prod_symm _ hLI, integral_prod_symm _ hRI,
    ← integral_neg]
  apply integral_congr_ae
  filter_upwards [hLI.prod_left_ae, hRI.prod_left_ae] with v hLv hRv
  simp only [scalarNativeCoordinates_symm_apply, L, R] at hLv hRv ⊢
  have hP : Continuous (fun x => scalarPoint x v) := by unfold scalarPoint; fun_prop
  have hdu (x : ℝ) (hx : x ≠ 0) : HasDerivAt (fun t => f (scalarPoint t v))
      (g (scalarPoint x v)) x := by
    have hd := (hfd (scalarPoint x v) hx).hasFDerivAt.comp_hasDerivAt x
      (scalarPoint_hasDerivAt_x x v)
    simpa only [Function.comp_def, hfg (scalarPoint x v) hx] using hd
  have hdt (x : ℝ) : HasDerivAt (fun t => test (scalarPoint t v))
      (dx test (scalarPoint x v) 0) x := by
    have hd := (ht.differentiable (by norm_num) (scalarPoint x v)).hasFDerivAt.comp_hasDerivAt x
      (scalarPoint_hasDerivAt_x x v)
    simpa only [Function.comp_def, dx] using hd
  have hX : Continuous (fun q : XV 1 => q.1 0) := by fun_prop
  obtain ⟨B, hB⟩ := hs.isCompact.exists_bound_of_continuousOn hX.continuousOn
  have hzTop : ∀ᶠ x in atTop, test (scalarPoint x v) = 0 := by
    filter_upwards [eventually_gt_atTop B] with x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hq
    have hb := hB (scalarPoint x v) hq
    have hl : x ≤ |x| := le_abs_self x
    simp only [scalarPoint, Real.norm_eq_abs] at hb
    linarith
  have hzBot : ∀ᶠ x in atBot, test (scalarPoint x v) = 0 := by
    filter_upwards [eventually_lt_atBot (-B)] with x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hq
    have hb := hB (scalarPoint x v) hq
    have hl : -x ≤ |x| := neg_le_abs x
    simp only [scalarPoint, Real.norm_eq_abs] at hb
    linarith
  apply scalar_integral_mul_deriv_off_zero
    (fun x => f (scalarPoint x v)) (fun x => g (scalarPoint x v))
    (fun x => test (scalarPoint x v)) (fun x => dx test (scalarPoint x v) 0)
    (hf.comp hP) (ht.continuous.comp hP) hdu hdt hRv hLv
  · apply tendsto_const_nhds.congr'
    filter_upwards [hzTop] with x hx
    simp only [hx, mul_zero]
  · apply tendsto_const_nhds.congr'
    filter_upwards [hzBot] with x hx
    simp only [hx, mul_zero]

/-- The actual scalar profile has its native position weak identity. -/
theorem scalarProfile_position_weak (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (hmatch : Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3)) =
      Real.rpow Lam (-gamma.1)) (test : XV 1 → ℝ) (ht : ContDiff ℝ 1 test)
    (hs : HasCompactSupport test) :
    (∫ q, scalarProfile gamma Lam q * dx test q 0) =
      -(∫ q, scalarGx gamma Lam q 0 * test q) := by
  apply scalar_position_ibp _ _ (scalarProfile_continuous gamma Lam hLam hmatch)
    ((scalarJets_locallyIntegrable gamma Lam hLam hmatch).1 0)
  · intro q hq
    exact (scalarProfile_contDiffAt_off_axis gamma Lam hLam q hq).differentiableAt
      (by norm_num)
  · intro q hq
    simp only [scalarGx, hq, ↓reduceIte, dx]
  · exact ht
  · exact hs

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
