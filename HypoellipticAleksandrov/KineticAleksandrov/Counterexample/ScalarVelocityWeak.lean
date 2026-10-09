module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarIntegrability
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarContinuity
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileWeak
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Tactic

/-!
# Scalar velocity weak identities

A position cutoff avoids the nonsmooth position axis without contributing any velocity
derivative. Native dominated convergence then removes that cutoff.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Filter Set
open scoped Topology

/-- A position cutoff removes the entire scalar position axis from the test support. -/
theorem scalar_position_cutoff_support (test : XV 1 → ℝ) (n : ℕ) (q : XV 1)
    (hq : q ∈ tsupport (fun z => test z * originCutoff n z.1)) : q.1 0 ≠ 0 := by
  intro hx
  have hz : q.1 = 0 := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact hx
  have ht : Tendsto (Prod.fst : XV 1 → PDE.Vec 1) (𝓝 q) (𝓝 0) := by
    simpa only [hz] using continuous_fst.tendsto q
  have he := (originCutoff_eventually_zero 1 n).comp_tendsto ht
  apply (notMem_tsupport_iff_eventuallyEq.mpr ?_) hq
  filter_upwards [he] with z hz
  change originCutoff n z.1 = 0 at hz
  simp only [hz, mul_zero]
  rfl

/-- Velocity integration by parts for a locally integrable jet smooth off the position axis. -/
theorem scalar_velocity_ibp (f g : XV 1 → ℝ)
    (hfi : LocallyIntegrable f volume) (hgi : LocallyIntegrable g volume)
    (hfd : ∀ q : XV 1, q.1 0 ≠ 0 → DifferentiableAt ℝ f q)
    (hfg : ∀ q : XV 1, q.1 0 ≠ 0 → fderiv ℝ f q (0, Pi.single 0 1) = g q)
    (test : XV 1 → ℝ) (ht : ContDiff ℝ 1 test) (hs : HasCompactSupport test) :
    (∫ q, f q * dv test q 0) = -(∫ q, g q * test q) := by
  let : Measure.IsAddHaarMeasure (volume : Measure (PDE.Vec 1)) :=
    isAddHaarMeasure_volume_pi (Fin 1)
  let : Measure.IsAddHaarMeasure (volume : Measure (XV 1)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hderiv : ∀ᵐ q ∂volume, fderiv ℝ f q (0, Pi.single 0 1) = g q := by
    filter_upwards [coordinates_ne_zero_ae 1 (by omega)] with q hq
    apply hfg q
    intro hz
    apply hq.1
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact hz
  let cut : ℕ → XV 1 → ℝ := fun n q => originCutoff n q.1
  have he (n : ℕ) : (∫ q, (f q * dv test q 0) * cut n q) =
      -(∫ q, (g q * test q) * cut n q) := by
    let t : XV 1 → ℝ := fun q => test q * cut n q
    have ht1 : ContDiff ℝ 1 t := ht.mul
      (((contDiff_originCutoff 1 n).of_le (by norm_num)).comp contDiff_fst)
    have htc : HasCompactSupport t := hs.mul_right
    have hgT : Integrable (fun q => g q * t q) volume := by
      simpa only [smul_eq_mul, mul_comm] using
        hgi.integrable_smul_left_of_hasCompactSupport ht1.continuous htc
    have hfT : Integrable (fun q => f q * t q) volume := by
      simpa only [smul_eq_mul, mul_comm] using
        hfi.integrable_smul_left_of_hasCompactSupport ht1.continuous htc
    have hfDT : Integrable (fun q => f q * fderiv ℝ t q (0, Pi.single 0 1)) volume := by
      simpa only [smul_eq_mul, mul_comm] using
        hfi.integrable_smul_left_of_hasCompactSupport
          ((ht1.fderiv_right (m := 0) (by norm_num)).clm_apply contDiff_const).continuous
          (htc.fderiv_apply ℝ (0, Pi.single 0 1))
    have hfGT : Integrable (fun q => fderiv ℝ f q (0, Pi.single 0 1) * t q) volume := by
      apply hgT.congr
      filter_upwards [hderiv] with q hq
      rw [hq]
    have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hfGT hfDT hfT
      (fun q hq => hfd q (scalar_position_cutoff_support test n q hq))
      (fun q _ => ht1.differentiable (by norm_num) q)
    have hR : (∫ q, fderiv ℝ f q (0, Pi.single 0 1) * t q) = ∫ q, g q * t q := by
      apply integral_congr_ae
      filter_upwards [hderiv] with q hq
      rw [hq]
    rw [hR] at hIBP
    change (∫ q, f q * dv t q 0) = -(∫ q, g q * t q) at hIBP
    simpa only [t, cut, dv_mul_position_cutoff test n _
      (ht.differentiable (by norm_num) _) 0, mul_assoc] using hIBP
  have hL : Integrable (fun q => f q * dv test q 0) volume := by
    simpa only [smul_eq_mul, mul_comm, dv] using
      hfi.integrable_smul_left_of_hasCompactSupport
        ((ht.fderiv_right (m := 0) (by norm_num)).clm_apply contDiff_const).continuous
        (hs.fderiv_apply ℝ (0, Pi.single 0 1))
  have hR : Integrable (fun q => g q * test q) volume := by
    simpa only [smul_eq_mul, mul_comm] using
      hgi.integrable_smul_left_of_hasCompactSupport ht.continuous hs
  have hc (n : ℕ) : Measurable (cut n) :=
    ((contDiff_originCutoff 1 n).continuous.comp continuous_fst).measurable
  have hb (n : ℕ) (q : XV 1) : |cut n q| ≤ 1 := abs_originCutoff_le_one n q.1
  have hl : ∀ᵐ q ∂volume, Tendsto (fun n => cut n q) atTop (𝓝 1) := by
    filter_upwards [coordinates_ne_zero_ae 1 (by omega)] with q hq
    exact originCutoff_tendsto q.1 hq.1
  have hlimL := integral_mul_cutoff_tendsto _ hL cut hc hb hl
  have hlimR := (integral_mul_cutoff_tendsto _ hR cut hc hb hl).neg
  exact tendsto_nhds_unique hlimL (hlimR.congr (fun n => (he n).symm))

/-- The actual scalar profile has its first native velocity weak identity. -/
theorem scalarProfile_velocity_weak (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (hmatch : Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3)) =
      Real.rpow Lam (-gamma.1)) (test : XV 1 → ℝ) (ht : ContDiff ℝ 1 test)
    (hs : HasCompactSupport test) :
    (∫ q, scalarProfile gamma Lam q * dv test q 0) =
      -(∫ q, scalarGv gamma Lam q 0 * test q) := by
  apply scalar_velocity_ibp _ _
    (scalarProfile_continuous gamma Lam hLam hmatch).locallyIntegrable
    ((scalarJets_locallyIntegrable gamma Lam hLam hmatch).2.1 0)
  · intro q hq
    exact (scalarProfile_contDiffAt_off_axis gamma Lam hLam q hq).differentiableAt
      (by norm_num)
  · intro q hq
    simp only [scalarGv, hq, ↓reduceIte, dv]
  · exact ht
  · exact hs

/-- The actual scalar profile has its second native velocity weak identity. -/
theorem scalarProfile_hessian_weak (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (hmatch : Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3)) =
      Real.rpow Lam (-gamma.1)) (test : XV 1 → ℝ) (ht : ContDiff ℝ 2 test)
    (hs : HasCompactSupport test) :
    (∫ q, scalarProfile gamma Lam q * dvv test q 0 0) =
      (∫ q, scalarHess gamma Lam q 0 0 * test q) := by
  have hjet := scalarJets_locallyIntegrable gamma Lam hLam hmatch
  have hfirst := scalarProfile_velocity_weak gamma Lam hLam hmatch
    (fun q => dv test q 0) (contDiff_dv_test test ht 0)
    (hs.fderiv_apply ℝ (0, Pi.single 0 1))
  have hsecond : (∫ q, scalarGv gamma Lam q 0 * dv test q 0) =
      -(∫ q, scalarHess gamma Lam q 0 0 * test q) := by
    apply scalar_velocity_ibp _ _ (hjet.2.1 0) (hjet.2.2 0 0)
    · intro q hq
      exact scalarGv_differentiableAt gamma Lam hLam q hq 0
    · intro q hq
      exact (scalarHess_eq_velocity_derivative gamma Lam q hq 0 0).symm
    · exact ht.of_le (by norm_num)
    · exact hs
  change (∫ q, scalarProfile gamma Lam q * dvv test q 0 0) =
    -(∫ q, scalarGv gamma Lam q 0 * dv test q 0) at hfirst
  simpa only [hsecond, neg_neg] using hfirst

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
