module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileGeTwoIntegrability
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileWeakExtension
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Classical integration by parts away from the profile origin -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Set

/-- Integration by parts for a locally integrable jet smooth away from the origin. -/
theorem punctured_directional_ibp {d : ℕ} (f : XV d → ℝ) (w : XV d)
    (hf : LocallyIntegrable f volume)
    (hdf : LocallyIntegrable (fun q => fderiv ℝ f q w) volume)
    (hs : ∀ q : XV d, q ≠ 0 → DifferentiableAt ℝ f q)
    (test : XV d → ℝ) (ht : ContDiff ℝ 1 test) (hc : HasCompactSupport test)
    (hz : (0 : XV d) ∉ tsupport test) :
    (∫ q, f q * fderiv ℝ test q w) = -(∫ q, fderiv ℝ f q w * test q) := by
  let : Measure.IsAddHaarMeasure (volume : Measure (PDE.Vec d)) :=
    isAddHaarMeasure_volume_pi (Fin d)
  let : Measure.IsAddHaarMeasure (volume : Measure (XV d)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · simpa only [smul_eq_mul, mul_comm] using
      hdf.integrable_smul_left_of_hasCompactSupport ht.continuous hc
  · simpa only [smul_eq_mul, mul_comm] using
      hf.integrable_smul_left_of_hasCompactSupport
        ((ht.fderiv_right (m := 0) (by norm_num)).clm_apply contDiff_const).continuous
        (hc.fderiv_apply ℝ w)
  · simpa only [smul_eq_mul, mul_comm] using
      hf.integrable_smul_left_of_hasCompactSupport ht.continuous hc
  · intro q hq
    exact hs q (fun he => hz (he ▸ hq))
  · intro q _
    exact ht.differentiable (by norm_num) q

/-- The two constant velocity derivatives of a C2 test commute. -/
theorem dvv_test_swap {d : ℕ} (test : XV d → ℝ) (ht : ContDiff ℝ 2 test)
    (q : XV d) (i k : Fin d) : dvv test q i k = dvv test q k i := by
  have hd : DifferentiableAt ℝ (fderiv ℝ test) q :=
    ((ht.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) q
  unfold dvv dv
  rw [fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_clm_apply hd (differentiableAt_const _)]
  simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply] using!
    ((ht.contDiffAt (x := q)).isSymmSndFDerivAt (by simp)).eq
      (0, Pi.single i 1) (0, Pi.single k 1)

/-- The higher-dimensional classical profile has all punctured weak identities. -/
theorem classical_punctured_weak_from_jets {d : ℕ} (H : XV d → ℝ)
    (hH : Continuous H)
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ : Set (XV d)))
    (hx : ∀ i, LocallyIntegrable (fun q => dx H q i) volume)
    (hv : ∀ i, LocallyIntegrable (fun q => dv H q i) volume)
    (hh : ∀ i k, LocallyIntegrable (fun q => dvv H q i k) volume)
    (test : XV d → ℝ) (ht : ContDiff ℝ 2 test) (hc : HasCompactSupport test)
    (hz : (0 : XV d) ∉ tsupport test) :
    (∀ i, (∫ q, H q * dx test q i) = -(∫ q, dx H q i * test q)) ∧
    (∀ i, (∫ q, H q * dv test q i) = -(∫ q, dv H q i * test q)) ∧
    (∀ i k, (∫ q, H q * dvv test q i k) = (∫ q, dvv H q i k * test q)) := by
  have hdiff := differentiableAt_profile_off_origin H hs
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact punctured_directional_ibp H (Pi.single i 1, 0) hH.locallyIntegrable (hx i)
      hdiff test (ht.of_le (by norm_num)) hc hz
  · intro i
    exact punctured_directional_ibp H (0, Pi.single i 1) hH.locallyIntegrable (hv i)
      hdiff test (ht.of_le (by norm_num)) hc hz
  · intro i k
    have htest : ContDiff ℝ 1 (fun q => dv test q i) := contDiff_dv_test test ht i
    have hsupport : HasCompactSupport (fun q => dv test q i) :=
      hc.fderiv_apply ℝ (0, Pi.single i 1)
    have htestzero : (0 : XV d) ∉ tsupport (fun q => dv test q i) :=
      fun hmem => hz ((tsupport_fderiv_apply_subset ℝ (0, Pi.single i 1)) hmem)
    have hfirst := punctured_directional_ibp H (0, Pi.single k 1)
      hH.locallyIntegrable (hv k) hdiff _ htest hsupport htestzero
    have hsecond := punctured_directional_ibp (fun q => dv H q k) (0, Pi.single i 1)
      (hv k) (hh i k)
      (fun q hq => (contDiffAt_dv_off_origin H hs q hq k).differentiableAt (by simp))
      test (ht.of_le (by norm_num)) hc hz
    change (∫ q, H q * dvv test q k i) = -(∫ q, dv H q k * dv test q i) at hfirst
    change (∫ q, dv H q k * dv test q i) = -(∫ q, dvv H q i k * test q) at hsecond
    simpa only [dvv_test_swap test ht _ k i, hsecond, neg_neg] using hfirst

/-- The higher-dimensional classical profile has all punctured weak identities. -/
theorem profile_classical_punctured_weak (d : ℕ) (hd : 1 ≤ d)
    (H : XV d → ℝ) (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1)
    (hH : Continuous H)
    (hhom : ∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q)
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ : Set (XV d)))
    (test : XV d → ℝ) (ht : ContDiff ℝ 2 test) (hc : HasCompactSupport test)
    (hz : (0 : XV d) ∉ tsupport test) :
    (∀ i, (∫ q, H q * dx test q i) = -(∫ q, dx H q i * test q)) ∧
    (∀ i, (∫ q, H q * dv test q i) = -(∫ q, dv H q i * test q)) ∧
    (∀ i k, (∫ q, H q * dvv test q i k) = (∫ q, dvv H q i k * test q)) := by
  obtain ⟨hx, hv, hh⟩ := profile_classical_jets_locallyIntegrable d hd H alpha ha ha1 hhom hs
  exact classical_punctured_weak_from_jets H hH hs hx hv hh test ht hc hz

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
