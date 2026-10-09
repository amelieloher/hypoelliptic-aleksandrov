module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningWeakBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningWeakLimit
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningBounds

/-! # The weak flattening chain rule in every dimension

Classical chain rules hold for the normalized convolutions. Compact jet bounds
and almost-everywhere convergence pass their test identities to the original
flattening. The complementary-coordinate cutoffs then remove the origin.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Filter Set

/-- Smooth functions have the three classical punctured distributional identities. -/
theorem smooth_punctured_weak_identities {d : ℕ} (H : XV d → ℝ)
    (hs : ContDiff ℝ (⊤ : ℕ∞) H)
    (test : XV d → ℝ) (ht : ContDiff ℝ 2 test) (hc : HasCompactSupport test)
    (hz : (0 : XV d) ∉ tsupport test) :
    (∀ i, (∫ q, H q * dx test q i) = -(∫ q, dx H q i * test q)) ∧
    (∀ i, (∫ q, H q * dv test q i) = -(∫ q, dv H q i * test q)) ∧
    (∀ i k, (∫ q, H q * dvv test q i k) = (∫ q, dvv H q i k * test q)) := by
  have hx (i : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (fun q => dx H q i) :=
    (hs.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  have hv (i : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (fun q => dv H q i) :=
    (hs.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  have hh (i k : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (fun q => dvv H q i k) :=
    ((hv k).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  exact classical_punctured_weak_from_jets H hs.continuous hs.contDiffOn
    (fun i => (hx i).continuous.locallyIntegrable)
    (fun i => (hv i).continuous.locallyIntegrable)
    (fun i k => (hh i k).continuous.locallyIntegrable) test ht hc hz

/-- The literal flattened function has all weak test identities away from the origin. -/
theorem flatProfile_punctured_weak_of_profile {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    (test : XV d → ℝ) (ht : ContDiff ℝ 2 test) (hs : HasCompactSupport test)
    (hz : (0 : XV d) ∉ tsupport test) :
    (∀ i, (∫ q, selectedFlatProfile h r q * dx test q i) =
      -(∫ q, flatProfilePositionJet h r q i * test q)) ∧
    (∀ i, (∫ q, selectedFlatProfile h r q * dv test q i) =
      -(∫ q, flatProfileVelocityJet h r q i * test q)) ∧
    (∀ i k, (∫ q, selectedFlatProfile h r q * dvv test q i k) =
      (∫ q, flatProfileHessian h r q i k * test q)) := by
  let K := tsupport test
  obtain ⟨C, hC, hb⟩ := mollifiedFlatProfile_eventually_bounded h r hr K hs hz
  have hnorm : ∀ᶠ n in atTop, ∀ q ∈ K, ‖mollifiedFlatProfile h r n q‖ ≤ C := by
    filter_upwards [hb] with n hn
    exact fun q hq => (hn q hq).1
  have hvalue (t : XV d → ℝ) (hc : Continuous t) (hsc : HasCompactSupport t)
      (hsub : tsupport t ⊆ K) :
      Tendsto (fun n => ∫ q, mollifiedFlatProfile h r n q * t q) atTop
        (nhds (∫ q, selectedFlatProfile h r q * t q)) :=
    integral_mul_test_tendsto _ _
      (fun n => (contDiff_mollifiedFlatProfile h r n).continuous.aestronglyMeasurable)
      (mollifiedFlatProfile_ae_tendsto h r) t hc hsc K hsub C hC hnorm
  have hclassic (n : ℕ) := smooth_punctured_weak_identities _
    (contDiff_mollifiedFlatProfile h r n) test ht hs hz
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hleft := hvalue (fun q => dx test q i) (continuous_dx_test test ht i)
      (hs.fderiv_apply ℝ (Pi.single i 1, 0)) (tsupport_fderiv_apply_subset ℝ (Pi.single i 1, 0))
    have hbound : ∀ᶠ n in atTop, ∀ q ∈ K, ‖dx (mollifiedFlatProfile h r n) q i‖ ≤ C := by
      filter_upwards [hb] with n hn
      intro q hq
      simpa only [Real.norm_eq_abs] using (hn q hq).2.1 i
    have hright := integral_mul_test_tendsto _ _
      (fun n => (measurable_fderiv_apply_const ℝ (mollifiedFlatProfile h r n)
        (Pi.single i 1, 0)).aestronglyMeasurable)
      (dx_mollifiedFlatProfile_ae_tendsto h r hr i) test ht.continuous hs K subset_rfl C hC hbound
    exact tendsto_nhds_unique (hleft.congr (fun n => (hclassic n).1 i)) hright.neg
  · intro i
    have hleft := hvalue (fun q => dv test q i) (continuous_dv_test test ht i)
      (hs.fderiv_apply ℝ (0, Pi.single i 1)) (tsupport_fderiv_apply_subset ℝ (0, Pi.single i 1))
    have hbound : ∀ᶠ n in atTop, ∀ q ∈ K, ‖dv (mollifiedFlatProfile h r n) q i‖ ≤ C := by
      filter_upwards [hb] with n hn
      intro q hq
      simpa only [Real.norm_eq_abs] using (hn q hq).2.2.1 i
    have hright := integral_mul_test_tendsto _ _
      (fun n => (measurable_fderiv_apply_const ℝ (mollifiedFlatProfile h r n)
        (0, Pi.single i 1)).aestronglyMeasurable)
      (dv_mollifiedFlatProfile_ae_tendsto h r hr i) test ht.continuous hs K subset_rfl C hC hbound
    exact tendsto_nhds_unique (hleft.congr (fun n => (hclassic n).2.1 i)) hright.neg
  · intro i k
    have hsub : tsupport (fun q => dvv test q i k) ⊆ K :=
      (tsupport_fderiv_apply_subset ℝ (0, Pi.single i 1)).trans
        (tsupport_fderiv_apply_subset ℝ (0, Pi.single k 1))
    have hleft := hvalue (fun q => dvv test q i k) (continuous_dvv_test test ht i k)
      ((hs.fderiv_apply ℝ (0, Pi.single k 1)).fderiv_apply ℝ (0, Pi.single i 1)) hsub
    have hbound : ∀ᶠ n in atTop, ∀ q ∈ K, ‖dvv (mollifiedFlatProfile h r n) q i k‖ ≤ C := by
      filter_upwards [hb] with n hn
      intro q hq
      simpa only [Real.norm_eq_abs] using (hn q hq).2.2.2 i k
    have hright := integral_mul_test_tendsto _ _
      (fun n => (measurable_dvv (mollifiedFlatProfile h r n) i k).aestronglyMeasurable)
      (dvv_mollifiedFlatProfile_ae_tendsto h r hr i k)
      test ht.continuous hs K subset_rfl C hC hbound
    exact tendsto_nhds_unique (hleft.congr (fun n => (hclassic n).2.2 i k)) hright

/-- The literal flattened function has the three weak identities on the entire carrier. -/
theorem flatProfile_weak_of_profile {d : ℕ} (hd : 1 ≤ d) {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r) :
    ∀ test : XV d → ℝ, ContDiff ℝ 2 test → HasCompactSupport test →
      (∀ i, (∫ q, selectedFlatProfile h r q * dx test q i) =
        -(∫ q, flatProfilePositionJet h r q i * test q)) ∧
      (∀ i, (∫ q, selectedFlatProfile h r q * dv test q i) =
        -(∫ q, flatProfileVelocityJet h r q i * test q)) ∧
      (∀ i k, (∫ q, selectedFlatProfile h r q * dvv test q i k) =
        (∫ q, flatProfileHessian h r q i k * test q)) := by
  obtain ⟨hx, hv, hh⟩ := flatProfile_jets_locallyIntegrable_of_profile h r hr
  exact profile_weak_identities_extend d hd (selectedFlatProfile h r)
    (flatProfilePositionJet h r) (flatProfileVelocityJet h r) (flatProfileHessian h r)
    (continuous_selectedFlatProfile h r) hx hv hh (flatProfile_punctured_weak_of_profile h r hr)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
