module

public import HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique

/-!
# Crossed weak velocity derivatives

This module proves that two crossed second weak velocity derivatives of one
raw function agree almost everywhere.  The proof uses distributional
uniqueness and commutation of classical mixed derivatives of test functions.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace HypoellipticAleksandrov.Parabolic

private theorem cross_ae_eq_of_pairing_eq {d : ℕ} {U : Set (TimeVelocity d)}
    (hU : IsOpen U) {du dv : TimeVelocity d → ℝ}
    (hdu : LocallyIntegrableOn du U volume)
    (hdv : LocallyIntegrableOn dv U volume)
    (hpair : ∀ φ : TimeVelocity d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ z in U, du z * φ z ∂volume) = ∫ z in U, dv z * φ z ∂volume) :
    du =ᵐ[timeVelocityVolumeOn U] dv := by
  have hdiffZero : ∀ᵐ z ∂volume, z ∈ U → du z - dv z = 0 := by
    refine hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (f := fun z => du z - dv z) (hdu.sub hdv) ?_
    intro φ hφSmooth hφCompact hφSub
    have hφCont : Continuous φ := hφSmooth.continuous
    have hduK : IntegrableOn du (tsupport φ) volume :=
      hdu.integrableOn_compact_subset hφSub hφCompact.isCompact
    have hdvK : IntegrableOn dv (tsupport φ) volume :=
      hdv.integrableOn_compact_subset hφSub hφCompact.isCompact
    have hduφK : IntegrableOn (fun z => du z * φ z) (tsupport φ) volume := by
      simpa [smul_eq_mul] using
        hduK.smul_continuousOn hφCont.continuousOn hφCompact.isCompact
    have hdvφK : IntegrableOn (fun z => dv z * φ z) (tsupport φ) volume := by
      simpa [smul_eq_mul] using
        hdvK.smul_continuousOn hφCont.continuousOn hφCompact.isCompact
    have hduφZero : ∀ z ∈ U \ tsupport φ, du z * φ z = 0 := by
      intro z hz
      simp [image_eq_zero_of_notMem_tsupport hz.2]
    have hdvφZero : ∀ z ∈ U \ tsupport φ, dv z * φ z = 0 := by
      intro z hz
      simp [image_eq_zero_of_notMem_tsupport hz.2]
    have hduInt : Integrable (fun z => du z * φ z) (timeVelocityVolumeOn U) := by
      simpa [IntegrableOn, timeVelocityVolumeOn] using
        hduφK.of_forall_diff_eq_zero hU.measurableSet hduφZero
    have hdvInt : Integrable (fun z => dv z * φ z) (timeVelocityVolumeOn U) := by
      simpa [IntegrableOn, timeVelocityVolumeOn] using
        hdvφK.of_forall_diff_eq_zero hU.measurableSet hdvφZero
    have hsetZero : ∫ z in U, φ z * (du z - dv z) ∂volume = 0 := by
      calc
        ∫ z in U, φ z * (du z - dv z) ∂volume =
            ∫ z in U, (du z * φ z - dv z * φ z) ∂volume := by
              apply setIntegral_congr_fun hU.measurableSet
              intro z hz
              ring
        _ = (∫ z in U, du z * φ z ∂volume) -
            ∫ z in U, dv z * φ z ∂volume := by
              rw [integral_sub hduInt hdvInt]
        _ = 0 := by rw [hpair φ hφSmooth hφCompact hφSub, sub_self]
    have hzeroOut : ∀ z, z ∉ U → φ z * (du z - dv z) = 0 := by
      intro z hz
      have hzNotIn : z ∉ tsupport φ := fun hz' => hz (hφSub hz')
      simp [image_eq_zero_of_notMem_tsupport hzNotIn]
    calc
      ∫ z, φ z • (du z - dv z) ∂volume =
          ∫ z, φ z * (du z - dv z) ∂volume := by simp [smul_eq_mul]
      _ = ∫ z in U, φ z * (du z - dv z) ∂volume := by
            rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzeroOut]
      _ = 0 := hsetZero
  rw [Filter.EventuallyEq, ae_restrict_iff' hU.measurableSet]
  filter_upwards [hdiffZero] with z hz hzU
  exact sub_eq_zero.mp (hz hzU)

private theorem cross_velocityGradient_contDiff_infty {d : ℕ}
    {f : TimeVelocity d → ℝ} {i : Fin d}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => velocityGradient f z i) := by
  unfold velocityGradient
  exact (contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const

private theorem cross_velocityGradient_hasCompactSupport {d : ℕ}
    {f : TimeVelocity d → ℝ} {i : Fin d}
    (hf : HasCompactSupport f) :
    HasCompactSupport (fun z => velocityGradient f z i) := by
  unfold velocityGradient
  simpa using hf.fderiv_apply (𝕜 := ℝ)
    ((0, Pi.single i 1) : TimeVelocity d)

private theorem cross_velocityGradient_tsupport_subset {d : ℕ}
    {f : TimeVelocity d → ℝ} {i : Fin d} :
    tsupport (fun z => velocityGradient f z i) ⊆ tsupport f := by
  unfold velocityGradient
  change closure (Function.support
    (fun z => fderiv ℝ f z (0, Pi.single i 1))) ⊆ tsupport f
  refine (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
  intro z hz
  rw [Function.mem_support] at hz ⊢
  intro hzero
  apply hz
  simp [hzero]

private theorem cross_velocityGradient_velocityGradient_commute {d : ℕ}
    {f : TimeVelocity d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (i j : Fin d) (z : TimeVelocity d) :
    velocityGradient (fun y => velocityGradient f y i) z j =
      velocityGradient (fun y => velocityGradient f y j) z i := by
  have hgrad : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) :=
    (contDiff_infty_iff_fderiv.mp hf).2
  have hgradDiff : DifferentiableAt ℝ (fderiv ℝ f) z :=
    hgrad.contDiffAt.differentiableAt (by simp)
  have hleft : velocityGradient (fun y => velocityGradient f y i) z j =
      HypoellipticAleksandrov.Parabolic.velocityHessian f z j i := by
    unfold velocityGradient HypoellipticAleksandrov.Parabolic.velocityHessian
    rw [fderiv_clm_apply hgradDiff (differentiableAt_const _)]
    have hconst : fderiv ℝ (fun _ : TimeVelocity d =>
        ((0, Pi.single i 1) : TimeVelocity d)) z = 0 :=
      (hasFDerivAt_const ((0, Pi.single i 1) : TimeVelocity d) z).fderiv
    rw [hconst]
    simp
  have hright : velocityGradient (fun y => velocityGradient f y j) z i =
      HypoellipticAleksandrov.Parabolic.velocityHessian f z i j := by
    unfold velocityGradient HypoellipticAleksandrov.Parabolic.velocityHessian
    rw [fderiv_clm_apply hgradDiff (differentiableAt_const _)]
    have hconst : fderiv ℝ (fun _ : TimeVelocity d =>
        ((0, Pi.single j 1) : TimeVelocity d)) z = 0 :=
      (hasFDerivAt_const ((0, Pi.single j 1) : TimeVelocity d) z).fderiv
    rw [hconst]
    simp
  rw [hleft, hright]
  exact (HypoellipticAleksandrov.Parabolic.velocityHessian_isSymm
      (hf.of_le (by
        change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)) z).apply i j

namespace HasWeakVelocityPartialDerivOn

/-- Two crossed second weak velocity derivatives of the same raw function
agree almost everywhere on an open domain. -/
theorem cross_ae_eq_of_memLp
    {d : ℕ} {U : Set (TimeVelocity d)}
    (hU : IsOpen U)
    (i j : Fin d)
    (u ui uj dij dji : TimeVelocity d → ℝ)
    (hdij : ParabolicMemLpOn U 2 dij)
    (hdji : ParabolicMemLpOn U 2 dji)
    (hui : HasWeakVelocityPartialDerivOn U i u ui)
    (huj : HasWeakVelocityPartialDerivOn U j u uj)
    (hij : HasWeakVelocityPartialDerivOn U j ui dij)
    (hji : HasWeakVelocityPartialDerivOn U i uj dji) :
    dij =ᵐ[timeVelocityVolumeOn U] dji := by
  apply cross_ae_eq_of_pairing_eq hU
    (hdij.locallyIntegrableOn (by norm_num))
    (hdji.locallyIntegrableOn (by norm_num))
  intro φ hφSmooth hφCompact hφSub
  have htestSmooth (k : Fin d) :
      ContDiff ℝ (⊤ : ℕ∞) (fun z => velocityGradient φ z k) :=
    cross_velocityGradient_contDiff_infty hφSmooth
  have htestCompact (k : Fin d) :
      HasCompactSupport (fun z => velocityGradient φ z k) :=
    cross_velocityGradient_hasCompactSupport hφCompact
  have htestSub (k : Fin d) :
      tsupport (fun z => velocityGradient φ z k) ⊆ U :=
    cross_velocityGradient_tsupport_subset.trans hφSub
  have hijSecond := hij φ hφSmooth hφCompact hφSub
  have hiFirst := hui (fun z => velocityGradient φ z j) (htestSmooth j)
    (htestCompact j) (htestSub j)
  have hjiSecond := hji φ hφSmooth hφCompact hφSub
  have hjFirst := huj (fun z => velocityGradient φ z i) (htestSmooth i)
    (htestCompact i) (htestSub i)
  calc
    (∫ z in U, dij z * φ z ∂volume) =
        ∫ z in U, u z *
          velocityGradient (fun y => velocityGradient φ y j) z i ∂volume := by
      linarith only [hijSecond, hiFirst]
    _ = ∫ z in U, u z *
          velocityGradient (fun y => velocityGradient φ y i) z j ∂volume := by
      apply setIntegral_congr_fun hU.measurableSet
      intro z hz
      simp only
      rw [cross_velocityGradient_velocityGradient_commute hφSmooth]
    _ = ∫ z in U, dji z * φ z ∂volume := by
      linarith only [hjiSecond, hjFirst]

end HasWeakVelocityPartialDerivOn
end HypoellipticAleksandrov.Parabolic
