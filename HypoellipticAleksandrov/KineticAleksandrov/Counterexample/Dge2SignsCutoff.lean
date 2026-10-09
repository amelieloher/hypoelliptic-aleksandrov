module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2SignsRescaled
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2CutoffScaling
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2SignsSeedTransport

/-! # Hessian sign control for the actual Appendix C cutoff -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- The velocity Hessian quadratic form of the actual cutoff. -/
def cutoffHessian {d : ℕ} (alpha C₀ sigma R : ℝ) (y e w : PDE.Vec d) : ℝ :=
  fderiv ℝ (fun z => fderiv ℝ (fun a => cutoffProfile alpha C₀ sigma R a e) z w) y w

/-- Two locally equal functions have equal scalar second directional derivatives. -/
theorem hessian_eq_of_eventuallyEq {d : ℕ} (F G : PDE.Vec d → ℝ)
    (y w u : PDE.Vec d) (h : F =ᶠ[nhds y] G) :
    fderiv ℝ (fun z => fderiv ℝ F z w) y u =
      fderiv ℝ (fun z => fderiv ℝ G z w) y u := by
  have hh : (fun z => fderiv ℝ F z w) =ᶠ[nhds y] (fun z => fderiv ℝ G z w) := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with z hz
    exact congrArg (fun L => L w) hz
  exact congrArg (fun L => L u) (hh.fderiv_eq (𝕜 := ℝ))

/-- The actual cutoff has the seed Hessian in the open inner ball. -/
theorem cutoffHessian_eq_seed {d : ℕ} (alpha C₀ sigma R : ℝ) (hR : 0 < R)
    (y e w : PDE.Vec d) (hy : PDE.vecEuclideanNorm y < R) :
    cutoffHessian alpha C₀ sigma R y e w =
      fderiv ℝ (fun z => fderiv ℝ (fun a => seed alpha C₀ sigma a e) z w) y w := by
  apply hessian_eq_of_eventuallyEq
  filter_upwards [PDE.continuous_vecEuclideanNorm.continuousAt.eventually_lt_const hy]
    with z hz
  exact cutoffProfile_eq_seed alpha C₀ sigma R hR z e hz.le

/-- The actual cutoff has the radial Hessian in the open outer region. -/
theorem cutoffHessian_eq_radial {d : ℕ} (alpha C₀ sigma R : ℝ) (hR : 0 < R)
    (y e w : PDE.Vec d) (hy : 2 * R < PDE.vecEuclideanNorm y) :
    cutoffHessian alpha C₀ sigma R y e w =
      fderiv ℝ (fun z => fderiv ℝ (radialProfile alpha) z w) y w := by
  apply hessian_eq_of_eventuallyEq
  filter_upwards [PDE.continuous_vecEuclideanNorm.continuousAt.eventually_const_lt hy]
    with z hz
  exact cutoffProfile_eq_radial alpha C₀ sigma R hR z e hz.le

/-- For sufficiently large R the actual cutoff has both Hessian signs on its closed annulus. -/
theorem eventually_cutoff_annulus_signs (d : ℕ) (hd : 2 ≤ d) (alpha C₀ sigma : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hsigma : 0 < sigma) :
    ∀ᶠ R : ℝ in Filter.atTop, 2 < R ∧ ∀ y e : PDE.Vec d,
      PDE.vecNormSq e = 1 → R ≤ PDE.vecEuclideanNorm y →
      PDE.vecEuclideanNorm y ≤ 2 * R →
      (∃ w, 0 < cutoffHessian alpha C₀ sigma R y e w) ∧
      (∃ w, cutoffHessian alpha C₀ sigma R y e w < 0) := by
  filter_upwards [eventually_rescaled_annulus_signs d hd alpha C₀ sigma ha ha1,
    Filter.eventually_gt_atTop (2 : ℝ)] with R hsign hR2
  have hR : 0 < R := lt_trans (by norm_num) hR2
  refine ⟨hR2, ?_⟩
  intro y e he hyR hy2R
  let z := R⁻¹ • y
  have hnorm : PDE.vecEuclideanNorm z = PDE.vecEuclideanNorm y / R := by
    simp only [z, PDE.vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr hR),
      div_eq_mul_inv, mul_comm]
  have hz : (e, z) ∈ cutoffAnnulus d := by
    refine ⟨he, ?_, ?_⟩
    · rw [hnorm]
      exact (le_div_iff₀ hR).mpr (by simpa using hyR)
    · rw [hnorm]
      exact (div_le_iff₀ hR).mpr (by simpa only [mul_comm] using hy2R)
  have hRz : R • z = y := by
    dsimp [z]
    rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  have hp : 0 < (Real.rpow R alpha)⁻¹ * R ^ 2 :=
    mul_pos (inv_pos.mpr (Real.rpow_pos_of_pos hR _)) (sq_pos_of_pos hR)
  obtain ⟨⟨wp, hwp⟩, ⟨wn, hwn⟩⟩ := hsign e z hz
  have hh (w : PDE.Vec d) : rescaledHessian alpha sigma
      (C₀ / Real.rpow R alpha) R⁻¹ e z w =
      (Real.rpow R alpha)⁻¹ * R ^ 2 * cutoffHessian alpha C₀ sigma R y e w := by
    unfold rescaledHessian cutoffHessian
    rw [rescaledCutoff_hessian alpha C₀ sigma R hsigma hR, hRz]
  refine ⟨⟨wp, ?_⟩, ⟨wn, ?_⟩⟩
  · rw [hh] at hwp
    exact (mul_pos_iff_of_pos_left hp).mp hwp
  · rw [hh] at hwn
    by_contra hh
    exact (mul_nonneg hp.le (le_of_not_gt hh)).not_gt hwn

/-- The actual cutoff has a positive Hessian direction everywhere, once R is large. -/
theorem eventually_cutoff_positive_direction (d : ℕ) (hd : 2 ≤ d)
    (alpha C₀ sigma : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) (hsigma : 0 < sigma) :
    ∀ᶠ R : ℝ in Filter.atTop, 2 < R ∧ ∀ y e : PDE.Vec d,
      PDE.vecNormSq e = 1 → ∃ w, 0 < cutoffHessian alpha C₀ sigma R y e w := by
  filter_upwards [eventually_cutoff_annulus_signs d hd alpha C₀ sigma ha ha1 hsigma]
    with R hR
  have hR0 : 0 < R := lt_trans (by norm_num) hR.1
  refine ⟨hR.1, ?_⟩
  intro y e he
  by_cases hy : PDE.vecEuclideanNorm y < R
  · obtain ⟨w, hw⟩ := seed_positive_direction d hd alpha C₀ sigma ha hsigma y e
    exact ⟨w, by rwa [cutoffHessian_eq_seed alpha C₀ sigma R hR0 y e w hy]⟩
  · by_cases houter : 2 * R < PDE.vecEuclideanNorm y
    · have hy0 : y ≠ 0 := by
        intro hzero
        have hn : PDE.vecEuclideanNorm y = 0 := PDE.vecEuclideanNorm_eq_zero_iff.mpr hzero
        rw [hn] at houter
        linarith
      obtain ⟨w, hw⟩ := radialHessian_positive_direction d hd alpha ha y hy0
      refine ⟨w, ?_⟩
      rw [cutoffHessian_eq_radial alpha C₀ sigma R hR0 y e w houter,
        radialProfile_hessian alpha y w w hy0]
      exact hw
    · exact (hR.2 y e he (le_of_not_gt hy) (le_of_not_gt houter)).1

/-- The transport expression agrees with the seed throughout the open inner ball. -/
theorem cutoffTransport_eq_seed {d : ℕ} (alpha C₀ sigma R : ℝ) (hR : 0 < R)
    (y e : PDE.Vec d) (hy : PDE.vecEuclideanNorm y < R) :
    ansatzTransport alpha (cutoffProfile alpha C₀ sigma R) y e =
      ansatzTransport alpha (seed alpha C₀ sigma) y e := by
  have hvel : (fun z => cutoffProfile alpha C₀ sigma R z e) =ᶠ[nhds y]
      (fun z => seed alpha C₀ sigma z e) := by
    filter_upwards [PDE.continuous_vecEuclideanNorm.continuousAt.eventually_lt_const hy]
      with z hz
    exact cutoffProfile_eq_seed alpha C₀ sigma R hR z e hz.le
  have hsphere : (fun z => cutoffProfile alpha C₀ sigma R y z) =
      (fun z => seed alpha C₀ sigma y z) := by
    funext z
    exact cutoffProfile_eq_seed alpha C₀ sigma R hR y z hy.le
  unfold ansatzTransport
  rw [cutoffProfile_eq_seed alpha C₀ sigma R hR y e hy.le, hvel.fderiv_eq, hsphere]

/-- A strictly negative Hessian direction exists outside the small seed ball for large R. -/
theorem eventually_cutoff_negative_direction (d : ℕ) (hd : 2 ≤ d)
    (alpha C₀ sigma : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) (hsigma : 0 < sigma)
    (hsq : sigma ^ 2 < (1 - alpha) / 16) :
    ∀ᶠ R : ℝ in Filter.atTop, 2 < R ∧ ∀ y e : PDE.Vec d,
      PDE.vecNormSq e = 1 → 1 / 4 < PDE.vecEuclideanNorm (y - e) →
      ∃ w, cutoffHessian alpha C₀ sigma R y e w < 0 := by
  filter_upwards [eventually_cutoff_annulus_signs d hd alpha C₀ sigma ha ha1 hsigma]
    with R hR
  have hR0 : 0 < R := lt_trans (by norm_num) hR.1
  refine ⟨hR.1, ?_⟩
  intro y e he hyseed
  by_cases hy : PDE.vecEuclideanNorm y < R
  · have hnorm := PDE.vecEuclideanNorm_nonneg (y - e)
    have hsqnorm := PDE.vecEuclideanNorm_sq (y - e)
    have hlow : (1 / 16 : ℝ) < PDE.vecNormSq (y - e) := by nlinarith
    have hthreshold : sigma ^ 2 < (1 - alpha) * PDE.vecNormSq (y - e) := by
      have hh := mul_lt_mul_of_pos_left hlow (sub_pos.mpr ha1)
      linarith
    obtain ⟨w, hw⟩ := seed_negative_direction alpha C₀ sigma ha hsigma y e hthreshold
    exact ⟨w, by rwa [cutoffHessian_eq_seed alpha C₀ sigma R hR0 y e w hy]⟩
  · by_cases houter : 2 * R < PDE.vecEuclideanNorm y
    · have hy0 : y ≠ 0 := by
        intro hzero
        rw [PDE.vecEuclideanNorm_eq_zero_iff.mpr hzero] at houter
        linarith
      refine ⟨y, ?_⟩
      rw [cutoffHessian_eq_radial alpha C₀ sigma R hR0 y e y houter,
        radialProfile_hessian alpha y y y hy0]
      exact radialHessian_radial_neg alpha ha ha1 y hy0
    · exact (hR.2 y e he (le_of_not_gt hy) (le_of_not_gt houter)).2

/-- Source sign control for the actual cutoff, with all parameters chosen internally. -/
theorem exists_cutoff_sign_parameters (d : ℕ) (hd : 2 ≤ d) (alpha : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C₀ sigma R : ℝ, 0 < C₀ ∧ 0 < sigma ∧ 2 < R ∧
      ∀ y e : PDE.Vec d, PDE.vecNormSq e = 1 →
        (∃ w, 0 < cutoffHessian alpha C₀ sigma R y e w) ∧
        ((∃ w, cutoffHessian alpha C₀ sigma R y e w < 0) ∨
          1 ≤ ansatzTransport alpha (cutoffProfile alpha C₀ sigma R) y e) := by
  let sigma := (1 - alpha) / 8
  have hsigma : 0 < sigma := div_pos (sub_pos.mpr ha1) (by norm_num)
  have hsq : sigma ^ 2 < (1 - alpha) / 16 := by
    dsimp [sigma]
    nlinarith [sq_nonneg alpha]
  obtain ⟨C₀, hC₀, htransport⟩ := seed_transport_pos d alpha sigma ha hsigma
  obtain ⟨R, hp, hn⟩ := ((eventually_cutoff_positive_direction d hd alpha C₀ sigma ha ha1
    hsigma).and (eventually_cutoff_negative_direction d hd alpha C₀ sigma ha ha1
    hsigma hsq)).exists
  refine ⟨C₀, sigma, R, hC₀, hsigma, hp.1, ?_⟩
  intro y e he
  refine ⟨hp.2 y e he, ?_⟩
  by_cases hy : 1 / 4 < PDE.vecEuclideanNorm (y - e)
  · exact Or.inl (hn.2 y e he hy)
  · right
    have hsmall : PDE.vecEuclideanNorm (y - e) ≤ 1 / 4 := le_of_not_gt hy
    have hen : PDE.vecEuclideanNorm e = 1 := by
      unfold PDE.vecEuclideanNorm
      rw [he]
      norm_num
    have htri := PDE.vecEuclideanNorm_add_le (y - e) e
    have hinner : PDE.vecEuclideanNorm y < R := by
      rw [sub_add_cancel, hen] at htri
      linarith
    rw [cutoffTransport_eq_seed alpha C₀ sigma R (lt_trans (by norm_num) hp.1) y e hinner]
    exact htransport y e he hsmall

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
