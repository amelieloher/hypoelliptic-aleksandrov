module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2ProfileBounds

/-! # Exact homogeneity and gauge bound for the velocity gradient -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- Positive kinetic dilation preserves nonzero points. -/
theorem dilate_ne_zero {d : ℕ} (r : ℝ) (hr : 0 < r) (q : XV d) (hq : q ≠ 0) :
    dilate r q ≠ 0 := by
  intro hzero
  have hx := congrArg Prod.fst hzero
  have hv := congrArg Prod.snd hzero
  exact hq (Prod.ext ((smul_eq_zero_iff_right (pow_ne_zero 3 hr.ne')).mp hx)
    ((smul_eq_zero_iff_right hr.ne').mp hv))

/-- The derivative of a homogeneous smooth function has the source velocity weight. -/
theorem homogeneous_velocity_jet {d : ℕ} (alpha : ℝ) (H : XV d → ℝ)
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ))
    (hhom : ∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q)
    (r : ℝ) (hr : 0 < r) (q : XV d) (hq : q ≠ 0) (w : PDE.Vec d) :
    fderiv ℝ H (dilate r q) (0, w) =
      Real.rpow r (alpha - 1) * fderiv ℝ H q (0, w) := by
  have hqmem : q ∈ ({0}ᶜ : Set (XV d)) := hq
  have hrqmem : dilate r q ∈ ({0}ᶜ : Set (XV d)) := dilate_ne_zero r hr q hq
  have hopen : IsOpen ({0}ᶜ : Set (XV d)) := isClosed_singleton.isOpen_compl
  have hqd := (hsmooth.contDiffAt (hopen.mem_nhds hqmem)).differentiableAt (by simp)
  have hrqd := (hsmooth.contDiffAt (hopen.mem_nhds hrqmem)).differentiableAt (by simp)
  have hd : HasFDerivAt (dilate (d := d) r)
      ((r ^ 3 • ContinuousLinearMap.fst ℝ (PDE.Vec d) (PDE.Vec d)).prod
        (r • ContinuousLinearMap.snd ℝ (PDE.Vec d) (PDE.Vec d))) q :=
    (hasFDerivAt_fst.const_smul (r ^ 3)).prodMk (hasFDerivAt_snd.const_smul r)
  have hh := hrqd.hasFDerivAt.comp q hd
  have hother : HasFDerivAt (fun z => H (dilate r z))
      (Real.rpow r alpha • fderiv ℝ H q) q := by
    convert hqd.hasFDerivAt.const_mul (Real.rpow r alpha) using 1
    funext z
    exact hhom r hr z
  have heq := congrArg (fun L : XV d →L[ℝ] ℝ => L (0, w)) (hh.unique hother)
  have hsmul : (0, r • w) = r • ((0, w) : XV d) := by simp
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_zero, smul_eq_mul] at heq
  rw [hsmul, map_smul, smul_eq_mul] at heq
  have hpower : Real.rpow r (alpha - 1) = Real.rpow r alpha / r := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_sub hr, Real.rpow_one]
  rw [hpower]
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hr.ne').mpr
  simpa only [mul_comm] using heq

/-- The native selector vector has the same exact velocity homogeneity. -/
theorem homogeneous_dv {d : ℕ} (alpha : ℝ) (H : XV d → ℝ)
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ))
    (hhom : ∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q)
    (r : ℝ) (hr : 0 < r) (q : XV d) (hq : q ≠ 0) :
    dv H (dilate r q) = Real.rpow r (alpha - 1) • dv H q := by
  ext i
  exact homogeneous_velocity_jet alpha H hsmooth hhom r hr q hq (Pi.single i 1)

/-- Smooth homogeneous profiles satisfy the source velocity-gradient bound. -/
theorem homogeneous_velocity_gradient_bound {d : ℕ} (alpha : ℝ) (H : XV d → ℝ)
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ))
    (hhom : ∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q) :
    ∃ C : ℝ, 0 < C ∧ ∀ q, q ≠ 0 →
      PDE.vecEuclideanNorm (dv H q) ≤ C * Real.rpow (rho q) (alpha - 1) := by
  let K : Set (XV d) := {q | rho q = 1}
  have hKnz : ∀ q ∈ K, q ≠ 0 := by
    intro q hq hz
    have hh : rho q = 1 := hq
    simp [hz] at hh
  have hopen : IsOpen ({0}ᶜ : Set (XV d)) := isClosed_singleton.isOpen_compl
  have hd : ContinuousOn (fun q => PDE.vecEuclideanNorm (dv H q)) K := by
    apply PDE.continuous_vecEuclideanNorm.comp_continuousOn
    apply continuousOn_pi.mpr
    intro i
    have hc := (hsmooth.continuousOn_fderiv_of_isOpen hopen (by simp)).clm_apply
      (continuousOn_const (c := ((0, Pi.single i 1) : XV d)))
    exact hc.mono (fun q hq => hKnz q hq)
  obtain ⟨B, hB⟩ := (isCompact_unitGaugeShell d).bddAbove_image hd
  let C := max 1 B
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro q hq
  have hr : 0 < rho q := (rho_nonneg q).lt_of_ne' ((rho_eq_zero_iff q).not.mpr hq)
  let p := dilate (rho q)⁻¹ q
  have hp : p ∈ K := by
    change rho (dilate (rho q)⁻¹ q) = 1
    rw [rho_dilate _ (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']
  have hpnz := hKnz p hp
  have hqp : dilate (rho q) p = q := by
    dsimp [p]
    rw [dilate_mul, mul_inv_cancel₀ hr.ne', dilate_one]
  have hj := homogeneous_dv alpha H hsmooth hhom (rho q) hr p hpnz
  rw [hqp] at hj
  rw [hj, PDE.vecEuclideanNorm_smul]
  have hpow := Real.rpow_pos_of_pos hr (alpha - 1)
  simp only [Real.rpow_eq_pow] at hpow ⊢
  rw [abs_of_pos hpow]
  have hb : PDE.vecEuclideanNorm (dv H p) ≤ C :=
    (hB ⟨p, hp, rfl⟩).trans (le_max_right _ _)
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb hpow.le

/-- The actual profile satisfies the required velocity-gradient estimate. -/
theorem geometricProfile_velocity_gradient_bound {d : ℕ} (alpha C₀ sigma R : ℝ)
    (hsigma : 0 < sigma) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : XV d, q ≠ 0 →
      PDE.vecEuclideanNorm (dv (geometricProfile alpha C₀ sigma R) q) ≤
        C * Real.rpow (rho q) (alpha - 1) := by
  apply homogeneous_velocity_gradient_bound alpha (geometricProfile alpha C₀ sigma R)
    (geometricProfile_smooth_off_origin alpha C₀ sigma R hsigma hR)
  exact fun r hr q => geometricProfile_homogeneous alpha C₀ sigma R r hr q

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
