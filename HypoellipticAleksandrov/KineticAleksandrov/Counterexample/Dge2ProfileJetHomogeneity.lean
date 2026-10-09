module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2ProfileSpectralJets

/-! # Homogeneity of the full velocity Hessian and stationary transport -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- Punctured homogeneity is sufficient for the exact velocity derivative scaling. -/
theorem punctured_homogeneous_velocity_jet {d : ℕ} (beta : ℝ) (F : XV d → ℝ)
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) F ({0}ᶜ))
    (hhom : ∀ r : ℝ, 0 < r → ∀ q, q ≠ 0 →
      F (dilate r q) = Real.rpow r beta * F q)
    (r : ℝ) (hr : 0 < r) (q : XV d) (hq : q ≠ 0) (w : PDE.Vec d) :
    fderiv ℝ F (dilate r q) (0, w) = Real.rpow r (beta - 1) * fderiv ℝ F q (0, w) := by
  have hopen : IsOpen ({0}ᶜ : Set (XV d)) := isClosed_singleton.isOpen_compl
  have hqd := (hsmooth.contDiffAt (hopen.mem_nhds hq)).differentiableAt (by simp)
  have hrqd := (hsmooth.contDiffAt
    (hopen.mem_nhds (dilate_ne_zero r hr q hq))).differentiableAt (by simp)
  have hd : HasFDerivAt (dilate (d := d) r)
      ((r ^ 3 • ContinuousLinearMap.fst ℝ (PDE.Vec d) (PDE.Vec d)).prod
        (r • ContinuousLinearMap.snd ℝ (PDE.Vec d) (PDE.Vec d))) q :=
    (hasFDerivAt_fst.const_smul (r ^ 3)).prodMk (hasFDerivAt_snd.const_smul r)
  have hh := hrqd.hasFDerivAt.comp q hd
  have hother : HasFDerivAt (fun z => F (dilate r z)) (Real.rpow r beta • fderiv ℝ F q) q := by
    apply (hqd.hasFDerivAt.const_mul (Real.rpow r beta)).congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hq] with z hz
    exact hhom r hr z hz
  have heq := congrArg (fun L : XV d →L[ℝ] ℝ => L (0, w)) (hh.unique hother)
  have hsmul : (0, r • w) = r • ((0, w) : XV d) := by simp
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_zero, smul_eq_mul] at heq
  rw [hsmul, map_smul, smul_eq_mul] at heq
  have hpower : Real.rpow r (beta - 1) = Real.rpow r beta / r := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_sub hr, Real.rpow_one]
  rw [hpower, div_mul_eq_mul_div]
  apply (eq_div_iff hr.ne').mpr
  simpa only [mul_comm] using heq

/-- The velocity Hessian has the exact kinetic weight alpha minus two. -/
theorem homogeneous_dvv {d : ℕ} (alpha : ℝ) (H : XV d → ℝ)
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ))
    (hhom : ∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q)
    (r : ℝ) (hr : 0 < r) (q : XV d) (hq : q ≠ 0) :
    dvv H (dilate r q) = Real.rpow r (alpha - 2) • dvv H q := by
  have hopen : IsOpen ({0}ᶜ : Set (XV d)) := isClosed_singleton.isOpen_compl
  ext i k
  let F := fun z => fderiv ℝ H z (0, Pi.single k 1)
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) F ({0}ᶜ) :=
    (hsmooth.fderiv_of_isOpen hopen (m := (⊤ : ℕ∞)) (by simp)).clm_apply
      (contDiffOn_const (c := ((0, Pi.single k 1) : XV d)))
  have hhomF : ∀ s : ℝ, 0 < s → ∀ z, z ≠ 0 →
      F (dilate s z) = Real.rpow s (alpha - 1) * F z :=
    fun s hs z hz => homogeneous_velocity_jet alpha H hsmooth hhom s hs z hz _
  have hh := punctured_homogeneous_velocity_jet (alpha - 1) F hF hhomF r hr q hq
    (Pi.single i 1)
  have hexp : alpha - 1 - 1 = alpha - 2 := by ring
  simpa only [dvv, dv, Matrix.smul_apply, smul_eq_mul, hexp] using hh

/-- The source full position jet has the exact kinetic weight alpha minus three. -/
theorem homogeneous_position_jet {d : ℕ} (alpha : ℝ) (H : XV d → ℝ)
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ))
    (hhom : ∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q)
    (r : ℝ) (hr : 0 < r) (q : XV d) (hq : q ≠ 0) (w : PDE.Vec d) :
    fderiv ℝ H (dilate r q) (w, 0) = Real.rpow r (alpha - 3) * fderiv ℝ H q (w, 0) := by
  have hopen : IsOpen ({0}ᶜ : Set (XV d)) := isClosed_singleton.isOpen_compl
  have hqd := (hsmooth.contDiffAt (hopen.mem_nhds hq)).differentiableAt (by simp)
  have hrqd := (hsmooth.contDiffAt
    (hopen.mem_nhds (dilate_ne_zero r hr q hq))).differentiableAt (by simp)
  have hd : HasFDerivAt (dilate (d := d) r)
      ((r ^ 3 • ContinuousLinearMap.fst ℝ (PDE.Vec d) (PDE.Vec d)).prod
        (r • ContinuousLinearMap.snd ℝ (PDE.Vec d) (PDE.Vec d))) q :=
    (hasFDerivAt_fst.const_smul (r ^ 3)).prodMk (hasFDerivAt_snd.const_smul r)
  have hh := hrqd.hasFDerivAt.comp q hd
  have hother : HasFDerivAt (fun z => H (dilate r z)) (Real.rpow r alpha • fderiv ℝ H q) q := by
    convert hqd.hasFDerivAt.const_mul (Real.rpow r alpha) using 1
    funext z
    exact hhom r hr z
  have heq := congrArg (fun L : XV d →L[ℝ] ℝ => L (w, 0)) (hh.unique hother)
  have hsmul : (r ^ 3 • w, 0) = r ^ 3 • ((w, 0) : XV d) := by simp
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_zero, smul_eq_mul] at heq
  rw [hsmul, map_smul, smul_eq_mul] at heq
  have hpower : Real.rpow r (alpha - 3) = Real.rpow r alpha / r ^ (3 : ℕ) := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_sub hr]
    norm_num
  rw [hpower, div_mul_eq_mul_div]
  apply (eq_div_iff (pow_ne_zero 3 hr.ne')).mpr
  simpa only [mul_comm] using heq

/-- The actual stationary transport has the same kinetic weight as the velocity Hessian. -/
theorem homogeneous_transport {d : ℕ} (alpha : ℝ) (H : XV d → ℝ)
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ))
    (hhom : ∀ r : ℝ, 0 < r → ∀ q, H (dilate r q) = Real.rpow r alpha * H q)
    (r : ℝ) (hr : 0 < r) (q : XV d) (hq : q ≠ 0) :
    PDE.vecDot (dilate r q).2 (dx H (dilate r q)) =
      Real.rpow r (alpha - 2) * PDE.vecDot q.2 (dx H q) := by
  rw [transport_eq_direction, transport_eq_direction]
  have hdir : ((dilate r q).2, (0 : PDE.Vec d)) = r • ((q.2, 0) : XV d) := by
    simp only [dilate, Prod.smul_mk, smul_zero]
  rw [hdir, map_smul, smul_eq_mul, homogeneous_position_jet alpha H hsmooth hhom r hr q hq]
  have hp : r * Real.rpow r (alpha - 3) = Real.rpow r (alpha - 2) := by
    simp only [Real.rpow_eq_pow]
    conv_lhs => lhs; rw [← Real.rpow_one r]
    rw [← Real.rpow_add hr]
    congr 1
    ring
  rw [← mul_assoc, hp]

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
