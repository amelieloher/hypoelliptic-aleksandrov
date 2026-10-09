module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoffSource
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoffDifference

/-! # The actual backward operator of the cutoff profile -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory HypoellipticAleksandrov.Parabolic

/-- The native spatial slice of the barrier is smooth at every finite order. -/
theorem contDiff_nativeBarrier (d : ℕ) (mu R t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : XV d => barrier mu R ⟨t, q.1, q.2⟩) := by
  simpa only [barrier] using!
    (contDiff_const (c := Real.exp (-mu * t))).mul ((contDiff_const (c := (2 : ℝ))).sub
      ((PDE.contDiff_vecNormSq.comp contDiff_snd).div_const (R ^ 2)))

/-- The cutoff's time derivative differentiates only the explicit exponential barrier. -/
theorem timeCutoffProfile_timeDerivative {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R : ℝ) (P : KineticPoint d) :
    kineticTimeDerivative (timeCutoffProfile (profileFunction h) alpha r mu R) P =
      -deriv timeCutoffTheta (selectedFlatProfile h r (P.position, P.velocity) -
        barrier mu R P) * kineticTimeDerivative (barrier mu R) P := by
  have hb := (((hasDerivAt_id P.time).const_mul (-mu)).exp).mul_const
    (2 - PDE.vecNormSq P.velocity / R ^ 2)
  have hi := hb.const_sub (selectedFlatProfile h r (P.position, P.velocity))
  have ht : DifferentiableAt ℝ timeCutoffTheta
      (selectedFlatProfile h r (P.position, P.velocity) - barrier mu R P) :=
    (contDiff_timeCutoffTheta.differentiable (by simp)).differentiableAt
  have he := ht.hasDerivAt.comp P.time hi
  change HasDerivAt
    (fun s => timeCutoffProfile (profileFunction h) alpha r mu R
      ⟨s, P.position, P.velocity⟩) _ P.time at he
  change deriv (fun s => timeCutoffProfile (profileFunction h) alpha r mu R
    ⟨s, P.position, P.velocity⟩) P.time = _
  rw [he.deriv, barrier_timeDerivative]
  simp only [selectedFlatProfile, barrier, id_eq, mul_one]
  ring

/-- At a C2 point of the flattened profile, the actual cutoff operator equals its weak jets. -/
theorem timeCutoff_operator_eq_representative_at {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R t : ℝ) (q : XV d)
    (hu : ContDiffAt ℝ 2 (selectedFlatProfile h r) q)
    (hj : flatProfilePositionJet h r q = dx (selectedFlatProfile h r) q ∧
      flatProfileVelocityJet h r q = dv (selectedFlatProfile h r) q ∧
      flatProfileHessian h r q = dvv (selectedFlatProfile h r) q) :
    backwardOperator (fun _t x v => profileMatrix h (x, v))
      (timeCutoffProfile (profileFunction h) alpha r mu R) ⟨t, q.1, q.2⟩ =
      timeCutoffSourceRepresentative h r mu R ⟨t, q.1, q.2⟩ := by
  let b : XV d → ℝ := fun y => barrier mu R ⟨t, y.1, y.2⟩
  let f : XV d → ℝ := fun y => selectedFlatProfile h r y - b y
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := contDiff_nativeBarrier d mu R t
  have hb2 : ContDiffAt ℝ 2 b q := (hb.of_le (by simp)).contDiffAt
  have hf : ContDiffAt ℝ 2 f q := hu.sub hb2
  have hc : ContDiffAt ℝ 2 (fun y => timeCutoffTheta (f y)) q :=
    (contDiff_timeCutoffTheta.of_le (by simp)).contDiffAt.comp q hf
  have hbx : dx b q = 0 := by
    rw [dx_eq_classicalGradient b (hb.differentiable (by simp))]
    exact barrier_positionGradient mu R ⟨t, q.1, q.2⟩
  have hbv : dv b q = kineticVelocityGradient (barrier mu R) ⟨t, q.1, q.2⟩ :=
    dv_eq_classicalGradient b (hb.differentiable (by simp)) q
  have hbh : dvv b q = kineticVelocityHessian (barrier mu R) ⟨t, q.1, q.2⟩ := by
    simpa only [b, kineticVelocityHessian, barrier] using! dvv_eq_sliceHessian_at b q hb2
  have hx : kineticPositionGradient
      (timeCutoffProfile (profileFunction h) alpha r mu R) ⟨t, q.1, q.2⟩ =
      fun i => deriv timeCutoffTheta (f q) * flatProfilePositionJet h r q i := by
    rw [show kineticPositionGradient
      (timeCutoffProfile (profileFunction h) alpha r mu R) ⟨t, q.1, q.2⟩ =
      dx (fun y => timeCutoffTheta (f y)) q from
        (dx_eq_classicalGradient_at _ q (hc.differentiableAt (by norm_num))).symm]
    funext i
    unfold dx
    rw [fderiv_timeCutoffTheta_comp f q (hf.differentiableAt (by norm_num))]
    change deriv timeCutoffTheta (f q) * dx f q i = _
    rw [dx_sub_at _ _ q (hu.differentiableAt (by norm_num))
      (hb2.differentiableAt (by norm_num)), hbx, sub_zero, ← hj.1]
  have hh : kineticVelocityHessian
      (timeCutoffProfile (profileFunction h) alpha r mu R) ⟨t, q.1, q.2⟩ =
      fun i k => deriv timeCutoffTheta (f q) *
        (flatProfileHessian h r q i k - kineticVelocityHessian (barrier mu R) ⟨t, q.1, q.2⟩ i k) +
        deriv (deriv timeCutoffTheta) (f q) *
          (flatProfileVelocityJet h r q - kineticVelocityGradient (barrier mu R) ⟨t, q.1, q.2⟩) i *
          (flatProfileVelocityJet h r q -
            kineticVelocityGradient (barrier mu R) ⟨t, q.1, q.2⟩) k := by
    have hs := dvv_eq_sliceHessian_at (fun y => timeCutoffTheta (f y)) q hc
    change dvv (fun y => timeCutoffTheta (f y)) q =
      kineticVelocityHessian
        (timeCutoffProfile (profileFunction h) alpha r mu R) ⟨t, q.1, q.2⟩ at hs
    rw [← hs]
    funext i k
    rw [dvv_timeCutoffTheta_comp f q hf i k,
      dvv_sub_at _ _ q hu hb2, dv_sub_at _ _ q (hu.differentiableAt (by norm_num))
        (hb2.differentiableAt (by norm_num)), hbv, hbh, ← hj.2.1, ← hj.2.2]
    rfl
  rw [backwardOperator_apply, timeCutoffProfile_timeDerivative, hx, hh]
  rfl

/-- Both dimension branches satisfy the actual time-cutoff operator bound almost everywhere. -/
theorem timeCutoff_operator_le_of_profile {d : ℕ} (hd : 1 ≤ d) {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    (R : ℝ) (hR : 0 < R) (t : ℝ) :
    ∀ᵐ q ∂volume,
      backwardOperator (fun _t x v => profileMatrix h (x, v))
        (timeCutoffProfile (profileFunction h) alpha r
          ((d : ℝ) * profileLowerEllipticity h / R ^ 2) R) ⟨t, q.1, q.2⟩ ≤
        flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r q := by
  filter_upwards [selectedFlatProfile_contDiffAt_ae h r,
    flatProfile_jets_ae_of_profile h r hr,
    timeCutoff_source_le_of_profile hd h r hr R hR t] with q hc hj hs
  rw [timeCutoff_operator_eq_representative_at h r _ R t q hc hj]
  exact hs

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
