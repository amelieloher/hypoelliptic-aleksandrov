module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitConeCalculus

/-! # Vanishing of both actual measures beyond every strict transport cone -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter
open SectionTwo TheoremA Evolution

/-- A strict negative transport direction kills both actual measures on its positive side. -/
theorem reconstruction_strict_transport_cone_ae
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ))
    (alpha beta gamma delta : ℝ) (hdelta : 0 < delta)
    (he : reconstructionConeCoordinate alpha beta gamma e.1 = 0)
    (hdir : ∀ v ∈ H.carrier, alpha + v * beta ≤ -delta) :
    (∀ᵐ p ∂stripExitOfRealization hH hlam hLam A H E hE T e,
      reconstructionConeCoordinate alpha beta gamma p ≤ 0) ∧
    ∀ᵐ p ∂stripGreenOfKernel H E.2 T e, reconstructionConeCoordinate alpha beta gamma p ≤ 0 := by
  let rho := reconstructionConeCoordinate alpha beta gamma
  let phi := expNegInvGlue ∘ rho
  let Ω := stripExitOfRealization hH hlam hLam A H E hE T e
  let Γ := stripGreenOfKernel H E.2 T e
  let V := max |H.lo| |H.hi|
  let C := |alpha| + V * |beta|
  have hV : 0 ≤ V := (abs_nonneg H.lo).trans (le_max_left _ _)
  have hC : 0 ≤ C := add_nonneg (abs_nonneg _) (mul_nonneg hV (abs_nonneg _))
  have hv (v : ℝ) (hv : v ∈ H.carrier) : |v| ≤ V := by
    apply abs_le.mpr
    exact ⟨((neg_le_neg (le_max_left |H.lo| |H.hi|)).trans (neg_abs_le H.lo)).trans hv.1.le,
      hv.2.le.trans ((le_abs_self H.hi).trans (le_max_right _ _))⟩
  have hop (p : Point) : forwardScalarOperator A.a phi p =
      (alpha + p.velocity 0 * beta) * deriv expNegInvGlue (rho p) :=
    reconstructionConeProbe_operator A.a alpha beta gamma p
  have hbd (p : Point) (hp : p.velocity 0 ∈ H.carrier) :
      |forwardScalarOperator A.a phi p| ≤ C * 2 := by
    rw [hop, abs_mul, abs_of_nonneg (reconstructionConeTransition_deriv_bounds _).1]
    apply mul_le_mul _ (reconstructionConeTransition_deriv_bounds _).2.1
      (reconstructionConeTransition_deriv_bounds _).1 hC
    exact (abs_add_le _ _).trans (add_le_add le_rfl (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hv _ hp) (abs_nonneg _)))
  have hi := strip_identity_bounded_smooth_of_realization hH hlam hLam A H E hE T e phi
    (reconstructionConeProbe_smooth alpha beta gamma) (by
      refine ⟨max 1 (C * 2), fun p hp => ?_⟩
      constructor
      · change |expNegInvGlue (rho p)| ≤ _
        rw [abs_of_nonneg (expNegInvGlue.nonneg _)]
        exact (reconstructionConeTransition_bound _).2.trans (le_max_left _ _)
      · exact (hbd p hp).trans (le_max_right _ _))
  have hpn : ∀ p, 0 ≤ phi p := fun p => expNegInvGlue.nonneg _
  have hint : Integrable phi Ω := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
      ((reconstruction_smooth_physical_continuous phi
        (reconstructionConeProbe_smooth _ _ _)).measurable.aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hpn p)]
      exact (reconstructionConeTransition_bound _).2)
  have hkn : forwardScalarOperator A.a phi ≤ᵐ[Γ] 0 := by
    filter_upwards [stripGreenOfKernel_ae_mem_stripPast H E.2 T e] with p hp
    rw [hop]
    exact mul_nonpos_of_nonpos_of_nonneg ((hdir _ hp.2).trans (neg_nonpos.mpr hdelta.le))
      (reconstructionConeTransition_deriv_bounds _).1
  have hpos := integral_nonneg_of_ae (μ := Ω) (Filter.Eventually.of_forall hpn)
  have hneg := integral_nonpos_of_ae hkn
  have hzero : phi e.1 = 0 := by
    change expNegInvGlue (reconstructionConeCoordinate alpha beta gamma e.1) = 0
    rw [he]
    exact expNegInvGlue.zero
  change phi e.1 = (∫ p, phi p ∂Ω) - (∫ p, forwardScalarOperator A.a phi p ∂Γ) at hi
  rw [hzero] at hi
  have hφint : (∫ p, phi p ∂Ω) = 0 := by linarith
  have hkint : (∫ p, forwardScalarOperator A.a phi p ∂Γ) = 0 := by linarith
  constructor
  · have hz := (integral_eq_zero_iff_of_nonneg hpn hint).mp hφint
    filter_upwards [hz] with p hp
    exact expNegInvGlue.zero_iff_nonpos.mp hp
  · have hdc : Continuous (deriv expNegInvGlue) :=
      (expNegInvGlue.contDiff : ContDiff ℝ (⊤ : ℕ∞) expNegInvGlue).continuous_deriv (by simp)
    have hrho : Continuous rho :=
      ((continuous_const.mul continuous_time).add
        (continuous_const.mul ((continuous_apply 0).comp continuous_position))).add continuous_const
    have hmeas : AEStronglyMeasurable (forwardScalarOperator A.a phi) Γ := by
      have hc : Continuous (fun p : Point => (alpha + p.velocity 0 * beta) *
          deriv expNegInvGlue (rho p)) := (((continuous_const.add
        (((continuous_apply 0).comp continuous_velocity).mul continuous_const)).mul
          (hdc.comp hrho)))
      exact hc.measurable.aestronglyMeasurable.congr
        (Filter.Eventually.of_forall (fun p => (hop p).symm))
    have hkintg : Integrable (forwardScalarOperator A.a phi) Γ := by
      apply Integrable.mono' (integrable_const (C * 2)) hmeas
      filter_upwards [stripGreenOfKernel_ae_mem_stripPast H E.2 T e] with p hp
      rw [Real.norm_eq_abs]
      exact hbd p hp.2
    have hz := (integral_eq_zero_iff_of_nonneg_ae (by
      filter_upwards [hkn] with p hp; exact neg_nonneg.mpr hp) hkintg.neg).mp
        (by
          change (∫ p, -forwardScalarOperator A.a phi p ∂Γ) = 0
          rw [integral_neg, hkint, neg_zero])
    filter_upwards [hz, stripGreenOfKernel_ae_mem_stripPast H E.2 T e] with p hp hs
    by_contra hposrho
    have hdr := (reconstructionConeTransition_deriv_bounds (rho p)).2.2 (not_le.mp hposrho)
    have hcoef : alpha + p.velocity 0 * beta < 0 := (hdir _ hs.2).trans_lt (neg_neg_of_pos hdelta)
    have hn := mul_neg_of_neg_of_pos hcoef hdr
    rw [← hop] at hn
    change -forwardScalarOperator A.a phi p = 0 at hp
    linarith

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
