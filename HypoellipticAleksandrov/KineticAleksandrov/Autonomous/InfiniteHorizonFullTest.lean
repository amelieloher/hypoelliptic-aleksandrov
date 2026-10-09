module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonTestGerm
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonRestriction
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtension

/-! # Infinite-horizon Green identity for the source's full late-vanishing C112 test class -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic

/-- The actual infinite Green and exit families obey the full C112 identity for tests vanishing
uniformly after a finite time. The lower-strip start is strictly interior, as ruled for this
  lane. -/
theorem strip_identity_infinite_C112
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (lower : ℝ) (e : StripPole H ⊤)
    (he : lower < e.1.time) (phi : Point → ℝ)
    (hphi : IsKineticC112On phi {p | lower < p.time ∧ p.velocity 0 ∈ H.carrier})
    (hc : ContinuousOn phi {p | lower < p.time ∧ p.velocity 0 ∈ Icc H.lo H.hi})
    (hb : ∃ M : ℝ, ∀ p, lower < p.time → p.velocity 0 ∈ H.carrier →
      |phi p| ≤ M ∧ |forwardScalarOperator A.a phi p| ≤ M)
    (R : ℝ) (hz : ∀ p, R ≤ p.time → p.velocity 0 ∈ H.carrier → phi p = 0) :
    phi e.1 = (∫ p, phi p ∂stripInfiniteExit hH hLE hlam hLam A H e) -
      ∫ p, forwardScalarOperator A.a phi p ∂stripGreen hH hLE hlam hLam A H ⊤ e := by
  let V := max R e.1.time + 1
  let T := V + 1
  have hRV : R < V := by dsimp [V]; linarith [le_max_left R e.1.time]
  have heV : e.1.time < V := by dsimp [V]; linarith [le_max_right R e.1.time]
  have heT : e.1.time < T := by dsimp [T]; linarith
  let ep := stripPoleFinite H e T heT
  have hi : reconstructionStrip H lower T ⊆
      {p | lower < p.time ∧ p.velocity 0 ∈ H.carrier} := fun _ hp => ⟨hp.1, hp.2.2⟩
  have hreg : IsKineticC112On phi (reconstructionStrip H lower T) :=
    ⟨hphi.1.mono hi, fun p hp => hphi.2.1 p (hi hp),
      fun p hp => hphi.2.2.1 p (hi hp), fun p hp => hphi.2.2.2.1 p (hi hp),
      hphi.2.2.2.2.1.mono hi, hphi.2.2.2.2.2.1.mono hi,
      hphi.2.2.2.2.2.2.1.mono hi, hphi.2.2.2.2.2.2.2.mono hi⟩
  have hcont : ContinuousOn phi (reconstructionStrip H lower T ∪ reconstructionExit H lower T) := by
    apply hc.mono
    intro p hp
    rcases hp with hp | hp
    · exact ⟨hp.1, hp.2.2.1.le, hp.2.2.2.le⟩
    · rcases hp with hp | hp
      · exact ⟨by rw [hp.1]; exact he.trans heT, hp.2⟩
      · refine ⟨hp.1, ?_⟩
        rcases hp.2.2 with hv | hv <;> rw [hv]
        · exact ⟨le_rfl, H.ordered.le⟩
        · exact ⟨H.ordered.le, le_rfl⟩
  obtain ⟨M, hM⟩ := hb
  have hid := strip_identity_C112 hH hLE hlam hLam A H lower T (he.trans heT) ep he phi
    hreg hcont ⟨M, fun p hp => hM p hp.1 hp.2.2⟩
  have hzeroexit (μ : Measure Point)
      (hm : ∀ᵐ p ∂μ, e.1.time ≤ p.time ∧ p.velocity 0 ∈ Icc H.lo H.hi) :
      (∫ p in {p : Point | p.time < V}, phi p ∂μ) = ∫ p, phi p ∂μ := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hm] with p hp hlate
    exact infinite_test_zero_late_closed H lower R phi hc hz p
      (he.trans_le hp.1) (hRV.le.trans (not_lt.mp hlate)) hp.2
  have hzi := hzeroexit (stripInfiniteExit hH hLE hlam hLam A H e)
    ((stripInfiniteExit_ae_future_faces hH hLE hlam hLam A H e).mono (fun p hp => by
      refine ⟨hp.1, ?_⟩
      rcases hp.2 with hv | hv <;> rw [hv]
      · exact ⟨le_rfl, H.ordered.le⟩
      · exact ⟨H.ordered.le, le_rfl⟩))
  have hzf := hzeroexit (stripExit hH hLE hlam hLam A H T ep)
    ((stripExitOfRealization_ae_closed_future hH hlam hLam A H _
      (stripEvolution_spec hH hLE hlam hLam A H) T ep).mono
      (fun p hp => ⟨hp.1, hp.2.2⟩))
  have hre := stripInfiniteExit_restrict_finite hH hLE hlam hLam A H e T heT V
    (by dsimp [T]; linarith)
  have hexit := hzf.symm.trans ((congrArg (fun μ : Measure Point => ∫ p, phi p ∂μ)
    hre.symm).trans hzi)
  have hrg := stripGreen_finite_restrict_infinite hH hLE hlam hLam A H e T heT
  have hzg : (∫ p in {p : Point | p.time < T}, forwardScalarOperator A.a phi p
      ∂stripGreen hH hLE hlam hLam A H ⊤ e) =
      ∫ p, forwardScalarOperator A.a phi p ∂stripGreen hH hLE hlam hLam A H ⊤ e := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [stripGreen_infinite_ae_future_carrier hH hLE hlam hLam A H e] with p hp hlate
    exact infinite_test_operator_zero_late A.a H phi R hz p
      (by have ht : T ≤ p.time := not_lt.mp hlate; dsimp [T] at ht; linarith) hp.2
  have hgreen := (congrArg (fun μ : Measure Point =>
    ∫ p, forwardScalarOperator A.a phi p ∂μ) hrg).trans hzg
  exact hid.trans (congrArg₂ (fun x y : ℝ => x - y) hexit hgreen)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
