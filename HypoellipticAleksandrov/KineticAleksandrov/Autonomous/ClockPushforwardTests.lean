module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockGreenTestBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockPushforwardGreen

/-! # The actual finite physical Green test at a sufficiently late physical horizon -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic
open SectionTwo TheoremA Evolution

/-- A weighted compact normalized probe expressed in physical coordinates. -/
def clockWeightedProbe (c : Clock) (e : Point) (f : exitProbeSubmodule) : Point → ℝ :=
  fun p => |p.velocity 0| * exitProbePhysical f (c.map e p)

/-- The weighted physical clock probe is continuous and compactly supported. -/
theorem clockWeightedProbe_continuous_compact (c : Clock) (e : Point)
    (f : exitProbeSubmodule) :
    Continuous (clockWeightedProbe c e f) ∧ HasCompactSupport (clockWeightedProbe c e f) := by
  have hf := exitProbePhysical_continuous_compact f
  exact ⟨((continuous_apply 0).comp continuous_velocity).abs.mul
    (hf.1.comp (c.continuous_map e)),
    (hf.2.comp_homeomorph (c.homeomorph e)).mul_left⟩

/-- The genuine test has zero exit integral at every physical horizon past the clock cutoff. -/
theorem clock_test_exit_zero
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point)
    (R T U : ℝ) (hRT : R < T) (hU : e.time + 2 * c.r ^ 2 * R ≤ U)
    (ep : StripPole c.activeInterval (U : WithTop ℝ)) (hep : ep.1 = e)
    (f : exitProbeSubmodule) (hfn : ∀ p, 0 ≤ exitProbePhysical f p)
    (hs : tsupport (exitProbePhysical f) ⊆
      {p | p.time < T ∧ p.velocity 0 ∈ clockNormalizedInterval.carrier})
    (hz : ∀ p, R ≤ p.time → exitProbePhysical f p = 0) :
    (∫ p, clockSourcePotential hH hLE hlam hLam A c e T f
      (sectionTwoPoint (c.map e p)) ∂stripExit hH hLE hlam hLam A c.activeInterval U ep) = 0 := by
  have hc := (clock_forward_cone_finite hH hLE hlam hLam A c U ep).1
  have hex : ∀ᵐ p ∂stripExit hH hLE hlam hLam A c.activeInterval U ep,
      p ∈ reconstructionExit c.activeInterval (ep.1.time - 1) U := by
    rw [ae_iff]
    exact (strip_exit_probability hH hLE hlam hLam A c.activeInterval
      (ep.1.time - 1) U ep (by linarith)).2.1
  apply integral_eq_zero_of_ae
  filter_upwards [hc, hex] with p hp hx
  rcases hx with hx | hx
  · have ht : R ≤ (c.map e p).time := by
      have hp' : p.time - e.time ≤ 2 * c.r ^ 2 * (c.map e p).time := by
        simpa only [hep] using hp
      have hsqr := sq_pos_of_pos c.positive
      rw [hx.1] at hp'
      nlinarith
    exact (clockSourcePotential_regular hH hLE hlam hLam A c e R T hRT
      f hfn hs hz).2.2.1 _ ht
  · exact clockSourcePotential_pullback_zero_faces hH hLE hlam hLam A c e R T hRT
      f hfn hs hz p hx.2.2

/-- The literal full-test strip identity gives the weighted compact-probe integral.
All regularity, boundedness and the zero exit term are proved from the actual normalized solver. -/
theorem clock_weighted_test_finite
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point)
    (R T U : ℝ) (hRT : R < T) (hU : e.time + 2 * c.r ^ 2 * R ≤ U)
    (ep : StripPole c.activeInterval (U : WithTop ℝ)) (hep : ep.1 = e)
    (f : exitProbeSubmodule) (hfn : ∀ p, 0 ≤ exitProbePhysical f p)
    (hs : tsupport (exitProbePhysical f) ⊆
      {p | p.time < T ∧ p.velocity 0 ∈ clockNormalizedInterval.carrier})
    (hz : ∀ p, R ≤ p.time → exitProbePhysical f p = 0) :
    (∫ p, clockWeightedProbe c e f p ∂stripGreen hH hLE hlam hLam A c.activeInterval U ep) =
      (|c.vbar| * c.r ^ 2) * clockSourcePotential hH hLE hlam hLam A c e T f
        (sectionTwoPoint (c.map e e)) := by
  let u := (clockSourcePotential hH hLE hlam hLam A c e T f ∘ sectionTwoPoint) ∘ c.map e
  have hu := clock_pullback_C112 c e _
    (clockSourcePotential_regular hH hLE hlam hLam A c e R T hRT f hfn hs hz).2.1
  have hreg := clock_C112_mono hu
    (show reconstructionStrip c.activeInterval (ep.1.time - 1) U ⊆
      {p | p.velocity 0 ∈ c.active} from fun _ hp => hp.2.2)
  have hcont := clockSourcePotential_pullback_continuous hH hLE hlam hLam A c e R T hRT
    f hfn hs hz
  obtain ⟨M, hM⟩ := clockSourcePotential_pullback_bounded hH hLE hlam hLam A c e R T hRT
    f hfn hs hz
  have heU : ep.1.time < U := WithTop.coe_lt_coe.mp ep.2.1
  have hi := strip_identity_C112 hH hLE hlam hLam A c.activeInterval (ep.1.time - 1) U
    (by linarith) ep (by linarith) u hreg
    (hcont.mono (fun p hp => (nested_strip_union_exit_subset_closed c.activeInterval
      c.activeInterval subset_rfl (ep.1.time - 1) U hp).2))
    ⟨M, fun p hp => hM p hp.2.2⟩
  have hzero := clock_test_exit_zero hH hLE hlam hLam A c e R T U hRT hU ep hep
    f hfn hs hz
  have hsource : (fun p => forwardScalarOperator A.a u p) =ᵐ[
      stripGreen hH hLE hlam hLam A c.activeInterval U ep]
      fun p => -(1 / (|c.vbar| * c.r ^ 2)) * clockWeightedProbe c e f p := by
    filter_upwards [stripGreenOfKernel_ae_mem_stripPast c.activeInterval
      (stripEvolution hH hLE hlam hLam A c.activeInterval).2 U ep] with p hp
    exact (clockSourcePotential_physical_equation hH hLE hlam hLam A c e R T hRT
      f hfn hs hz p hp.2).trans (by dsimp [clockWeightedProbe]; ring)
  rw [integral_congr_ae hsource, integral_const_mul] at hi
  change u ep.1 = _ - _ at hi
  change (∫ p, u p ∂stripExit hH hLE hlam hLam A c.activeInterval U ep) = 0 at hzero
  rw [hzero] at hi
  have hv : |c.vbar| * c.r ^ 2 ≠ 0 :=
    ne_of_gt (mul_pos (abs_pos.mpr c.nonzero) (sq_pos_of_pos c.positive))
  have heval : u ep.1 = clockSourcePotential hH hLE hlam hLam A c e T f
      (sectionTwoPoint (c.map e e)) := congrArg u hep
  rw [heval] at hi
  have hi' : clockSourcePotential hH hLE hlam hLam A c e T f
      (sectionTwoPoint (c.map e e)) =
      (∫ p, clockWeightedProbe c e f p ∂stripGreen hH hLE hlam hLam A
        c.activeInterval U ep) / (|c.vbar| * c.r ^ 2) := hi.trans (by ring)
  exact ((eq_div_iff hv).mp hi').symm.trans (mul_comm _ _)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
