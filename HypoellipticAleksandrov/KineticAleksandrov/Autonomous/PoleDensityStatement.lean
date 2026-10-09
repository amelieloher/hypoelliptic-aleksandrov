module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PoleDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PushforwardStatement

/-! # The clock proposition from the interval density estimate -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open scoped ENNReal

/-- Strict clock-time support gives the source's signed spatial concentration. -/
theorem clock_signed_concentration
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) :
    stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e he)
      {z | ¬0 < Real.sign c.vbar * (z.position 0 - e.position 0)} = 0 := by
  apply (ae_iff).mp
  filter_upwards [stripGreen_infinite_ae_future_carrier hH hLE hlam hLam A c.activeInterval
    (densityClockPole c e he),
    clock_forward_cone_infinite hH hLE hlam hLam A c (densityClockPole c e he)] with p hp hc
  have hs : 0 < (c.map e p).time := by
    have ht : e.time < p.time := hp.1
    change p.time - e.time ≤ 2 * c.r ^ 2 * (c.map e p).time at hc
    nlinarith [sq_pos_of_pos c.positive]
  change 0 < (p.position 0 - e.position 0) / (c.vbar * c.r ^ 2) at hs
  rcases lt_or_gt_of_ne c.nonzero with hv | hv
  · have hd : c.vbar * c.r ^ 2 < 0 := mul_neg_of_neg_of_pos hv (sq_pos_of_pos c.positive)
    have hx := (div_pos_iff.mp hs).resolve_left (by simp [hd.not_gt])
    simp only [Real.sign_of_neg hv, neg_one_mul]
    exact neg_pos.mpr hx.1
  · have hd : 0 < c.vbar * c.r ^ 2 := mul_pos hv (sq_pos_of_pos c.positive)
    have hx := (div_pos_iff.mp hs).resolve_right (fun hn => (not_lt_of_ge hd.le) hn.2)
    simpa only [Real.sign_of_pos hv, one_mul] using hx.1

/-- The clock proposition follows from the interval density estimate, with the Dirichlet
solvability hypothesis kept explicit rather than hidden in the proposition. -/
theorem pushforwardStatement_holds :
    PushforwardStatement := by
  intro hH hLE lam Lam hlam hLam
  constructor
  · intro A c e he
    exact ⟨clock_signed_concentration hH hLE hlam hLam A c e he,
      clock_green_pushforward hH hLE hlam hLam A c e he⟩
  · intro q hq
    obtain ⟨C, hC, hc⟩ := one_sign_pole_density hH hLE hlam hLam q hq.1 hq.2
    refine ⟨C, hC, ?_⟩
    intro A c e he
    obtain ⟨G, hGm, hGn, hGE, hGN, hGs⟩ := hc A c e he
    have hS : MeasurableSet (densityClockStrip c e) :=
      (isOpen_lt continuous_const continuous_time).measurableSet.inter
        (isOpen_Ioo.preimage ((continuous_apply 0).comp continuous_velocity)).measurableSet
    have hbound := (eLpNorm_mono_measure G
      (Measure.restrict_le_self (μ := (volume : Measure Point))
        (s := densityClockStrip c e))).trans hGN
    have hfinite := hbound.trans_lt (ENNReal.ofReal_lt_top)
    refine ⟨G, hGm, hGn, ?_, hfinite, ?_⟩
    · calc
        _ = (stripGreen hH hLE hlam hLam A c.activeInterval ⊤
            (densityClockPole c e he)).restrict (densityClockStrip c e) :=
          (Measure.restrict_eq_self_of_ae_mem hGs).symm
        _ = _ := (congrArg (fun μ : Measure Point =>
          μ.restrict (densityClockStrip c e)) hGE).trans
            (restrict_withDensity hS _)
    · exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq
        (ENNReal.toReal_ofReal (mul_nonneg hC.le (Real.rpow_nonneg c.positive.le _)))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
