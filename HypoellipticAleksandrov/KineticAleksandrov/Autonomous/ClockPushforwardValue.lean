module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockPushforwardTests
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonGreenSupport

/-! # Actual clock Duhamel values equal the normalized infinite Green test integral -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution

/-- The physical normalized initial pole has time and transported coordinate zero. -/
def clockPhysicalPole (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) :
    StripPole clockNormalizedInterval ⊤ :=
  ⟨⟨0, fun _ => 0, fun _ => (e.velocity 0 - c.vbar) / c.r⟩,
    WithTop.coe_lt_top _, (c.mem_active_iff (e.velocity 0)).mp he⟩

/-- The literal position clock sends its source pole to the normalized initial pole. -/
theorem clock_map_pole (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) :
    c.map e e = (clockPhysicalPole c e he).1 := by
  ext i <;> simp [Clock.map, clockPhysicalPole]

/-- The actual physical normalized Green is exactly the established strip map of the same kernel. -/
theorem clockGreen_eq_stripGreenOfKernel
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) :
    clockGreen hH hLE hlam hLam A c e he =
      stripGreenOfKernel clockNormalizedInterval (clockEvolution hH hLE hlam hLam A c e).2
        ⊤ (clockPhysicalPole c e he) := rfl

/-- Late vanishing identifies the genuine clock test value with the actual infinite Green
  integral. -/
theorem clockSourcePotential_eq_infinite_green
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active)
    (R T : ℝ) (hT : 0 < T) (hRT : R < T) (f : exitProbeSubmodule)
    (hz : ∀ p, R ≤ p.time → exitProbePhysical f p = 0) :
    clockSourcePotential hH hLE hlam hLam A c e T f (sectionTwoPoint (c.map e e)) =
      ∫ p, exitProbePhysical f p ∂clockGreen hH hLE hlam hLam A c e he := by
  let ep := stripPoleFinite clockNormalizedInterval (clockPhysicalPole c e he) T hT
  have hv := nestedSourcePotential_eq_green A clockNormalizedInterval
    (clockEvolution hH hLE hlam hLam A c e) T f ep
  have hleft : clockSourcePotential hH hLE hlam hLam A c e T f
      (sectionTwoPoint (c.map e e)) = nestedSourcePotential clockNormalizedInterval
        (clockEvolution hH hLE hlam hLam A c e) T f ep.1 := by
    rw [clock_map_pole c e he]
    rfl
  have hr := stripGreenOfKernel_horizonRestriction clockNormalizedInterval
    (clockEvolution hH hLE hlam hLam A c e).2 T ep
  have hep : stripPoleInfinite clockNormalizedInterval T ep = clockPhysicalPole c e he :=
    Subtype.ext rfl
  have heq := congrArg (stripGreenOfKernel clockNormalizedInterval
    (clockEvolution hH hLE hlam hLam A c e).2 ⊤) hep
  have hm := (congrArg (fun μ : Measure Point => μ.restrict {p | p.time < T}) heq).trans
    (congrArg (fun μ : Measure Point => μ.restrict {p | p.time < T})
      (clockGreen_eq_stripGreenOfKernel hH hLE hlam hLam A c e he).symm)
  have hrestricted := hr.trans hm
  exact hleft.trans (hv.trans ((congrArg (fun μ : Measure Point =>
    ∫ p, exitProbePhysical f p ∂μ) hrestricted).trans
    (setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp =>
      hz p (hRT.le.trans (not_lt.mp hp))))))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
