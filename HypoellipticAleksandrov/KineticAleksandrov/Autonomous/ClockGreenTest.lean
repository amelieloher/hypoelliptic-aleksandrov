module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockGreenTestSource

/-! # The genuine normalized Duhamel test satisfies the physical clock equation -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic
open SectionTwo TheoremA Evolution

/-- Local and extended normalized operators agree on the normalized active strip. -/
theorem clock_extended_operator_eq {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (c : Clock) (e : Point) (u : Point → ℝ) (p : Point)
    (hp : p.position 0 ∈ normalizedActive) :
    transportedForwardOperator (c.normalizedCoefficient A.a e) c.normalizedDrift u p =
      transportedForwardOperator (zIndependentCoefficient (c.extendedCoefficient lam A.a e))
        c.extendedVectorDrift u p := by
  have hB : fullKineticCoefficientAt (c.normalizedCoefficient A.a e) p =
      fullKineticCoefficientAt (zIndependentCoefficient (c.extendedCoefficient lam A.a e)) p := by
    ext i j
    exact (c.extendedDiffusion_eq A.a e p.time (p.position 0) hp).symm
  have hb : c.normalizedDrift p.position = c.extendedVectorDrift p.position := by
    ext i
    exact (c.extendedDrift_eq hp).symm
  rw [transportedForwardOperator_apply, transportedForwardOperator_apply, hB, hb]

/-- The actual normalized compact-source test obeys the exact physical weighted source equation. -/
theorem clockSourcePotential_physical_equation
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (R T : ℝ) (hRT : R < T)
    (f : exitProbeSubmodule) (hfn : ∀ p, 0 ≤ exitProbePhysical f p)
    (hs : tsupport (exitProbePhysical f) ⊆
      {p | p.time < T ∧ p.velocity 0 ∈ clockNormalizedInterval.carrier})
    (hz : ∀ p, R ≤ p.time → exitProbePhysical f p = 0)
    (p : Point) (hp : p.velocity 0 ∈ c.active) :
    forwardScalarOperator A.a
      ((clockSourcePotential hH hLE hlam hLam A c e T f ∘ sectionTwoPoint) ∘ c.map e) p =
        -(|p.velocity 0| / (|c.vbar| * c.r ^ 2)) * exitProbePhysical f (c.map e p) := by
  obtain ⟨-, hsm, -, hop⟩ :=
    clockSourcePotential_regular hH hLE hlam hLam A c e R T hRT f hfn hs hz
  rw [c.conjugacy A.a e _ hsm p hp]
  have hi : (sectionTwoPoint (c.map e p)).position 0 ∈ normalizedActive :=
    (c.mem_active_iff (p.velocity 0)).mp hp
  rw [clock_extended_operator_eq A c e _ _ hi]
  have heq : (clockSourcePotential hH hLE hlam hLam A c e T f ∘ sectionTwoPoint) ∘
      sectionTwoPoint = clockSourcePotential hH hLE hlam hLam A c e T f := by
    funext q
    exact congrArg _ (sectionTwoPoint_involutive q)
  rw [heq, hop]
  · rw [sectionTwoPoint_involutive]
    ring
  · rw [intervalDomain, PDE.mem_oneDimensionalAxisBox_iff]
    exact hi

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
