module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockGreenTestClosed

/-! # Actual uniform-in-spacetime bounds for a physical clock test -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic
open SectionTwo TheoremA Evolution

/-- The genuine clock potential and its literal physical source are bounded on the active strip. -/
theorem clockSourcePotential_pullback_bounded
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (R T : ℝ) (hRT : R < T)
    (f : exitProbeSubmodule) (hfn : ∀ p, 0 ≤ exitProbePhysical f p)
    (hs : tsupport (exitProbePhysical f) ⊆
      {p | p.time < T ∧ p.velocity 0 ∈ clockNormalizedInterval.carrier})
    (hz : ∀ p, R ≤ p.time → exitProbePhysical f p = 0) :
    ∃ M : ℝ, ∀ p, p.velocity 0 ∈ c.active →
      |((clockSourcePotential hH hLE hlam hLam A c e T f ∘ sectionTwoPoint) ∘
        c.map e) p| ≤ M ∧
      |forwardScalarOperator A.a
        ((clockSourcePotential hH hLE hlam hLam A c e T f ∘ sectionTwoPoint) ∘
          c.map e) p| ≤ M := by
  obtain ⟨C, -, hb⟩ :=
    (clockSourcePotential_regular hH hLE hlam hLam A c e R T hRT f hfn hs hz).1
  obtain ⟨M, hM⟩ := exitProbePhysical_bounded_source A f
  let D := |c.vbar| * c.r ^ 2
  have hD : 0 < D := mul_pos (abs_pos.mpr c.nonzero) (sq_pos_of_pos c.positive)
  refine ⟨max C ((3 * |c.vbar| / 2 / D) * max M 0), ?_⟩
  intro p hp
  refine ⟨(hb _).trans (le_max_left _ _), ?_⟩
  rw [clockSourcePotential_physical_equation hH hLE hlam hLam A c e R T hRT
    f hfn hs hz p hp, abs_mul, abs_neg,
    abs_of_nonneg (div_nonneg (abs_nonneg _) hD.le)]
  apply le_trans _ (le_max_right _ _)
  apply mul_le_mul
  · exact div_le_div_of_nonneg_right (c.active_abs_bounds hp).2 hD.le
  · exact (hM _).1.trans (le_max_left _ _)
  · exact abs_nonneg _
  · exact div_nonneg (by positivity) hD.le

/-- Restrict literal physical C112 regularity to a smaller set. -/
theorem clock_C112_mono {u : Point → ℝ} {D E : Set Point}
    (hu : IsKineticC112On u D) (hi : E ⊆ D) : IsKineticC112On u E :=
  ⟨hu.1.mono hi, fun p hp => hu.2.1 p (hi hp),
    fun p hp => hu.2.2.1 p (hi hp), fun p hp => hu.2.2.2.1 p (hi hp),
    hu.2.2.2.2.1.mono hi, hu.2.2.2.2.2.1.mono hi,
    hu.2.2.2.2.2.2.1.mono hi, hu.2.2.2.2.2.2.2.mono hi⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
