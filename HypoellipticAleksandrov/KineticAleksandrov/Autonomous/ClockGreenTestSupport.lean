module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockGreenTest

/-! # Compact clock tests have a genuine late cutoff -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution

/-- A compact physical probe has a strictly positive cutoff above its entire time support. -/
theorem clock_probe_cutoff (f : exitProbeSubmodule) :
    ∃ R : ℝ, 0 < R ∧
      (∀ p ∈ tsupport (exitProbePhysical f), p.time < R) ∧
      (∀ p, R ≤ p.time → exitProbePhysical f p = 0) := by
  have hc := (exitProbePhysical_continuous_compact f).2
  obtain ⟨b, hb⟩ := (hc.image continuous_time).bddAbove
  refine ⟨max b 0 + 1, by have := le_max_right b 0; linarith, ?_, ?_⟩
  · intro p hp
    have ht := hb (show p.time ∈ KineticPoint.time '' tsupport (exitProbePhysical f)
      from ⟨p, hp, rfl⟩)
    have := le_max_left b 0
    linarith
  · intro p hp
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    have ht := hb (show p.time ∈ KineticPoint.time '' tsupport (exitProbePhysical f)
      from ⟨p, hs, rfl⟩)
    have := le_max_left b 0
    linarith

/-- Every nonnegative compact interior clock probe produces a bounded, globally strip-smooth
actual test with the exact physical source equation and a proved late cutoff. -/
theorem clock_potential_test
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point)
    (f : exitProbeSubmodule) (hfn : ∀ p, 0 ≤ exitProbePhysical f p)
    (hs : tsupport (exitProbePhysical f) ⊆
      {p | 0 < p.time ∧ p.velocity 0 ∈ normalizedActive}) :
    ∃ R : ℝ, ∃ h : Point → ℝ, 0 < R ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ p, |h p| ≤ C) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (h ∘ scalarPoint)
        {q : Fin 3 → ℝ | q 2 ∈ normalizedActive} ∧
      (∀ p, R ≤ p.time → h p = 0) ∧
      (∀ p, p.velocity 0 ∈ c.active → forwardScalarOperator A.a (h ∘ c.map e) p =
        -(|p.velocity 0| / (|c.vbar| * c.r ^ 2)) * exitProbePhysical f (c.map e p)) := by
  obtain ⟨R, hR, ht, hz⟩ := clock_probe_cutoff f
  have hs' : tsupport (exitProbePhysical f) ⊆
      {p | p.time < R + 1 ∧ p.velocity 0 ∈ clockNormalizedInterval.carrier} := by
    intro p hp
    exact ⟨by linarith [ht p hp], (hs hp).2⟩
  obtain ⟨hb, hsm, hzero, -⟩ :=
    clockSourcePotential_regular hH hLE hlam hLam A c e R (R + 1) (by linarith)
      f hfn hs' hz
  refine ⟨R, clockSourcePotential hH hLE hlam hLam A c e (R + 1) f ∘ sectionTwoPoint,
    hR, ?_, hsm, ?_, ?_⟩
  · obtain ⟨C, hC, hbound⟩ := hb
    exact ⟨C, hC, fun p => hbound _⟩
  · intro p hp
    exact hzero (sectionTwoPoint p) hp
  · intro p hp
    exact clockSourcePotential_physical_equation hH hLE hlam hLam A c e R (R + 1)
      (by linarith) f hfn hs' hz p hp

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
