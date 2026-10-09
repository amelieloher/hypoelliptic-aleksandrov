module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockGreenTestGerm

/-! # Actual normalized clock source potentials and their global strip equation -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution

/-- The clock test is the genuine normalized killed Duhamel potential. -/
def clockSourcePotential
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (T : ℝ)
    (f : exitProbeSubmodule) : Point → ℝ :=
  duhamelPotential (clockEvolution hH hLE hlam hLam A c e).2 T
    (exitProbePhysical f ∘ sectionTwoPoint)

/-- The actual clock test is bounded, smooth on the whole normalized strip, vanishes late,
and solves the literal extended transported equation there. -/
theorem clockSourcePotential_regular
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (R T : ℝ) (hRT : R < T)
    (f : exitProbeSubmodule) (hfn : ∀ p, 0 ≤ exitProbePhysical f p)
    (hs : tsupport (exitProbePhysical f) ⊆
      {p | p.time < T ∧ p.velocity 0 ∈ clockNormalizedInterval.carrier})
    (hz : ∀ p, R ≤ p.time → exitProbePhysical f p = 0) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ p,
      |clockSourcePotential hH hLE hlam hLam A c e T f p| ≤ C) ∧
    ContDiffOn ℝ (⊤ : ℕ∞)
      ((clockSourcePotential hH hLE hlam hLam A c e T f ∘ sectionTwoPoint) ∘ scalarPoint)
      {q : Fin 3 → ℝ | q 2 ∈ normalizedActive} ∧
    (∀ p, R ≤ p.time → clockSourcePotential hH hLE hlam hLam A c e T f p = 0) ∧
    (∀ p, p.position ∈ intervalDomain clockNormalizedInterval →
      transportedForwardOperator (zIndependentCoefficient (c.extendedCoefficient lam A.a e))
        c.extendedVectorDrift (clockSourcePotential hH hLE hlam hLam A c e T f) p =
          -exitProbePhysical f (sectionTwoPoint p)) := by
  let E := clockEvolution hH hLE hlam hLam A c e
  have hsetting := c.extended_sourceSetting hlam hLam A e
  obtain ⟨hBs, hBsym, hBell⟩ := sectionTwoCoefficient_fullBounds (3 * lam / 5) (3 * Lam)
    (c.extendedCoefficient lam A.a e) hsetting.1
  have hgc := (exitProbePhysical_continuous_compact f).2.comp_homeomorph
    (sectionTwoHomeomorph 1)
  obtain ⟨⟨-, C, hC, hb⟩, -, hsm, -, hop, -, -, -, -⟩ :=
    kinetic_duhamel hH (by omega)
      (intervalDomain_admissible clockNormalizedInterval) (zeroCurve_piecewiseC1 1)
      (by positivity : 0 < 3 * lam / 5) (by linarith : 3 * lam / 5 ≤ 3 * Lam)
      (by norm_num : (0 : ℝ) < 9 / 25)
      (zIndependentCoefficient (c.extendedCoefficient lam A.a e)) hBs hBsym hBell
      c.extendedVectorDrift hsetting.2.1 hsetting.2.2.2.2.1 E.1 E.2
      (clockEvolution_spec hH hLE hlam hLam A c e) T
      (exitProbePhysical f ∘ sectionTwoPoint) (fun p => hfn _)
      (nested_native_probe_raw_smooth f) hgc
      (nested_native_probe_source_support clockNormalizedInterval T f hs)
  have hzero : ∀ p, R ≤ p.time → duhamelPotential E.2 T
      (exitProbePhysical f ∘ sectionTwoPoint) p = 0 := by
    intro p hp
    exact clock_duhamel_zero_after E.2 T R (exitProbePhysical f ∘ sectionTwoPoint)
      (fun q hq => hz (sectionTwoPoint q) hq) p hp
  refine ⟨⟨C, hC, hb⟩,
    clock_native_smooth_to_scalar _
      (clock_native_smooth_of_zero_after _ R T hRT hsm hzero), hzero, ?_⟩
  intro p hp
  by_cases ht : p.time < T
  · exact hop p ⟨ht, mem_movingDomain_iff.mpr (by simpa using hp)⟩
  · have hRp : R < p.time := hRT.trans_le (not_lt.mp ht)
    exact (clock_transport_operator_zero_after _ _ _ R hzero p hRp).trans
      (by rw [hz (sectionTwoPoint p) hRp.le]; simp)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
