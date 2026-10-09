module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockGreenTestSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripBoundary

/-! # Genuine continuity and lateral traces of normalized clock tests -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution
open scoped Topology

/-- Past closed-strip continuity and an earlier zero half-space give full closed-strip
  continuity. -/
theorem clock_continuous_of_zero_after (u : Point → ℝ) (R T : ℝ) (hRT : R < T)
    (hu : ContinuousOn u {p | p.time ≤ T ∧
      p.position ∈ closure (intervalDomain clockNormalizedInterval)})
    (hz : ∀ p, R ≤ p.time → u p = 0) :
    ContinuousOn u {p | p.position ∈ closure (intervalDomain clockNormalizedInterval)} := by
  intro p hp
  by_cases ht : p.time < T
  · apply (hu p ⟨ht.le, hp⟩).mono_of_mem_nhdsWithin
    have hn : ∀ᶠ q in 𝓝 p, q.time < T :=
      (isOpen_lt continuous_time continuous_const).mem_nhds ht
    filter_upwards [hn.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with q hq hmem
    exact ⟨hq.le, hmem⟩
  · have hRp : R < p.time := hRT.trans_le (not_lt.mp ht)
    have hn : ∀ᶠ q in 𝓝 p, R < q.time :=
      (isOpen_lt continuous_const continuous_time).mem_nhds hRp
    have heq : u =ᶠ[𝓝 p] (fun _ => (0 : ℝ)) := hn.mono (fun q hq => hz q hq.le)
    exact (continuousAt_const.congr_of_eventuallyEq heq).continuousWithinAt

/-- The actual normalized test is continuous on the full closed velocity strip and zero on
both lateral faces; the boundary conclusions come from the genuine Duhamel theorem. -/
theorem clockSourcePotential_boundary
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (R T : ℝ) (hRT : R < T)
    (f : exitProbeSubmodule) (hfn : ∀ p, 0 ≤ exitProbePhysical f p)
    (hs : tsupport (exitProbePhysical f) ⊆
      {p | p.time < T ∧ p.velocity 0 ∈ clockNormalizedInterval.carrier})
    (hz : ∀ p, R ≤ p.time → exitProbePhysical f p = 0) :
    ContinuousOn (clockSourcePotential hH hLE hlam hLam A c e T f)
      {p | p.position ∈ closure (intervalDomain clockNormalizedInterval)} ∧
    (∀ p, p.position 0 = -3 / 4 ∨ p.position 0 = 3 / 4 →
      clockSourcePotential hH hLE hlam hLam A c e T f p = 0) := by
  let E := clockEvolution hH hLE hlam hLam A c e
  have hsetting := c.extended_sourceSetting hlam hLam A e
  obtain ⟨hBs, hBsym, hBell⟩ := sectionTwoCoefficient_fullBounds (3 * lam / 5) (3 * Lam)
    (c.extendedCoefficient lam A.a e) hsetting.1
  obtain ⟨-, -, -, -, -, hc, -, hv, -⟩ :=
    kinetic_duhamel hH (by omega)
      (intervalDomain_admissible clockNormalizedInterval) (zeroCurve_piecewiseC1 1)
      (by positivity : 0 < 3 * lam / 5) (by linarith : 3 * lam / 5 ≤ 3 * Lam)
      (by norm_num : (0 : ℝ) < 9 / 25)
      (zIndependentCoefficient (c.extendedCoefficient lam A.a e)) hBs hBsym hBell
      c.extendedVectorDrift hsetting.2.1 hsetting.2.2.2.2.1 E.1 E.2
      (clockEvolution_spec hH hLE hlam hLam A c e) T
      (exitProbePhysical f ∘ sectionTwoPoint) (fun p => hfn _)
      (nested_native_probe_raw_smooth f)
      ((exitProbePhysical_continuous_compact f).2.comp_homeomorph (sectionTwoHomeomorph 1))
      (nested_native_probe_source_support clockNormalizedInterval T f hs)
  have hzero := (clockSourcePotential_regular hH hLE hlam hLam A c e R T hRT
    f hfn hs hz).2.2.1
  refine ⟨clock_continuous_of_zero_after _ R T hRT ?_ hzero, ?_⟩
  · apply hc.mono
    intro p hp
    refine ⟨hp.1, ?_⟩
    rw [mem_closure_movingDomain_iff, sub_zero]
    exact hp.2
  · intro p hp
    apply hv p
    rw [mem_frontier_movingDomain_iff, sub_zero]
    exact nested_intervalDomain_frontier_of_endpoint clockNormalizedInterval p.position hp

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
