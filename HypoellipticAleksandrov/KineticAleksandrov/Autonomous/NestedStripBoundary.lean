module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripSource

/-! # Exact interval closure and the actual compact-source exit traces -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution

/-- The native one-dimensional interval closure is exactly the physical scalar closed interval. -/
theorem nested_intervalDomain_closure_iff (H : Interval) (v : PDE.Vec 1) :
    v ∈ closure (intervalDomain H) ↔ H.lo ≤ v 0 ∧ v 0 ≤ H.hi := by
  let e := (ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 => ℝ)).toHomeomorph
  have hset : intervalDomain H = e ⁻¹' Ioo H.lo H.hi := by
    ext w
    rw [intervalDomain, PDE.mem_oneDimensionalAxisBox_iff]
    rfl
  rw [hset, ← e.preimage_closure, closure_Ioo H.ordered.ne]
  rfl

/-- Either scalar endpoint is a genuine native velocity frontier point. -/
theorem nested_intervalDomain_frontier_of_endpoint (H : Interval) (v : PDE.Vec 1)
    (hv : v 0 = H.lo ∨ v 0 = H.hi) : v ∈ frontier (intervalDomain H) := by
  rw [frontier,
    (isOpen_of_isAdmissibleEvolutionDomain (intervalDomain_admissible H)).interior_eq]
  refine ⟨(nested_intervalDomain_closure_iff H v).mpr ?_, ?_⟩
  · rcases hv with hv | hv <;> rw [hv]
    · exact ⟨le_rfl, H.ordered.le⟩
    · exact ⟨H.ordered.le, le_rfl⟩
  · intro hm
    have hb := PDE.mem_oneDimensionalAxisBox_iff.mp hm
    change H.lo < v 0 ∧ v 0 < H.hi at hb
    rcases hv with hv | hv <;> rw [hv] at hb
    · exact (lt_irrefl _ hb.1)
    · exact (lt_irrefl _ hb.2)

/-- Compact source potentials are continuous on the literal physical closed past and zero
on both terminal and lateral exits of their own interval. -/
theorem nestedSourcePotential_continuous_zero_exit
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (f : exitProbeSubmodule)
    (hfn : ∀ p, 0 ≤ exitProbePhysical f p)
    (hs : tsupport (exitProbePhysical f) ⊆ {p | p.time < T ∧ p.velocity 0 ∈ H.carrier}) :
    ContinuousOn (nestedSourcePotential H E T f)
      {p | p.time ≤ T ∧ p.velocity 0 ∈ Icc H.lo H.hi} ∧
    (∀ p, p.time = T → nestedSourcePotential H E T f p = 0) ∧
    (∀ p, p.velocity 0 = H.lo ∨ p.velocity 0 = H.hi →
      nestedSourcePotential H E T f p = 0) := by
  have hgc := (exitProbePhysical_continuous_compact f).2.comp_homeomorph
    (sectionTwoHomeomorph 1)
  obtain ⟨-, -, -, -, -, hc, ht, hv, -⟩ :=
    kinetic_duhamel hH (by omega) (intervalDomain_admissible H) (zeroCurve_piecewiseC1 1)
      hlam hLam one_pos (evolutionCoefficient A.a) (evolutionCoefficient_smooth A)
      (evolutionCoefficient_symmetric A.a) (evolutionCoefficient_bounds A)
      (identityDrift 1) (identityDrift_smooth 1) (identityDrift_bounds 1)
      E.1 E.2 hE T (exitProbePhysical f ∘ sectionTwoPoint) (fun p => hfn _)
      (nested_native_probe_raw_smooth f) hgc (nested_native_probe_source_support H T f hs)
  refine ⟨hc.comp (continuous_sectionTwoPoint 1).continuousOn ?_,
    fun p hp => ht (sectionTwoPoint p) hp, fun p hp => hv (sectionTwoPoint p) ?_⟩
  · intro p hp
    change p.time ≤ T ∧ p.velocity ∈ closure (movingDomain (intervalDomain H) (fun _ => 0) p.time)
    refine ⟨hp.1, ?_⟩
    rw [mem_closure_movingDomain_iff, sub_zero]
    exact (nested_intervalDomain_closure_iff H p.velocity).mpr hp.2
  · rw [mem_frontier_movingDomain_iff, sub_zero]
    exact nested_intervalDomain_frontier_of_endpoint H p.velocity hp

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
