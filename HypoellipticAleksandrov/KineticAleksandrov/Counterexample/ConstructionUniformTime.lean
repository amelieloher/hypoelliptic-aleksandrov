module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionJointSource

/-! # Uniform bounds for the time representative on compact time intervals -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory Set HypoellipticAleksandrov.Parabolic

/-- The selected time representative is jointly measurable. -/
theorem construction_extendedTimeJet_joint_measurable {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R : ℝ) :
    Measurable (fun z : ℝ × XV d => constructionExtendedTimeJet h r mu R z.1 z.2) := by
  have hH := (selectedProfile_spec h).2.2.2.2.2.2.1
  have hm : Measurable ({z : ℝ × XV d | profileFunction h z.2 < 1}.indicator
      (fun z => kineticTimeDerivative
        (timeCutoffProfile (profileFunction h) alpha r mu R) ⟨z.1, z.2.1, z.2.2⟩)) :=
    (construction_rawTimeJet_joint_continuous h r mu R).measurable.indicator
      (isOpen_lt (hH.comp continuous_snd) continuous_const).measurableSet
  convert hm using 1
  funext z
  simp only [constructionExtendedTimeJet]
  by_cases hp : profileFunction h z.2 < 1 <;> simp [hp]

/-- The time representative is bounded globally in space, uniformly over compact time. -/
theorem construction_extendedTimeJet_uniform_bound {d : ℕ} {alpha : ℝ}
    (ha : 0 < alpha) (h : CounterProfileStatement d alpha) (r mu R a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, ∀ q,
      |constructionExtendedTimeJet h r mu R t q| ≤ C := by
  let K := Icc a b ×ˢ {q | profileFunction h q ≤ 1}
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_profile_unit_sublevel ha h)
  obtain ⟨C, hC, hb⟩ := construction_compact_scalar_bound K hK _
    (construction_rawTimeJet_joint_continuous h r mu R)
  refine ⟨C, hC, fun t ht q => ?_⟩
  by_cases hp : profileFunction h q < 1
  · have hq : q ∈ {y | profileFunction h y < 1} := hp
    rw [constructionExtendedTimeJet, indicator_of_mem hq]
    exact hb (t, q) ⟨ht, hp.le⟩
  · have hq : q ∉ {y | profileFunction h y < 1} := hp
    rw [constructionExtendedTimeJet, indicator_of_notMem hq, abs_zero]
    exact hC

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
