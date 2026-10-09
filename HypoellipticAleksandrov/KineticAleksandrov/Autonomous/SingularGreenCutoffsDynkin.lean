module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsC2
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionComparison
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TerminalMomentBoundsKernel
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceInterior
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceTraces

/-! # Derived whole-space Green formula for zero-terminal smooth tests

The potential is the actual evolution integral. Its weak equation, continuity,
and bounded comparison identify it with the supplied smooth test.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic SectionTwo Evolution Occupation Set MeasureTheory

/-- A C² test with a bounded terminal error obeys the same error bound against
its actual signed Green potential. No Green identity is taken as a premise. -/
theorem fullspace_green_terminal_error
    (hH : HormanderHypoellipticityStatement) {lam Lam : ℝ}
    (hlam : 0 < lam) (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E) (T : ℝ)
    (u g : Point → ℝ)
    (hu : ContDiffOn ℝ 2 (u ∘ evolutionHomeomorph 1)
      (evolutionHomeomorph 1 ⁻¹'
        evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T))
    (huc : ContinuousOn u
      (evolutionPastClosedCylinder autonomousWholeDomain (fun _ => 0) T))
    (hg : Measurable g) (Cu M : ℝ) (hM : 0 ≤ M)
    (hub : ∀ p, p.time ≤ T → |u p| ≤ Cu) (hgb : ∀ p, |g p| ≤ M)
    (hgz : ∀ p, T ≤ p.time → g p = 0)
    (δ : ℝ) (hut : ∀ p, p.time = T → |u p| ≤ δ)
    (hop : ∀ p, p.time < T →
      transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1) u p = -g p)
    (p₀ : Point) (hp₀ : p₀.time < T) : |duhamelPotential E.2 T g p₀ - u p₀| ≤ δ := by
  let D := evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T
  let U := evolutionHomeomorph 1 ⁻¹' D
  let W := duhamelPotential E.2 T g
  let v := fun p => W p - u p
  have hD : IsOpen D := isOpen_duhamelCylinder
    (isOpen_of_isAdmissibleEvolutionDomain autonomousWholeDomain_admissible)
    continuous_const T
  have hU : IsOpen U := hD.preimage (evolutionHomeomorph 1).continuous
  have hwk := duhamel_bounded_isKineticWeakTransportedSolution
    autonomousWholeDomain_admissible autonomousWholeDomain_measurable continuous_const
    (evolutionCoefficient A.a) (identityDrift 1) E.1 E.2 hE
    (evolutionCoefficient_smooth A) (evolutionCoefficient_symmetric A.a)
    (identityDrift_smooth 1) g hg M hM hgb T
  have hw : IsWeakTransportedSolution (evolutionCoefficient A.a) (identityDrift 1) U
      (W ∘ evolutionHomeomorph 1) ((fun p => -g p) ∘ evolutionHomeomorph 1) :=
    (isWeakTransportedSolution_comp_iff _ _ _ _ _).2 hwk
  have huw := c2_isWeakTransportedSolution A hU hu
  have hue : IsWeakTransportedSolution (evolutionCoefficient A.a) (identityDrift 1) U
      (u ∘ evolutionHomeomorph 1) ((fun p => -g p) ∘ evolutionHomeomorph 1) := by
    refine ⟨huw.1, ?_⟩
    intro ψ hψ hc hs
    rw [huw.2 ψ hψ hc hs]
    apply setIntegral_congr_fun hU.measurableSet
    intro x hx
    have he := transportedOperator_comp (B := evolutionCoefficient A.a)
      (b := identityDrift 1) ((hu.contDiffAt (hU.mem_nhds hx)).of_le (by simp)) (x := x)
    dsimp only [Function.comp_apply]
    rw [he, hop _ hx.1]
  have hvw := weak_same_source_sub A hw hue
  have hWc : ContinuousOn W D :=
    continuousOn_duhamelPotential_bounded_signed hH autonomousWholeDomain_admissible
      autonomousWholeDomain_measurable continuous_const (evolutionCoefficient A.a)
      (identityDrift 1) E.1 E.2 hE (evolutionCoefficient_smooth A)
      (evolutionCoefficient_symmetric A.a) (identityDrift_smooth 1)
      lam Lam 1 hlam one_pos (evolutionCoefficient_bounds A) (identityDrift_bounds 1).2
      T g hg M hM hgb (by
        intro p hp
        apply hgz p
        by_contra hn
        apply hp
        exact ⟨lt_of_not_ge hn, by
          change p.position ∈ movingDomain (wholeSpace 1) (fun _ => 0) p.time
          rw [movingDomain_wholeSpace]; trivial⟩)
  have hvc : ContinuousOn v D := hWc.sub (huc.mono (fun _ hp => ⟨hp.1.le, subset_closure hp.2⟩))
  have hvs : ContDiffOn ℝ (⊤ : ℕ∞) (v ∘ evolutionHomeomorph 1) U :=
    homogeneous_weak_contDiffOn hH hlam A hU hvw
      (hvc.comp (evolutionHomeomorph 1).continuous.continuousOn (fun _ hx => hx))
  have hve := duhamel_operator_eq_of_smooth_weak hU (evolutionCoefficient_smooth A)
    (evolutionCoefficient_symmetric A.a) (identityDrift_smooth 1) hvs
    continuousOn_const hvw
  have hvr (p : Point) (hp : p ∈ D) : IsSliceRegularAt v p :=
    reconstruction_slice_regular_of_contDiffOn hD hvs p hp
  have hvop (p : Point) (hp : p ∈ D) :
      transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1) v p = 0 := by
    have hx : (evolutionHomeomorph 1).symm p ∈ U := by
      simpa only [U, mem_preimage, Homeomorph.apply_symm_apply] using hp
    have he := hve _ hx
    rw [transportedOperator_comp ((hvs.contDiffAt (hU.mem_nhds hx)).of_le (by simp))] at he
    simpa only [Function.comp_apply, Homeomorph.apply_symm_apply] using he
  have hclosed : ContinuousOn v
      (evolutionPastClosedCylinder autonomousWholeDomain (fun _ => 0) T) := by
    intro p hp
    by_cases ht : p.time = T
    · exact ((continuousAt_duhamelPotential_terminal E.2 g M hM hgb T p ht).continuousWithinAt.sub
        (huc p hp))
    · apply (hvc p ⟨lt_of_le_of_ne hp.1 ht, ?_⟩).continuousAt
        (hD.mem_nhds ⟨lt_of_le_of_ne hp.1 ht, ?_⟩) |>.continuousWithinAt
      all_goals
        change p.position ∈ movingDomain (wholeSpace 1) (fun _ => 0) p.time
        rw [movingDomain_wholeSpace]; trivial
  have hvterm (p : Point) (ht : p.time = T) : |v p| ≤ δ := by
    dsimp [v, W]
    rw [duhamelPotential_eq_zero_of_terminal_le E.2 T g p ht.ge, zero_sub, abs_neg]
    exact hut p ht
  have hbound (p : Point) (hp : p ∈ movingClosedSlab autonomousWholeDomain
      (fun _ => 0) p₀.time T) : |v p| ≤ (T - p₀.time) * M + Cu := by
    have hh := abs_duhamelPotential_le_abs_time E.2 g M hM hgb p T
    dsimp [v, W]
    calc
      |duhamelPotential E.2 T g p - u p| ≤
          |duhamelPotential E.2 T g p| + |u p| := abs_sub _ _
      _ ≤ |T - p.time| * M + Cu := add_le_add hh (hub p hp.2.1)
      _ ≤ (T - p₀.time) * M + Cu := by
        rw [abs_of_nonneg (sub_nonneg.mpr hp.2.1)]
        exact add_le_add (mul_le_mul_of_nonneg_right (by linarith [hp.1]) hM) le_rfl
  have hcmp (f : Point → ℝ) (hfc : ContinuousOn f
      (evolutionPastClosedCylinder autonomousWholeDomain (fun _ => 0) T))
      (hfr : ∀ p ∈ D, IsSliceRegularAt f p)
      (hfo : ∀ p ∈ D, transportedForwardOperator (evolutionCoefficient A.a)
        (identityDrift 1) f p = 0)
      (hft : ∀ p, p.time = T → f p ≤ δ)
      (hfb : ∀ p ∈ movingClosedSlab autonomousWholeDomain (fun _ => 0) p₀.time T,
        |f p| ≤ (T - p₀.time) * M + Cu) : f p₀ ≤ δ := by
    have hh := growth_comparison
      (isOpen_of_isAdmissibleEvolutionDomain autonomousWholeDomain_admissible)
      continuous_const hlam (evolutionCoefficient_bounds A) (identityDrift_bounds 1).1
      (le_refl 0) zero_le_one (a := p₀.time) (T := T) (u := fun p => f p - δ)
      ⟨_, fun p hp => sub_le_sub_right ((le_abs_self _).trans (hfb p hp)) δ⟩
      ((hfc.sub continuousOn_const).mono (fun _ hp => ⟨hp.2.1, hp.2.2⟩))
      (fun p hp => (hfr p ⟨hp.2.1, hp.2.2⟩).sub (IsSliceRegularAt.const δ p))
      (fun p hp => by
        rw [viscousTransportedOperator_sub (hfr p ⟨hp.2.1, hp.2.2⟩)
          (IsSliceRegularAt.const δ p), viscousTransportedOperator_const,
          viscousTransportedOperator_zero, hfo p ⟨hp.2.1, hp.2.2⟩]
        norm_num)
      (fun p _ ht => sub_nonpos.mpr (hft p ht))
      (fun p _ hf => by
        change p.position ∈ frontier (movingDomain (wholeSpace 1) (fun _ => 0) p.time) at hf
        rw [movingDomain_wholeSpace, frontier_univ] at hf
        exact False.elim hf)
    apply sub_nonpos.mp
    exact hh p₀ ⟨le_rfl, hp₀.le, by
      change p₀.position ∈ closure (movingDomain (wholeSpace 1) (fun _ => 0) p₀.time)
      rw [movingDomain_wholeSpace, closure_univ]; trivial⟩
  have h1 := hcmp v hclosed hvr hvop (fun p ht => (le_abs_self _).trans (hvterm p ht)) hbound
  have h2 := hcmp (fun p => -v p) hclosed.neg (fun p hp => (hvr p hp).neg)
    (fun p hp => by
      have hh := viscousTransportedOperator_const_mul
        (B := evolutionCoefficient A.a) (b := identityDrift 1) (ε := 0) (-1) (hvr p hp)
      rw [viscousTransportedOperator_zero, viscousTransportedOperator_zero,
        hvop p hp, mul_zero] at hh
      simpa only [neg_one_mul] using hh)
    (fun p ht => (neg_le_abs _).trans (hvterm p ht))
    (fun p hp => by rw [abs_neg]; exact hbound p hp)
  exact abs_le.mpr ⟨by linarith only [h2], h1⟩

/-- A zero-terminal C² test equals its actual signed source potential. -/
theorem fullspace_green_zero_terminal
    (hH : HormanderHypoellipticityStatement) {lam Lam : ℝ}
    (hlam : 0 < lam) (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E) (T : ℝ)
    (u g : Point → ℝ)
    (hu : ContDiffOn ℝ 2 (u ∘ evolutionHomeomorph 1)
      (evolutionHomeomorph 1 ⁻¹'
        evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T))
    (huc : ContinuousOn u
      (evolutionPastClosedCylinder autonomousWholeDomain (fun _ => 0) T))
    (hg : Measurable g) (Cu M : ℝ) (hM : 0 ≤ M)
    (hub : ∀ p, p.time ≤ T → |u p| ≤ Cu) (hgb : ∀ p, |g p| ≤ M)
    (hgz : ∀ p, T ≤ p.time → g p = 0)
    (hut : ∀ p, p.time = T → u p = 0)
    (hop : ∀ p, p.time < T →
      transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1) u p = -g p)
    (p₀ : Point) (hp₀ : p₀.time < T) : duhamelPotential E.2 T g p₀ = u p₀ := by
  have hh := fullspace_green_terminal_error hH hlam A E hE T u g hu huc hg Cu M hM
    hub hgb hgz 0 (fun p hp => by rw [hut p hp, abs_zero]) hop p₀ hp₀
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hh)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
