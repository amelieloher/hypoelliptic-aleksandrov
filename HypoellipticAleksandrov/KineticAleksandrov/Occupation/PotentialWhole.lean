module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamel

/-!
# Proposition 4.2: the parabolic source potential on the whole space

In the whole-space case (`Ω = ℝ^d`, stationary curve, `σ₀ = 0`, `S = 1`) and for
`0 ≤ F ∈ C_c^∞((0,1) × ℝ^d)`, the source potential
`W(r, v) = ∫_r^1 ∫ F(t, w) P_{r,t}(v, dw) dt` is nonnegative, bounded by `‖F‖_∞` on
`[0,1] × ℝ^d`, vanishes at `r = 1`, and is a classical solution of
`∂_r W + B : D_v² W = -F` (smooth in `r < 1`).  This is the whole-space case of the parabolic
Duhamel lemma.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

variable {d : ℕ}

/-- In the whole-space case the starting set is the open half-space `{r < T}`. -/
theorem duhamelFiber_wholeSpace (T : ℝ) :
    duhamelFiber (wholeSpace d) (fun _ => (0 : PDE.Vec d)) T = {p | p.1 < T} := by
  ext p
  simp only [duhamelFiber, movingDomain_wholeSpace, mem_univ, and_true, mem_ofPred_eq]

/-- **Proposition 4.2.** -/
theorem occupation_potential (hH : HormanderHypoellipticityStatement) {lam Lam : ℝ}
    {B : CoefficientField d} (hB : IsSectionTwoCoefficient lam Lam B)
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hP : HasParabolicMarginalBundle (wholeSpace d) (fun _ => (0 : PDE.Vec d))
      (measurableSet_of_isAdmissibleEvolutionDomain (wholeSpace_admissible d))
      (zIndependentCoefficient B) K)
    (F : TimeVelocity d → ℝ) (hF0 : ∀ p, 0 ≤ F p) (hFs : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (hFsupp : tsupport F ⊆ Ioo (0 : ℝ) 1 ×ˢ univ) :
    (∀ p, 0 ≤ parabolicDuhamelPotential K
        (measurableSet_of_isAdmissibleEvolutionDomain (wholeSpace_admissible d)) 1 F p) ∧
      BddAbove ((parabolicDuhamelPotential K
        (measurableSet_of_isAdmissibleEvolutionDomain (wholeSpace_admissible d)) 1 F) ''
          (Icc (0 : ℝ) 1 ×ˢ univ)) ∧
      sSup ((parabolicDuhamelPotential K
        (measurableSet_of_isAdmissibleEvolutionDomain (wholeSpace_admissible d)) 1 F) ''
          (Icc (0 : ℝ) 1 ×ˢ univ)) ≤ ⨆ z, F z ∧
      (∀ v, parabolicDuhamelPotential K
        (measurableSet_of_isAdmissibleEvolutionDomain (wholeSpace_admissible d)) 1 F (1, v) = 0) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (parabolicDuhamelPotential K
        (measurableSet_of_isAdmissibleEvolutionDomain (wholeSpace_admissible d)) 1 F)
        {p : TimeVelocity d | p.1 < 1} ∧
      ∀ p : TimeVelocity d, p.1 < 1 →
        scalarParabolicOperator B (fun _ _ => 0) (parabolicDuhamelPotential K
          (measurableSet_of_isAdmissibleEvolutionDomain (wholeSpace_admissible d)) 1 F) p =
          -F p := by
  have hΩ := wholeSpace_admissible d
  have hγ := zeroCurve_piecewiseC1 d
  have hU : tsupport F ⊆ {p : TimeVelocity d | p.1 < 1 ∧
      p.2 ∈ movingDomain (wholeSpace d) (fun _ => (0 : PDE.Vec d)) p.1} := by
    intro p hp
    have := hFsupp hp
    exact ⟨this.1.2, by rw [movingDomain_wholeSpace]; exact mem_univ _⟩
  obtain ⟨hsm, -, heq, -, -, -⟩ := parabolic_duhamel hH hΩ hγ hB K hP 1 F hF0 hFs hFc hU
  have hΩm := measurableSet_of_isAdmissibleEvolutionDomain hΩ
  have hg : ∀ r, Measurable (fun v : PDE.Vec d => F (r, v)) := fun r =>
    hFs.continuous.measurable.comp (measurable_const.prodMk measurable_id)
  obtain ⟨C, hC⟩ := hFs.continuous.bounded_above_of_compact_support hFc
  have hbdd : BddAbove (range F) := ⟨C, by
    rintro _ ⟨p, rfl⟩
    exact (le_abs_self _).trans (by simpa using hC p)⟩
  have hgb : ∀ p, F p ≤ ⨆ q, F q := fun p => le_ciSup hbdd p
  have hsup0 : 0 ≤ ⨆ q, F q := (hF0 (0, 0)).trans (hgb _)
  have hle : ∀ p : TimeVelocity d, p.1 ∈ Icc (0 : ℝ) 1 →
      parabolicDuhamelPotential K hΩm 1 F p ≤ ⨆ q, F q := by
    intro p hp
    refine (parabolicDuhamelPotential_le K hΩm 1 F hg hF0 _ hgb p hp.2).trans ?_
    exact mul_le_of_le_one_left hsup0 (by linarith [hp.1])
  refine ⟨fun p => parabolicDuhamelPotential_nonneg K hΩm 1 F hg hF0 p, ?_, ?_,
    fun v => parabolicDuhamelPotential_eq_zero_of_terminal_le K hΩm 1 F (1, v) le_rfl, ?_, ?_⟩
  · exact ⟨⨆ q, F q, by
      rintro _ ⟨p, hp, rfl⟩
      exact hle p hp.1⟩
  · refine csSup_le ⟨_, ⟨(0, 0), ⟨⟨le_rfl, zero_le_one⟩, mem_univ _⟩, rfl⟩⟩ ?_
    rintro _ ⟨p, hp, rfl⟩
    exact hle p hp.1
  · exact hsm.mono fun p hp => ⟨hp, by rw [movingDomain_wholeSpace]; exact mem_univ _⟩
  · intro p hp
    exact heq p ⟨hp, by rw [movingDomain_wholeSpace]; exact mem_univ _⟩

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
