module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelSmooth

/-!
# Lemma 2.3: parabolic Duhamel potentials

Let `P` be the parabolic marginal kernel (`parabolicMarginalKernel`) of a moving-fiber kernel with
the parabolic marginal bundle for a `z`-independent smooth elliptic coefficient `B`, and let
`0 ≤ g ∈ C_c^∞(U₀)` with `U₀ = {(σ, v) : σ < T, v ∈ Ω_σ}`.  The parabolic Duhamel potential
`W(σ, v) = ∫_σ^T ∫ g(r, w) P_{σ,r}(v, dw) dr` is smooth in `U₀`, satisfies
`0 ≤ W ≤ (T - σ) sup g` and `∂_σ W + B : D_v² W = -g` in `U₀`, and extends continuously by zero
to the terminal face `σ = T` and the lateral frontier.  Hörmander's theorem enters only through the
explicit hypothesis `hH`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set Filter
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.Evolution
open scoped Topology

variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- **Parabolic Duhamel lemma** (Lemma 2.3), without the transport data. -/
theorem parabolic_duhamel (hH : HormanderHypoellipticityStatement)
    (hΩ : IsAdmissibleEvolutionDomain Ω) (hγ : IsContinuousPiecewiseC1 γ) {lam Lam : ℝ}
    {B : CoefficientField d} (hB : SectionTwo.IsSectionTwoCoefficient lam Lam B)
    (K : MovingFiberKernel Ω γ)
    (hP : SectionTwo.HasParabolicMarginalBundle Ω γ
      (measurableSet_of_isAdmissibleEvolutionDomain hΩ) (zIndependentCoefficient B) K)
    (T : ℝ) (g : TimeVelocity d → ℝ) (hg0 : ∀ p, 0 ≤ g p) (hgs : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g)
    (hgU : tsupport g ⊆ {p : TimeVelocity d | p.1 < T ∧ p.2 ∈ movingDomain Ω γ p.1}) :
    ContDiffOn ℝ (⊤ : ℕ∞)
        (parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) T g)
        {p : TimeVelocity d | p.1 < T ∧ p.2 ∈ movingDomain Ω γ p.1} ∧
      (∀ p ∈ {p : TimeVelocity d | p.1 < T ∧ p.2 ∈ movingDomain Ω γ p.1},
        0 ≤ parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) T g p ∧
        parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) T g p ≤
          (T - p.1) * ⨆ q, g q) ∧
      (∀ p ∈ {p : TimeVelocity d | p.1 < T ∧ p.2 ∈ movingDomain Ω γ p.1},
        scalarParabolicOperator B (fun _ _ => 0)
          (parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) T g)
          p = -g p) ∧
      ContinuousOn
        (parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) T g)
        {p : TimeVelocity d | p.1 ≤ T ∧ p.2 ∈ closure (movingDomain Ω γ p.1)} ∧
      (∀ p : TimeVelocity d, p.1 = T →
        parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) T g p = 0) ∧
      (∀ p : TimeVelocity d, p.2 ∈ frontier (movingDomain Ω γ p.1) →
        parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) T g p =
          0) := by
  have hΩm := measurableSet_of_isAdmissibleEvolutionDomain hΩ
  have hγc : Continuous γ := hγ.1
  obtain ⟨hsmooth, heq⟩ := duhamel_smooth_equation K hH hΩ hγc hB hP g hg0 hgs hgc T hgU
  have hg : ∀ r, Measurable (fun v : PDE.Vec d => g (r, v)) := fun r =>
    hgs.continuous.measurable.comp (measurable_const.prodMk measurable_id)
  obtain ⟨C, hC⟩ := hgs.continuous.bounded_above_of_compact_support hgc
  have hbdd : BddAbove (range g) := ⟨C, by
    rintro _ ⟨p, rfl⟩
    exact (le_abs_self _).trans (by simpa using hC p)⟩
  have hgb : ∀ p, g p ≤ ⨆ q, g q := fun p => le_ciSup hbdd p
  refine ⟨hsmooth, fun p hp => ⟨parabolicDuhamelPotential_nonneg K hΩm T g hg hg0 p,
    parabolicDuhamelPotential_le K hΩm T g hg hg0 _ hgb p hp.1.le⟩, heq,
    continuousOn_duhamelPotential K hΩ hγc hP g hg0 hgs hgc T hgU,
    fun p hp => parabolicDuhamelPotential_eq_zero_of_terminal_le K hΩm T g p hp.ge,
    fun p hp => parabolicDuhamelPotential_eq_zero_of_not_mem K hΩm T g p ?_⟩
  rw [(isOpen_movingDomain_of_isAdmissibleEvolutionDomain γ hΩ p.1).frontier_eq] at hp
  exact hp.2

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
