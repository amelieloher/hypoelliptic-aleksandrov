module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelEquation
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelGreen
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelBarrier

/-! # The kinetic Duhamel lemma for a supplied terminal evolution -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set
open Evolution
open scoped ENNReal
variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- Absolute-time source integration against the canonical, uniquely characterized Green measure. -/
theorem duhamelPotential_eq_greenMeasure (K : MovingFiberKernel Ω γ)
    (hΩ : MeasurableSet Ω) (hγ : Continuous γ) (T : ℝ) (g : KineticPoint d → ℝ)
    (hgn : ∀ p, 0 ≤ g p) (hg : Continuous g) (hc : HasCompactSupport g)
    (s : ℝ) (hs : s < T) (p : EvolutionState Ω γ s) :
    duhamelPotential K T g ⟨s, p.1.1, p.1.2⟩ =
      ∫ q, g ⟨s + q.1.1, q.2.1, q.2.2⟩ ∂greenMeasure K s (ENNReal.ofReal (T - s))
        (ENNReal.ofReal_pos.mpr (sub_pos.mpr hs)) (Measure.dirac p) :=
  duhamelPotential_eq_green K hΩ hγ T g hgn hg hc s hs p _
    (greenMeasure_spec K s _ _ (Measure.dirac p))

/-- The full kinetic Duhamel lemma (Lemma 2.3), relative to the named Hörmander hypothesis
and the supplied terminal evolution, with source normalization and zero traces. -/
theorem kinetic_duhamel (hH : HormanderHypoellipticityStatement) (_hd : 1 ≤ d)
    (hΩ : IsAdmissibleEvolutionDomain Ω) (hγ : IsContinuousPiecewiseC1 γ)
    {lam Lam m Lb : ℝ} (hlam : 0 < lam) (_hLam : lam ≤ Lam) (hm : 0 < m)
    (B : FullKineticCoefficient d) (hB : IsSmoothFullKineticCoefficient B)
    (hBs : IsSymmetricFullKineticCoefficient B)
    (hell : HasEverywhereLoewnerBounds lam Lam B)
    (b : PDE.Vec d → PDE.Vec d) (hb : IsSmoothDrift b)
    (hbounds : HasTransportBounds m Lb b)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ
      (measurableSet_of_isAdmissibleEvolutionDomain hΩ) B b S K)
    (T : ℝ) (g : KineticPoint d → ℝ) (hgn : ∀ p, 0 ≤ g p)
    (hgs : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × EvolutionAmbientState d =>
      g ⟨q.1, q.2.1, q.2.2⟩)) (hgc : HasCompactSupport g)
    (hgU : tsupport g ⊆ evolutionPastOpenCylinder Ω γ T) :
    (Measurable (duhamelPotential K T g) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ p, |duhamelPotential K T g p| ≤ C) ∧
    IsKineticWeakTransportedSolution B b (evolutionPastOpenCylinder Ω γ T)
      (duhamelPotential K T g) (fun p => -g p) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (duhamelPotential K T g ∘ evolutionHomeomorph d)
      (evolutionHomeomorph d ⁻¹' evolutionPastOpenCylinder Ω γ T) ∧
    (∀ p ∈ evolutionPastOpenCylinder Ω γ T,
      0 ≤ duhamelPotential K T g p ∧
      duhamelPotential K T g p ≤ (T - p.time) * ⨆ q, g q) ∧
    (∀ p ∈ evolutionPastOpenCylinder Ω γ T,
      transportedForwardOperator B b (duhamelPotential K T g) p = -g p) ∧
    ContinuousOn (duhamelPotential K T g) (evolutionPastClosedCylinder Ω γ T) ∧
    (∀ p : KineticPoint d, p.time = T → duhamelPotential K T g p = 0) ∧
    (∀ p : KineticPoint d, p.position ∈ frontier (movingDomain Ω γ p.time) →
      duhamelPotential K T g p = 0) ∧
    (∀ s : ℝ, ∀ hs : s < T, ∀ p : EvolutionState Ω γ s,
      duhamelPotential K T g ⟨s, p.1.1, p.1.2⟩ =
        ∫ q, g ⟨s + q.1.1, q.2.1, q.2.2⟩ ∂greenMeasure K s (ENNReal.ofReal (T - s))
          (ENNReal.ofReal_pos.mpr (sub_pos.mpr hs)) (Measure.dirac p)) := by
  have hΩm := measurableSet_of_isAdmissibleEvolutionDomain hΩ
  have hg : Continuous g := by
    convert hgs.continuous.comp (KineticPoint.homeomorphProd d).continuous using 1
    funext p
    rfl
  have hbdd : BddAbove (range g) := by
    obtain ⟨C, hC⟩ := hg.bddAbove_range_of_hasCompactSupport hgc
    exact ⟨C, hC⟩
  have hgb : ∀ p, g p ≤ ⨆ q, g q := fun p => le_ciSup hbdd p
  have hC0 : 0 ≤ ⨆ q, g q := (hgn ⟨0, 0, 0⟩).trans (hgb _)
  refine ⟨duhamelPotential_boundedBorel K hΩm hγ.1 T g hg hgc hgn,
    duhamel_isKineticWeakTransportedSolution hΩ hΩm hγ.1 B b S K hreal hB hBs hb
      g hgn hg hgc hgs T hgU,
    duhamelPotential_contDiffOn hH hΩ hΩm hγ.1 B b S K hreal hB hBs hb
      g hgn hg hgc hgs T hgU hlam hm hell hbounds.2,
    fun p hp => duhamelPotential_nonneg_le K T g hgn _ hC0 hgb p hp.1.le,
    duhamelPotential_source_equation hH hΩ hΩm hγ.1 B b S K hreal hB hBs hb
      g hgn hg hgc hgs T hgU hlam hm hell hbounds.2,
    continuousOn_duhamelPotential hΩ hΩm hγ.1 B b S K hreal g hgn hg hgc hgs T hgU,
    fun p hp => duhamelPotential_eq_zero_of_terminal_le K T g p hp.ge,
    fun p hp => duhamelPotential_eq_zero_of_not_mem K T g p ?_,
    fun s hs p => duhamelPotential_eq_greenMeasure K hΩm hγ.1 T g hgn hg hgc s hs p⟩
  rw [(isOpen_movingDomain_of_isAdmissibleEvolutionDomain γ hΩ p.time).frontier_eq] at hp
  exact hp.2

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
