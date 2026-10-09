module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelWeak
public import HypoellipticAleksandrov.KineticAleksandrov.ClassicalInputs
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelSmooth

/-! # Hörmander regularity for the full kinetic Duhamel source potential -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set Filter
open Evolution Occupation
open scoped Topology
variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- The full kinetic Duhamel potential solves the source equation in the existing weak carrier. -/
theorem duhamel_isKineticWeakTransportedSolution (hΩa : IsAdmissibleEvolutionDomain Ω)
    (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (g : KineticPoint d → ℝ) (hgn : ∀ p, 0 ≤ g p)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgs : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × EvolutionAmbientState d =>
      g ⟨q.1, q.2.1, q.2.2⟩)) (T : ℝ)
    (hgU : tsupport g ⊆ evolutionPastOpenCylinder Ω γ T) :
    IsKineticWeakTransportedSolution B b (evolutionPastOpenCylinder Ω γ T)
      (duhamelPotential K T g) (fun p => -g p) := by
  have hU₀ := isOpen_duhamelCylinder (isOpen_of_isAdmissibleEvolutionDomain hΩa) hγ T
  have hU := hU₀.preimage (evolutionHomeomorph d).continuous
  have hWc : ContinuousOn (duhamelPotential K T g) (evolutionPastOpenCylinder Ω γ T) :=
    (continuousOn_duhamelPotential hΩa hΩ hγ B b S K hreal g hgn hg hgc hgs T hgU
      ).mono (fun p hp => ⟨hp.1.le, subset_closure hp.2⟩)
  have hWQ := hWc.comp (evolutionHomeomorph d).continuous.continuousOn (fun x hx => hx)
  apply (isWeakTransportedSolution_comp_iff B b _ _ _).1
  refine ⟨hWQ.locallyIntegrableOn hU.measurableSet, fun ψ hψ hc hs => ?_⟩
  have hfull := duhamel_weak_identity hΩa hΩ hγ B b S K hreal hB hBs hb
    g hgn hg hgc hgs T hgU hψ hc hs
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  · simp only [Function.comp_apply, neg_mul, integral_neg]
    exact hfull
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero]
  · intro x hx
    rw [transportedAdjoint_eq_zero_of_notMem_tsupport ψ (fun h => hx (hs h)), mul_zero]

/-- Hörmander gives pointwise interior smoothness of the continuous kinetic source potential. -/
theorem duhamelPotential_contDiffOn (hH : HormanderHypoellipticityStatement)
    (hΩa : IsAdmissibleEvolutionDomain Ω)
    (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (g : KineticPoint d → ℝ) (hgn : ∀ p, 0 ≤ g p)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgs : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × EvolutionAmbientState d =>
      g ⟨q.1, q.2.1, q.2.2⟩)) (T : ℝ)
    (hgU : tsupport g ⊆ evolutionPastOpenCylinder Ω γ T)
    {lam Lam m : ℝ} (hlam : 0 < lam) (hm : 0 < m)
    (hell : HasEverywhereLoewnerBounds lam Lam B)
    (hcoerc : HasUnitDirectionDriftCoercivity m b) :
    ContDiffOn ℝ (⊤ : ℕ∞) (duhamelPotential K T g ∘ evolutionHomeomorph d)
      (evolutionHomeomorph d ⁻¹' evolutionPastOpenCylinder Ω γ T) := by
  have hU₀ := isOpen_duhamelCylinder (isOpen_of_isAdmissibleEvolutionDomain hΩa) hγ T
  have hU := hU₀.preimage (evolutionHomeomorph d).continuous
  have hWc : ContinuousOn (duhamelPotential K T g) (evolutionPastOpenCylinder Ω γ T) :=
    (continuousOn_duhamelPotential hΩa hΩ hγ B b S K hreal g hgn hg hgc hgs T hgU
      ).mono (fun p hp => ⟨hp.1.le, subset_closure hp.2⟩)
  have hWQ := hWc.comp (evolutionHomeomorph d).continuous.continuousOn (fun x hx => hx)
  have hweak := (isWeakTransportedSolution_comp_iff B b _ _ _).2
    (duhamel_isKineticWeakTransportedSolution hΩa hΩ hγ B b S K hreal hB hBs hb
      g hgn hg hgc hgs T hgU)
  have hg' : ContDiffOn ℝ (⊤ : ℕ∞) ((fun p => -g p) ∘ evolutionHomeomorph d)
      (evolutionHomeomorph d ⁻¹' evolutionPastOpenCylinder Ω γ T) :=
    ((hgs.comp (evolutionProdCLE d).contDiff).neg).contDiffOn
  obtain ⟨f, hf, hae⟩ := exists_smooth_representative_transported_source hH hlam hB hell hb
    hm hcoerc hU hweak hg'
  have heq := Measure.eqOn_open_of_ae_eq hae hU hWQ hf.continuousOn
  exact hf.congr (fun x hx => heq hx)

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
