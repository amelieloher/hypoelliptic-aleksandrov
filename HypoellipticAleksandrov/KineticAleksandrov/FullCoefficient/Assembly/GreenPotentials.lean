module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Assembly.Reflection
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsLocality
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelEquation
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonGeometry

/-!
# Green source potentials for a full coefficient

The Green source integral over the reflected cylinder has the regularity, sign and equation
required by the abstract ABP estimate, for a kinetic full coefficient `A` whose argument swap
`B(σ,v,z) = A(σ,z,v)` has a realizing terminal evolution.  This generalizes the `z`-independent
`green_potentials`; the body is the same, using `kinetic_duhamel`'s full-coefficient potentials.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Assembly
open Set MeasureTheory SectionTwo Evolution Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.TheoremA
open scoped Topology
variable {d : ℕ}

/-- The Green source integral has the regularity, sign and equation required by abstract ABP,
for a full coefficient. -/
theorem green_potentials_full (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam)
    (A : FullKineticCoefficient d) (hB : IsSmoothFullKineticCoefficient (swapCoefficient A))
    (hBs : IsSymmetricFullKineticCoefficient (swapCoefficient A))
    (hell : HasEverywhereLoewnerBounds lam Lam (swapCoefficient A))
    (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
      MeasurableSet.univ (swapCoefficient A) (identityDrift d) S K)
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (g : KineticPoint d → ℝ)
    (hgs : ContDiff ℝ (⊤ : ℕ∞) (fun z => g ((KineticPoint.equivProd d).symm z)))
    (hgc : HasCompactSupport g) (hgQ : tsupport g ⊆ forwardCylinder Z₀ R hR)
    (hg0 : ∀ P, 0 ≤ g P) :
    IsKineticC112On (fun P => ∫ z, g z ∂cylinderGreenMeasure K Z₀ R hR P)
        (forwardCylinder Z₀ R hR) ∧
      (∀ P ∈ forwardCylinder Z₀ R hR,
        0 ≤ ∫ z, g z ∂cylinderGreenMeasure K Z₀ R hR P) ∧
      (∀ P ∈ forwardCylinder Z₀ R hR,
        forwardKineticOperator A
          (fun P => ∫ z, g z ∂cylinderGreenMeasure K Z₀ R hR P) P = -g P) := by
  let T := Z₀.time + R ^ 2
  let g₂ := g ∘ sectionTwoPoint
  let W := duhamelPotential K T g₂
  let V := W ∘ sectionTwoPoint
  let F := fun P => ∫ z, g z ∂cylinderGreenMeasure K Z₀ R hR P
  have hg : Continuous g := by
    have heq : (fun P => g ((KineticPoint.equivProd d).symm
        ((KineticPoint.homeomorphProd d) P))) = g := by
      funext P
      rfl
    rw [← heq]
    exact hgs.continuous.comp (KineticPoint.homeomorphProd d).continuous
  have hg₂ : Continuous g₂ := hg.comp (continuous_sectionTwoPoint d)
  have hgc₂ : HasCompactSupport g₂ := hasCompactSupport_sectionTwoPoint hgc
  have hgs₂ := contDiff_sectionTwoPoint_source hgs
  have hg₂0 : ∀ P, 0 ≤ g₂ P := fun P => hg0 _
  have hgU : tsupport g₂ ⊆ evolutionPastOpenCylinder (wholeSpace d) (fun _ => 0) T := by
    intro P hP
    have hp := hgQ ((tsupport_comp_subset_preimage g (continuous_sectionTwoPoint d)) hP)
    have ht := ((mem_forwardCylinder_iff _ _ _ hR).1 hp).2.1
    exact ⟨ht, by simp [movingDomain_wholeSpace]⟩
  have hW := duhamelPotential_contDiffOn hH (wholeSpace_admissible d)
    MeasurableSet.univ continuous_const (swapCoefficient A) (identityDrift d)
    S K hreal hB hBs (identityDrift_smooth d) g₂ hg₂0 hg₂ hgc₂ hgs₂ T hgU
    hlam (by norm_num : (0 : ℝ) < 1) hell (identityDrift_bounds d).2
  have hEQ := duhamelPotential_source_equation hH (wholeSpace_admissible d)
    MeasurableSet.univ continuous_const (swapCoefficient A) (identityDrift d)
    S K hreal hB hBs (identityDrift_smooth d) g₂ hg₂0 hg₂ hgc₂ hgs₂ T hgU
    hlam (by norm_num : (0 : ℝ) < 1) hell (identityDrift_bounds d).2
  have heq : ∀ P, P.time < T → F P = V P :=
    fun P hP => integral_cylinderGreenMeasure K Z₀ R hR g hg0 hg hgc hgQ P hP
  have hQ := isOpen_forwardCylinder Z₀ R hR
  have hQt : ∀ P ∈ forwardCylinder Z₀ R hR, P.time < T :=
    fun P hP => ((mem_forwardCylinder_iff _ _ _ hR).1 hP).2.1
  let swap : EvolutionVec d → EvolutionVec d := fun x =>
    packPoint (timeCoord d x) (transportedCoord d x) (diffusedCoord d x)
  have hswap : ContDiff ℝ (⊤ : ℕ∞) swap := by
    exact (evolutionProdCLE d).symm.contDiff.comp
      ((Evolution.timeCoord d).contDiff.prodMk
        ((transportedCoord d).contDiff.prodMk (diffusedCoord d).contDiff))
  have hmap : MapsTo swap (evolutionHomeomorph d ⁻¹' forwardCylinder Z₀ R hR)
      (evolutionHomeomorph d ⁻¹' evolutionPastOpenCylinder (wholeSpace d) (fun _ => 0) T) := by
    intro x hx
    refine ⟨?_, by simp [movingDomain_wholeSpace]⟩
    simpa [swap] using hQt _ hx
  have hV : ContDiffOn ℝ (⊤ : ℕ∞) (V ∘ evolutionHomeomorph d)
      (evolutionHomeomorph d ⁻¹' forwardCylinder Z₀ R hR) := by
    have hv := hW.comp hswap.contDiffOn hmap
    convert hv using 1
    funext x
    simp only [V, W, swap, Function.comp_apply, evolutionHomeomorph_apply,
      timeCoord_packPoint, diffusedCoord_packPoint, transportedCoord_packPoint]
    rfl
  have hF := hV.congr (fun x hx => heq _ (hQt _ hx))
  refine ⟨isKineticC112On_of_contDiffOn hQ hF, ?_, ?_⟩
  · intro P hP
    exact integral_nonneg hg0
  · intro P hP
    have hn : F =ᶠ[𝓝 P] V := by
      filter_upwards [((isOpen_lt continuous_time continuous_const).mem_nhds (hQt P hP))]
        with z hz
      exact heq z hz
    rw [forwardKineticOperator_eq_of_eventuallyEq _ hn,
      forwardKineticOperator_eq_transported]
    have hw : V ∘ sectionTwoPoint = W := by
      funext q
      rfl
    rw [hw]
    exact hEQ _ ⟨hQt P hP, by simp [movingDomain_wholeSpace]⟩

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Assembly
