module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelRegularity
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! # Pointwise source equation for the kinetic Duhamel potential -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set Filter
open Evolution Occupation
open scoped Topology
variable {d : ℕ}

/-- The full kinetic operator preserves smoothness on an open set with smooth coefficients. -/
theorem contDiffOn_duhamel_operator {U : Set (EvolutionVec d)} (hU : IsOpen U)
    {B : FullKineticCoefficient d} (hB : IsSmoothFullKineticCoefficient B)
    {b : PDE.Vec d → PDE.Vec d} (hb : IsSmoothDrift b)
    {u : EvolutionVec d → ℝ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (transportedOperator B b u) U := by
  have hA : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x : EvolutionVec d =>
      B (timeCoord d x) (diffusedCoord d x) (transportedCoord d x) i j) :=
    fun i j => (hB i j).comp (evolutionProdCLE d).contDiff
  have hβ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x : EvolutionVec d => b (diffusedCoord d x) i) :=
    fun i => (contDiff_pi.mp hb i).comp (diffusedCoord d).contDiff
  unfold transportedOperator
  refine ((contDiffOn_duhamel_direction hU hu basisT).add ?_).add ?_
  · exact ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => (hA i j).contDiffOn.mul
      (contDiffOn_duhamel_direction hU (contDiffOn_duhamel_direction hU hu (basisV j))
        (basisV i))
  · exact ContDiffOn.sum fun i _ => (hβ i).contDiffOn.mul
      (contDiffOn_duhamel_direction hU hu (basisZ i))

/-- A smooth kinetic weak solution satisfies its source equation at every interior point. -/
theorem duhamel_operator_eq_of_smooth_weak {U : Set (EvolutionVec d)} (hU : IsOpen U)
    {B : FullKineticCoefficient d} (hB : IsSmoothFullKineticCoefficient B)
    (hBs : IsSymmetricFullKineticCoefficient B)
    {b : PDE.Vec d → PDE.Vec d} (hb : IsSmoothDrift b)
    {u f : EvolutionVec d → ℝ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (hf : ContinuousOn f U) (hweak : IsWeakTransportedSolution B b U u f) :
    ∀ x ∈ U, transportedOperator B b u x = f x := by
  have hop := (contDiffOn_duhamel_operator hU hB hb hu).continuousOn
  have hcont := hop.sub hf
  have hae0 := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hcont.locallyIntegrableOn hU.measurableSet) (fun ψ hψ hc hs => by
      have h1 := integral_transportedAdjoint_contDiffOn hU hB hBs hb hu ψ hψ hc hs
      have h2 := hweak.2 ψ hψ hc hs
      have iA := integrable_evolution_mul_test hop hψ.continuous hc hs
      have iF := integrable_evolution_mul_test hf hψ.continuous hc hs
      have hAe : (∫ x in U, transportedOperator B b u x * ψ x) =
          ∫ x, transportedOperator B b u x * ψ x :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
          rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero]
      have hFe : (∫ x in U, f x * ψ x) = ∫ x, f x * ψ x :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
          rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero]
      have hEq := h1.symm.trans h2
      rw [hAe, hFe] at hEq
      have hfun : (fun x => ψ x • (transportedOperator B b u x - f x)) =
          fun x => transportedOperator B b u x * ψ x - f x * ψ x := by
        funext x
        simp only [smul_eq_mul]
        ring
      simp only [Pi.sub_apply]
      rw [hfun, integral_sub iA iF, hEq, sub_self])
  have hae1 : (fun x => transportedOperator B b u x - f x)
      =ᵐ[volume.restrict U] fun _ => (0 : ℝ) :=
    (ae_restrict_iff' hU.measurableSet).2 hae0
  have heq := Measure.eqOn_open_of_ae_eq hae1 hU hcont continuousOn_const
  intro x hx
  exact sub_eq_zero.mp (heq hx)

variable {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- The full kinetic Duhamel potential satisfies `Lop W = -g` pointwise in the past cylinder. -/
theorem duhamelPotential_source_equation (hH : HormanderHypoellipticityStatement)
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
    ∀ p ∈ evolutionPastOpenCylinder Ω γ T,
      transportedForwardOperator B b (duhamelPotential K T g) p = -g p := by
  have hU := (isOpen_duhamelCylinder (isOpen_of_isAdmissibleEvolutionDomain hΩa) hγ T
    ).preimage (evolutionHomeomorph d).continuous
  have hsm := duhamelPotential_contDiffOn hH hΩa hΩ hγ B b S K hreal hB hBs hb
    g hgn hg hgc hgs T hgU hlam hm hell hcoerc
  have hweak := (isWeakTransportedSolution_comp_iff B b _ _ _).2
    (duhamel_isKineticWeakTransportedSolution hΩa hΩ hγ B b S K hreal hB hBs hb
      g hgn hg hgc hgs T hgU)
  have hf : ContinuousOn ((fun p => -g p) ∘ evolutionHomeomorph d)
      (evolutionHomeomorph d ⁻¹' evolutionPastOpenCylinder Ω γ T) :=
    (hg.neg.comp (evolutionHomeomorph d).continuous).continuousOn
  have heq := duhamel_operator_eq_of_smooth_weak hU hB hBs hb hsm hf hweak
  intro p hp
  have hx : (evolutionHomeomorph d).symm p ∈
      evolutionHomeomorph d ⁻¹' evolutionPastOpenCylinder Ω γ T := by simpa using hp
  have key := heq _ hx
  rw [transportedOperator_comp ((hsm.contDiffAt (hU.mem_nhds hx)).of_le (by simp))] at key
  simpa only [Function.comp_apply, Homeomorph.apply_symm_apply] using key

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
