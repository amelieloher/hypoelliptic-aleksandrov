module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EvolutionInstance
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelEquation
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelSmooth

/-! # Subtraction of weak solutions and homogeneous smooth representatives

Weak solutions with the same forcing have a homogeneous difference. Hörmander's
theorem then gives a smooth almost-everywhere representative. This module
keeps almost-everywhere regularity separate from the pointwise Green formula.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open Evolution Occupation SectionTwo

private theorem integrableOn_weak_mul_test {U : Set (EvolutionVec 1)}
    {u ψ : EvolutionVec 1 → ℝ} (hu : LocallyIntegrableOn u U volume)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
    IntegrableOn (fun x => u x * ψ x) U volume := by
  have hi := hu.integrableOn_compact_subset hs hc.isCompact
  have hm := hi.mul_continuousOn hψ.continuousOn hc.isCompact
  have hglobal : Integrable (fun x => u x * ψ x) volume := by
    apply (integrableOn_iff_integrable_of_support_subset ?_).mp hm
    intro x hx
    exact tsupport_mul_subset_right (subset_closure hx)
  exact hglobal.integrableOn

/-- Weak transported equations restrict to any smaller domain. -/
theorem weak_solution_restrict {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    {U D : Set (EvolutionVec 1)} (hDU : D ⊆ U) {u g : EvolutionVec 1 → ℝ}
    (hu : IsWeakTransportedSolution (evolutionCoefficient A.a) (identityDrift 1) U u g) :
    IsWeakTransportedSolution (evolutionCoefficient A.a) (identityDrift 1) D u g := by
  refine ⟨hu.1.mono_set hDU, ?_⟩
  intro ψ hψ hc hs
  have hl : ∀ x ∉ D,
      u x * transportedAdjoint (evolutionCoefficient A.a) (identityDrift 1) ψ x = 0 := by
    intro x hx
    rw [transportedAdjoint_eq_zero_of_notMem_tsupport ψ (fun h => hx (hs h)), mul_zero]
  have hr : ∀ x ∉ D, g x * ψ x = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero]
  have heq := hu.2 ψ hψ hc (hs.trans hDU)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => hl x (fun h => hx (hDU h))),
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => hr x (fun h => hx (hDU h)))] at heq
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hl,
    setIntegral_eq_integral_of_forall_compl_eq_zero hr]
  exact heq

/-- A smooth interior function satisfies the literal weak equation for its actual operator. -/
theorem smooth_isWeakTransportedSolution {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    {U : Set (EvolutionVec 1)} (hU : IsOpen U) {u : EvolutionVec 1 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) :
    IsWeakTransportedSolution (evolutionCoefficient A.a) (identityDrift 1) U u
      (transportedOperator (evolutionCoefficient A.a) (identityDrift 1) u) := by
  refine ⟨hu.continuousOn.locallyIntegrableOn hU.measurableSet, ?_⟩
  intro ψ hψ hc hs
  exact integral_transportedAdjoint_contDiffOn hU (evolutionCoefficient_smooth A)
    (evolutionCoefficient_symmetric A.a) (identityDrift_smooth 1) hu ψ hψ hc hs

/-- Two weak transported solutions with the same source have homogeneous difference. -/
theorem weak_same_source_sub {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    {U : Set (EvolutionVec 1)} {u v g : EvolutionVec 1 → ℝ}
    (hu : IsWeakTransportedSolution (evolutionCoefficient A.a) (identityDrift 1) U u g)
    (hv : IsWeakTransportedSolution (evolutionCoefficient A.a) (identityDrift 1) U v g) :
    IsWeakTransportedSolution (evolutionCoefficient A.a) (identityDrift 1) U
      (fun x => u x - v x) (fun _ => 0) := by
  refine ⟨hu.1.sub hv.1, ?_⟩
  intro ψ hψ hc hs
  have hLc := (contDiff_transportedAdjoint (evolutionCoefficient_smooth A)
    (identityDrift_smooth 1) hψ).continuous
  have hLk := hasCompactSupport_transportedAdjoint
    (B := evolutionCoefficient A.a) (b := identityDrift 1) hc
  have hLs : tsupport (transportedAdjoint (evolutionCoefficient A.a)
      (identityDrift 1) ψ) ⊆ U := by
    refine (closure_minimal ?_ (isClosed_tsupport ψ)).trans hs
    intro x hx
    by_contra hn
    exact hx (transportedAdjoint_eq_zero_of_notMem_tsupport ψ hn)
  have hiu := integrableOn_weak_mul_test hu.1 hLc hLk hLs
  have hiv := integrableOn_weak_mul_test hv.1 hLc hLk hLs
  simp_rw [sub_mul]
  rw [integral_sub hiu hiv, hu.2 ψ hψ hc hs, hv.2 ψ hψ hc hs, sub_self]
  simp only [zero_mul, integral_zero]

/-- The homogeneous weak difference has a smooth almost-everywhere representative. -/
theorem homogeneous_weak_smooth_representative
    (hH : HormanderHypoellipticityStatement) {lam Lam : ℝ} (hlam : 0 < lam)
    (A : SmoothAutonomous lam Lam) {U : Set (EvolutionVec 1)} (hU : IsOpen U)
    {u : EvolutionVec 1 → ℝ}
    (hu : IsWeakTransportedSolution (evolutionCoefficient A.a) (identityDrift 1) U
      u (fun _ => 0)) :
    ∃ f : EvolutionVec 1 → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) f U ∧
      u =ᵐ[volume.restrict U] f := by
  exact exists_smooth_representative_transported_source hH hlam
    (evolutionCoefficient_smooth A) (evolutionCoefficient_bounds A)
    (identityDrift_smooth 1) zero_lt_one (identityDrift_bounds 1).2 hU hu
    contDiffOn_const

/-- A continuous homogeneous weak solution is pointwise smooth on its open domain. -/
theorem homogeneous_weak_contDiffOn
    (hH : HormanderHypoellipticityStatement) {lam Lam : ℝ} (hlam : 0 < lam)
    (A : SmoothAutonomous lam Lam) {U : Set (EvolutionVec 1)} (hU : IsOpen U)
    {u : EvolutionVec 1 → ℝ}
    (hu : IsWeakTransportedSolution (evolutionCoefficient A.a) (identityDrift 1) U
      u (fun _ => 0)) (hc : ContinuousOn u U) :
    ContDiffOn ℝ (⊤ : ℕ∞) u U := by
  obtain ⟨f, hf, hae⟩ := homogeneous_weak_smooth_representative hH hlam A hU hu
  have heq := Measure.eqOn_open_of_ae_eq hae hU hc hf.continuousOn
  exact hf.congr (fun x hx => heq hx)

/-- The smooth representative of a homogeneous weak solution solves the equation pointwise. -/
theorem homogeneous_weak_smooth_solution
    (hH : HormanderHypoellipticityStatement) {lam Lam : ℝ} (hlam : 0 < lam)
    (A : SmoothAutonomous lam Lam) {U : Set (EvolutionVec 1)} (hU : IsOpen U)
    {u : EvolutionVec 1 → ℝ}
    (hu : IsWeakTransportedSolution (evolutionCoefficient A.a) (identityDrift 1) U
      u (fun _ => 0)) :
    ∃ f : EvolutionVec 1 → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) f U ∧
      u =ᵐ[volume.restrict U] f ∧
      ∀ x ∈ U, transportedOperator (evolutionCoefficient A.a) (identityDrift 1) f x = 0 := by
  obtain ⟨f, hf, hae⟩ := homogeneous_weak_smooth_representative hH hlam A hU hu
  have hw : IsWeakTransportedSolution (evolutionCoefficient A.a) (identityDrift 1) U
      f (fun _ => 0) := by
    refine ⟨hf.continuousOn.locallyIntegrableOn hU.measurableSet, ?_⟩
    intro ψ hψ hc hs
    refine (integral_congr_ae ?_).trans (hu.2 ψ hψ hc hs)
    filter_upwards [hae] with x hx
    rw [hx]
  exact ⟨f, hf, hae, duhamel_operator_eq_of_smooth_weak hU
    (evolutionCoefficient_smooth A) (evolutionCoefficient_symmetric A.a)
    (identityDrift_smooth 1) hf continuousOn_const hw⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
