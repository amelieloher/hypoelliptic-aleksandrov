module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockGreenTestVanishing
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripSource

/-! # The native normalized smoothness in literal scalar clock coordinates -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution

/-- Smooth native normalized potentials are smooth in literal physical scalar coordinates. -/
theorem clock_native_smooth_to_scalar (u : Point → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ evolutionHomeomorph 1)
      {x : EvolutionVec 1 | (evolutionHomeomorph 1 x).position ∈
        intervalDomain clockNormalizedInterval}) :
    ContDiffOn ℝ (⊤ : ℕ∞) ((u ∘ sectionTwoPoint) ∘ scalarPoint)
      {q : Fin 3 → ℝ | q 2 ∈ normalizedActive} := by
  let c : (Fin 3 → ℝ) → EvolutionVec 1 := fun q =>
    (evolutionProdCLE 1).symm (q 0, (fun _ => q 2), (fun _ => q 1))
  have hc : ContDiff ℝ (⊤ : ℕ∞) c := (evolutionProdCLE 1).symm.contDiff.comp
    ((contDiff_apply ℝ ℝ (0 : Fin 3)).prodMk
      ((contDiff_pi.mpr (fun _ => contDiff_apply ℝ ℝ (2 : Fin 3))).prodMk
        (contDiff_pi.mpr (fun _ => contDiff_apply ℝ ℝ (1 : Fin 3)))))
  have he (q : Fin 3 → ℝ) : evolutionHomeomorph 1 (c q) = sectionTwoPoint (scalarPoint q) := by
    apply (KineticPoint.equivProd 1).injective
    change evolutionProdCLE 1 ((evolutionProdCLE 1).symm _) = _
    exact ContinuousLinearEquiv.apply_symm_apply _ _
  have hm : MapsTo c {q : Fin 3 → ℝ | q 2 ∈ normalizedActive}
      {x : EvolutionVec 1 | (evolutionHomeomorph 1 x).position ∈
        intervalDomain clockNormalizedInterval} := by
    intro q hq
    change (evolutionHomeomorph 1 (c q)).position ∈ intervalDomain clockNormalizedInterval
    rw [he q, intervalDomain, PDE.mem_oneDimensionalAxisBox_iff]
    exact hq
  have h := hu.comp hc.contDiffOn hm
  have heq : (u ∘ evolutionHomeomorph 1) ∘ c = (u ∘ sectionTwoPoint) ∘ scalarPoint := by
    funext q
    exact congrArg u (he q)
  rwa [heq] at h

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
