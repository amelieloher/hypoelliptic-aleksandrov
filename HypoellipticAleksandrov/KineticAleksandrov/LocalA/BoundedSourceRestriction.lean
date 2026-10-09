module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceWeak

/-! # Restriction of the existing kinetic weak equation

Weak tests supported in a smaller domain extend by zero to the larger domain.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set Evolution Occupation

/-- Restrict a kinetic weak solution to a subdomain without changing its source. -/
theorem boundedSource_weak_restrict {d : ℕ} {U V : Set (KineticPoint d)}
    (hUV : U ⊆ V)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (u f : KineticPoint d → ℝ) (h : IsKineticWeakTransportedSolution B b V u f) :
    IsKineticWeakTransportedSolution B b U u f := by
  refine ⟨h.1.mono_set hUV, fun ψ hψ hc hs => ?_⟩
  have hsV : tsupport ψ ⊆ evolutionHomeomorph d ⁻¹' V := fun x hx => hUV (hs hx)
  have heq := h.2 ψ hψ hc hsV
  have htest : ∀ W : Set (KineticPoint d),
      tsupport ψ ⊆ evolutionHomeomorph d ⁻¹' W →
      (∫ z in W, f z * ψ ((evolutionHomeomorph d).symm z)) =
        ∫ z, f z * ψ ((evolutionHomeomorph d).symm z) := by
    intro W hW
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hn : (evolutionHomeomorph d).symm z ∉ tsupport ψ := by
      intro hx
      exact hz (by simpa using hW hx)
    rw [image_eq_zero_of_notMem_tsupport hn, mul_zero]
  have hadj : ∀ W : Set (KineticPoint d),
      tsupport ψ ⊆ evolutionHomeomorph d ⁻¹' W →
      (∫ z in W, u z * transportedAdjoint B b ψ ((evolutionHomeomorph d).symm z)) =
        ∫ z, u z * transportedAdjoint B b ψ ((evolutionHomeomorph d).symm z) := by
    intro W hW
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hn : (evolutionHomeomorph d).symm z ∉ tsupport ψ := by
      intro hx
      exact hz (by simpa using hW hx)
    rw [transportedAdjoint_eq_zero_of_notMem_tsupport ψ hn, mul_zero]
  rw [hadj V hsV, htest V hsV] at heq
  rw [hadj U hs, htest U hs]
  exact heq

/-- Restrict an ambient homogeneous weak solution while retaining the literal adjoint. -/
theorem boundedSource_ambientWeak_restrict {d : ℕ} {U V : Set (EvolutionVec d)}
    (hUV : U ⊆ V) (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (u : EvolutionVec d → ℝ) (h : IsWeakTransportedSolution B b V u (fun _ => 0)) :
    IsWeakTransportedSolution B b U u (fun _ => 0) := by
  refine ⟨h.1.mono_set hUV, fun ψ hψ hc hs => ?_⟩
  have heq := h.2 ψ hψ hc (hs.trans hUV)
  have hadj : ∀ W : Set (EvolutionVec d), tsupport ψ ⊆ W →
      (∫ z in W, u z * transportedAdjoint B b ψ z) =
        ∫ z, u z * transportedAdjoint B b ψ z := by
    intro W hW
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    rw [transportedAdjoint_eq_zero_of_notMem_tsupport ψ (fun hm => hz (hW hm)), mul_zero]
  simp only [zero_mul, integral_zero] at heq ⊢
  rw [hadj V (hs.trans hUV)] at heq
  rw [hadj U hs]
  exact heq

/-- Changing the source only outside the tested domain preserves the kinetic weak equation. -/
theorem boundedSource_weak_source_congr {d : ℕ} {U : Set (KineticPoint d)}
    (hU : MeasurableSet U) (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (u f g : KineticPoint d → ℝ) (hfg : EqOn f g U)
    (h : IsKineticWeakTransportedSolution B b U u f) :
    IsKineticWeakTransportedSolution B b U u g := by
  refine ⟨h.1, fun ψ hψ hc hs => ?_⟩
  rw [h.2 ψ hψ hc hs]
  apply setIntegral_congr_fun hU
  intro z hz
  change f z * ψ ((evolutionHomeomorph d).symm z) = g z * ψ ((evolutionHomeomorph d).symm z)
  rw [hfg hz]

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
