module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundarySolutionCalculus

/-! # Pointwise smoothness from the actual continuous weak source equation -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo Evolution Occupation Parabolic TheoremA
open scoped Topology

/-- A continuous actual kinetic weak solution with smooth forcing is pointwise smooth. -/
theorem boundary_continuous_weak_smooth
    (hH : HormanderHypoellipticityStatement) {d : ℕ} {lam Lam : ℝ}
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (D : Set (KineticPoint d)) (hD : IsOpen D)
    (u g : KineticPoint d → ℝ) (hc : ContinuousOn u D)
    (hw : IsKineticWeakTransportedSolution (zIndependentCoefficient B) (identityDrift d) D u g)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (g ∘ evolutionHomeomorph d)
      (evolutionHomeomorph d ⁻¹' D)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ evolutionHomeomorph d)
      (evolutionHomeomorph d ⁻¹' D) ∧
      ∀ x ∈ evolutionHomeomorph d ⁻¹' D,
        transportedOperator (zIndependentCoefficient B) (identityDrift d)
          (u ∘ evolutionHomeomorph d) x = g (evolutionHomeomorph d x) := by
  obtain ⟨hsm, hsym, hell⟩ := sectionTwoCoefficient_fullBounds lam Lam B hB
  have hU := hD.preimage (evolutionHomeomorph d).continuous
  have hweak := (isWeakTransportedSolution_comp_iff _ _ _ _ _).2 hw
  have huc := hc.comp (evolutionHomeomorph d).continuous.continuousOn (fun _ hx => hx)
  obtain ⟨f, hf, hae⟩ := exists_smooth_representative_transported_source hH hB.1
    hsm hell (identityDrift_smooth d) zero_lt_one (identityDrift_bounds d).2 hU hweak hg
  have heq := Measure.eqOn_open_of_ae_eq hae hU huc hf.continuousOn
  have hu := hf.congr (fun x hx => heq hx)
  exact ⟨hu, duhamel_operator_eq_of_smooth_weak hU hsm hsym
    (identityDrift_smooth d) hu hg.continuousOn hweak⟩

/-- Native smoothness converts back to the stipulated physical product-coordinate carrier. -/
theorem boundary_native_smooth_to_physical {d : ℕ}
    (D : Set (KineticPoint d)) (u : KineticPoint d → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) ((u ∘ sectionTwoPoint) ∘ evolutionHomeomorph d)
      (evolutionHomeomorph d ⁻¹' (sectionTwoPoint '' D))) :
    ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ (KineticPoint.equivProd d).symm)
      ((KineticPoint.equivProd d) '' D) := by
  let a : ℝ × PDE.Vec d × PDE.Vec d → EvolutionVec d := fun q =>
    (evolutionProdCLE d).symm (q.1, q.2.2, q.2.1)
  have ha : ContDiff ℝ (⊤ : ℕ∞) a := (evolutionProdCLE d).symm.contDiff.comp
    (contDiff_fst.prodMk (contDiff_snd.snd.prodMk contDiff_snd.fst))
  have haeq (q : ℝ × PDE.Vec d × PDE.Vec d) :
      evolutionHomeomorph d (a q) = sectionTwoPoint ((KineticPoint.equivProd d).symm q) := by
    ext <;> simp only [a, evolutionProdCLE_symm_apply, time_evolutionHomeomorph,
      position_evolutionHomeomorph, velocity_evolutionHomeomorph, timeCoord_packPoint,
      diffusedCoord_packPoint, transportedCoord_packPoint] <;> rfl
  have hm : MapsTo a ((KineticPoint.equivProd d) '' D)
      (evolutionHomeomorph d ⁻¹' (sectionTwoPoint '' D)) := by
    rintro q ⟨P, hP, rfl⟩
    refine ⟨P, hP, ?_⟩
    simpa only [Equiv.symm_apply_apply] using (haeq ((KineticPoint.equivProd d) P)).symm
  have h := hu.comp ha.contDiffOn hm
  have heq : ((u ∘ sectionTwoPoint) ∘ evolutionHomeomorph d) ∘ a =
      u ∘ (KineticPoint.equivProd d).symm := by
    funext q
    simp only [Function.comp_apply, haeq]
    rfl
  rw [heq] at h
  exact h

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
