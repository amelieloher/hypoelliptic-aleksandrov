module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundaryFunctional
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundaryMeasureUnique
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitMeasureRiesz

/-! # Existence and uniqueness of the actual finite ball exit measure

Riesz represents the proved positive contraction on the full trace. Its ambient image has
exactly the stipulated smooth-test action. All finite ambient measures with that action
coincide; support is preserved rather than inserted as an unproved package field.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo Evolution Autonomous
open scoped CompactlySupported ENNReal

/-- The actual closed physical trace is locally compact. -/
instance localTrace_locallyCompactSpace {d : ℕ} (a T : ℝ) (v₀ : PDE.Vec d) (R : ℝ) :
    LocallyCompactSpace (localTrace a T v₀ R) := by
  let : LocallyCompactSpace (KineticPoint d) :=
    (KineticPoint.homeomorphProd d).isClosedEmbedding.locallyCompactSpace
  exact (isClosed_localTrace a T v₀ R).locallyCompactSpace

/-- The trace carrier has a countable topological basis. -/
instance localTrace_secondCountableTopology {d : ℕ} (a T : ℝ) (v₀ : PDE.Vec d) (R : ℝ) :
    SecondCountableTopology (localTrace a T v₀ R) := by
  let : SecondCountableTopology (KineticPoint d) :=
    (KineticPoint.homeomorphProd d).secondCountableTopology
  infer_instance

variable (hH : HormanderHypoellipticityStatement)
  (hLE : LiebermanEllipsoidDirichletStatement)
  {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ}
  (hlam : 0 < lam) (hLam : lam ≤ Lam)
  (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
  (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)

/-- The exact planned unique finite ambient measure characterized by smooth boundary values. -/
theorem existsUnique_ballExitMeasure
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t}) :
    ∃! μ : Measure (KineticPoint d),
      IsFiniteMeasure μ ∧
      μ ((localTrace P.1.time T.1 v₀ R)ᶜ) = 0 ∧
      ∀ φ : KineticPoint d → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) (φ ∘ (KineticPoint.equivProd d).symm) →
        HasCompactSupport φ →
        (∫ Q, φ Q ∂μ) =
          ballBoundarySolution hH hLE hd hlam hLam B hB v₀ hR P.1.time T.1 φ P.1 := by
  obtain ⟨ℓ, hℓ, -⟩ := existsUnique_ballBoundaryFunctional hH hLE hd hlam hLam B hB v₀ hR P T
  obtain ⟨ν, hν, -⟩ := existsUnique_boundaryFunctional_measure ℓ hℓ.1
  let : IsFiniteMeasure ν := ⟨hν.1.trans_lt (by simp)⟩
  let μ := ν.map (Subtype.val : localTrace P.1.time T.1 v₀ R → KineticPoint d)
  have hμ : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  have hsupport : μ (localTrace P.1.time T.1 v₀ R)ᶜ = 0 := by
    dsimp only [μ]
    rw [Measure.map_apply measurable_subtype_coe
      (measurableSet_localTrace P.1.time T.1 v₀ R).compl]
    have heq : (Subtype.val : localTrace P.1.time T.1 v₀ R → KineticPoint d) ⁻¹'
        (localTrace P.1.time T.1 v₀ R)ᶜ = ∅ := by
      ext Q
      simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false]
      exact not_not.mpr Q.2
    rw [heq, measure_empty]
  have htests : ∀ φ : KineticPoint d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) (φ ∘ (KineticPoint.equivProd d).symm) →
      HasCompactSupport φ → (∫ Q, φ Q ∂μ) =
        ballBoundarySolution hH hLE hd hlam hLam B hB v₀ hR P.1.time T.1 φ P.1 := by
    intro φ hφ hc
    let f : boundaryProbeSubmodule d := ⟨φ ∘ (KineticPoint.equivProd d).symm,
      hφ, hc.comp_homeomorph (KineticPoint.homeomorphProd d).symm⟩
    have heq : boundaryProbePhysical f = φ := by
      funext Q
      exact congrArg φ ((KineticPoint.equivProd d).symm_apply_apply Q)
    dsimp only [μ]
    rw [integral_map measurable_subtype_coe.aemeasurable
      (boundary_probe_continuous φ hφ).measurable.aestronglyMeasurable]
    have h := (hν.2 (boundaryProbeCcLinear P.1.time T.1 v₀ R f)).trans (hℓ.2 f)
    change (∫ Q, boundaryProbePhysical f Q.1 ∂ν) =
      ballBoundarySolution hH hLE hd hlam hLam B hB v₀ hR P.1.time T.1
        (boundaryProbePhysical f) P.1 at h
    rw [heq] at h
    exact h
  refine ⟨μ, ⟨hμ, hsupport, htests⟩, ?_⟩
  intro μ' hμ'
  let : IsFiniteMeasure μ' := hμ'.1
  exact boundary_measure_ext μ' μ (fun φ hφ hc =>
    (hμ'.2.2 φ hφ hc).trans (htests φ hφ hc).symm)

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
