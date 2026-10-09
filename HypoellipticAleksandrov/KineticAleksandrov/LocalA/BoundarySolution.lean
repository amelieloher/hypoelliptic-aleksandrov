module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundarySolutionRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonLinear

/-! # The literal smooth homogeneous boundary solution

The signed source integral corrects the actual kinetic operator of the smooth probe.
Its proved continuity identifies the Hörmander representative pointwise. The prescribed
terminal and lateral traces are retained by the literal formula.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo Evolution TheoremA Parabolic
open scoped Topology

variable (hH : HormanderHypoellipticityStatement)
  (hLE : LiebermanEllipsoidDirichletStatement)
  {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ}
  (hlam : 0 < lam) (hLam : lam ≤ Lam)
  (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
  (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)

/-- The literal boundary extension obtained by correcting the actual probe source. -/
def ballBoundarySolution (a T : ℝ) (φ : KineticPoint d → ℝ) (P : KineticPoint d) : ℝ :=
  φ P + ballSourcePotential hH hLE hd hlam hLam B hB v₀ hR a T
    (forwardKineticOperator (ofTimeVelocityCoefficient B) φ) P

omit hH hLE hd hlam hLam B hB v₀ hR in
/-- Physical product-coordinate smoothness supplies the unswapped native regularity API. -/
theorem boundary_physical_smooth_to_native {D : Set (KineticPoint d)}
    {u : KineticPoint d → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ (KineticPoint.equivProd d).symm)
      ((KineticPoint.equivProd d) '' D)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ evolutionHomeomorph d)
      (evolutionHomeomorph d ⁻¹' D) := by
  exact hu.comp (evolutionProdCLE d).contDiff.contDiffOn
    (fun x hx => ⟨evolutionHomeomorph d x, hx, rfl⟩)

/-- The source-planned smoothness, homogeneous equation, continuity and exact traces. -/
theorem ballBoundarySolution_smooth_traces
    (a T : ℝ) (haT : a < T) (φ : KineticPoint d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ (KineticPoint.equivProd d).symm))
    (hc : HasCompactSupport φ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      ((ballBoundarySolution hH hLE hd hlam hLam B hB v₀ hR a T φ) ∘
        (KineticPoint.equivProd d).symm)
      ((KineticPoint.equivProd d) '' localStrip a T v₀ R) ∧
    (∀ P ∈ localStrip a T v₀ R,
      forwardKineticOperator (ofTimeVelocityCoefficient B)
        (ballBoundarySolution hH hLE hd hlam hLam B hB v₀ hR a T φ) P = 0) ∧
    ContinuousOn (ballBoundarySolution hH hLE hd hlam hLam B hB v₀ hR a T φ)
      (localClosedStrip a T v₀ R) ∧
    EqOn (ballBoundarySolution hH hLE hd hlam hLam B hB v₀ hR a T φ) φ
      (localTrace a T v₀ R) := by
  let F := forwardKineticOperator (ofTimeVelocityCoefficient B) φ
  let W := ballSourcePotential hH hLE hd hlam hLam B hB v₀ hR a T F
  let D := localStrip a T v₀ R
  let D' := sectionTwoPoint '' D
  have hD : IsOpen D := isOpen_localStrip a T v₀ R
  have hD' : IsOpen D' := (sectionTwoHomeomorph d).isOpenMap _ hD
  obtain ⟨hFc, M, hM, hFb⟩ := boundary_probe_operator_bounded B hB φ hφ hc
  obtain ⟨hWc, hWtr, hWb⟩ := ballSourcePotential_bounded_traces hH hLE hd hlam hLam
    B hB v₀ hR a T M haT hM F hFc.measurable (fun P _ => hFb P)
  have hweak := ballSourcePotential_weak hH hLE hd hlam hLam B hB v₀ hR a T haT
    F hFc.measurable ⟨M, fun P _ => hFb P⟩
  have hWsc : ContinuousOn (W ∘ sectionTwoPoint) D' :=
    (hWc.mono (localStrip_subset_closed a T v₀ R)).comp
      (continuous_sectionTwoPoint d).continuousOn (by
        rintro Q ⟨P, hP, rfl⟩
        exact hP)
  have hsource : ContDiffOn ℝ (⊤ : ℕ∞)
      ((fun Q => -F (sectionTwoPoint Q)) ∘ evolutionHomeomorph d)
      (evolutionHomeomorph d ⁻¹' D') := by
    have hsm := contDiffOn_duhamel_operator
      (hD'.preimage (evolutionHomeomorph d).continuous)
      (sectionTwoCoefficient_fullBounds lam Lam B hB).1 (identityDrift_smooth d)
      (boundary_probe_native_smooth φ hφ).contDiffOn
    have heq : ((fun Q => -F (sectionTwoPoint Q)) ∘ evolutionHomeomorph d) =
        fun x => -transportedOperator (zIndependentCoefficient B) (identityDrift d)
          ((φ ∘ sectionTwoPoint) ∘ evolutionHomeomorph d) x := by
      funext x
      exact congrArg Neg.neg (boundary_probe_operator_native B φ hφ x)
    rw [heq]
    exact hsm.neg
  obtain ⟨hWsm, hWop⟩ := boundary_continuous_weak_smooth hH B hB D' hD'
    (W ∘ sectionTwoPoint) (fun Q => -F (sectionTwoPoint Q)) hWsc hweak hsource
  have hWp := boundary_native_smooth_to_physical D W hWsm
  have hEsm : ContDiffOn ℝ (⊤ : ℕ∞)
      ((ballBoundarySolution hH hLE hd hlam hLam B hB v₀ hR a T φ) ∘
        (KineticPoint.equivProd d).symm) ((KineticPoint.equivProd d) '' D) :=
    hφ.contDiffOn.add hWp
  refine ⟨hEsm, ?_, (boundary_probe_continuous φ hφ).continuousOn.add hWc, ?_⟩
  · have hφr := isKineticC112On_of_contDiffOn hD
      (hφ.comp (evolutionProdCLE d).contDiff).contDiffOn
    have hWr := isKineticC112On_of_contDiffOn hD (boundary_physical_smooth_to_native hWp)
    intro P hP
    change forwardKineticOperator (ofTimeVelocityCoefficient B) (fun Q => φ Q + W Q) P = 0
    rw [comparison_forwardOperator_add hφr hWr _ hP]
    let x := (evolutionHomeomorph d).symm (sectionTwoPoint P)
    have hx : x ∈ evolutionHomeomorph d ⁻¹' D' := by
      change evolutionHomeomorph d x ∈ D'
      rw [Homeomorph.apply_symm_apply]
      exact ⟨P, hP, rfl⟩
    have h := hWop x hx
    have hs : ContDiffAt ℝ 2 ((W ∘ sectionTwoPoint) ∘ evolutionHomeomorph d) x :=
      (hWsm.contDiffAt
      ((hD'.preimage (evolutionHomeomorph d).continuous).mem_nhds hx)).of_le (by simp)
    rw [transportedOperator_comp hs] at h
    dsimp only [x] at h
    rw [Homeomorph.apply_symm_apply] at h
    change transportedForwardOperator (zIndependentCoefficient B) (identityDrift d)
      (W ∘ sectionTwoPoint) (sectionTwoPoint P) = -F P at h
    rw [forwardKineticOperator_eq_lop_identity B W]
    change F P + transportedForwardOperator (zIndependentCoefficient B) (identityDrift d)
      (W ∘ sectionTwoPoint) (sectionTwoPoint P) = 0
    rw [h, add_neg_cancel]
  · intro P hP
    change φ P + W P = φ P
    exact congrArg (fun x => φ P + x) (hWtr P hP) |>.trans (add_zero _)

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
