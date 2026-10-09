module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundaryFunctionalValues
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceLinearity

/-! # Linearity of the literal boundary reconstruction -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo Evolution TheoremA Parabolic

/-- Scalar factors commute with the literal Duhamel potential. -/
theorem boundary_duhamelPotential_const_mul {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ) (c : ℝ)
    (g : KineticPoint d → ℝ) (T : ℝ) (P : KineticPoint d) :
    duhamelPotential K T (fun Q => c * g Q) P = c * duhamelPotential K T g P := by
  unfold duhamelPotential
  have heq : duhamelIntegrand K (fun Q => c * g Q) P =
      fun r => c * duhamelIntegrand K g P r := by
    funext r
    unfold duhamelIntegrand
    split
    · exact integral_const_mul c _
    · exact (mul_zero c).symm
  rw [heq, integral_const_mul]

variable (hH : HormanderHypoellipticityStatement)
  (hLE : LiebermanEllipsoidDirichletStatement)
  {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ}
  (hlam : 0 < lam) (hLam : lam ≤ Lam)
  (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
  (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)

/-- Bounded measurable sources add under the canonical finite-strip integral. -/
theorem boundary_ballSourcePotential_add (a T : ℝ) (F G : KineticPoint d → ℝ)
    (hF : Measurable F) (hG : Measurable G)
    (M N : ℝ) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hFb : ∀ P ∈ localStrip a T v₀ R, |F P| ≤ M)
    (hGb : ∀ P ∈ localStrip a T v₀ R, |G P| ≤ N) (P : KineticPoint d) :
    ballSourcePotential hH hLE hd hlam hLam B hB v₀ hR a T (fun Q => F Q + G Q) P =
      ballSourcePotential hH hLE hd hlam hLam B hB v₀ hR a T F P +
      ballSourcePotential hH hLE hd hlam hLam B hB v₀ hR a T G P := by
  have heq : (localStrip a T v₀ R).indicator (fun Q => F Q + G Q) ∘ sectionTwoPoint =
      fun Q => (localStrip a T v₀ R).indicator F (sectionTwoPoint Q) +
        (localStrip a T v₀ R).indicator G (sectionTwoPoint Q) := by
    funext Q
    by_cases hQ : sectionTwoPoint Q ∈ localStrip a T v₀ R
    · simp only [Function.comp_apply, indicator_of_mem hQ]
    · simp only [Function.comp_apply, indicator_of_notMem hQ, add_zero]
  unfold ballSourcePotential
  rw [heq]
  obtain ⟨hFm, hFbound⟩ := boundedBallSource_extension a T M v₀ R hM F hF hFb
  obtain ⟨hGm, hGbound⟩ := boundedBallSource_extension a T N v₀ R hN G hG hGb
  exact duhamelPotential_add_bounded _ (PDE.isOpen_euclideanBall v₀ R).measurableSet
    continuous_const _ _ hFm hGm M N hM hN hFbound hGbound T (sectionTwoPoint P)

/-- Scalar factors pass through the canonical finite-strip source potential. -/
theorem boundary_ballSourcePotential_const_mul (a T c : ℝ)
    (F : KineticPoint d → ℝ) (P : KineticPoint d) :
    ballSourcePotential hH hLE hd hlam hLam B hB v₀ hR a T (fun Q => c * F Q) P =
      c * ballSourcePotential hH hLE hd hlam hLam B hB v₀ hR a T F P := by
  have heq : (localStrip a T v₀ R).indicator (fun Q => c * F Q) ∘ sectionTwoPoint =
      fun Q => c * (localStrip a T v₀ R).indicator F (sectionTwoPoint Q) := by
    funext Q
    by_cases hQ : sectionTwoPoint Q ∈ localStrip a T v₀ R
    · simp only [Function.comp_apply, indicator_of_mem hQ]
    · simp only [Function.comp_apply, indicator_of_notMem hQ, mul_zero]
  unfold ballSourcePotential
  rw [heq, boundary_duhamelPotential_const_mul]
  rfl

/-- The actual homogeneous boundary reconstruction adds for smooth compact probes. -/
theorem ballBoundarySolution_add (a T : ℝ) (φ ψ : KineticPoint d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ (KineticPoint.equivProd d).symm))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (ψ ∘ (KineticPoint.equivProd d).symm))
    (hcφ : HasCompactSupport φ) (hcψ : HasCompactSupport ψ) (P : KineticPoint d) :
    ballBoundarySolution hH hLE hd hlam hLam B hB v₀ hR a T (fun Q => φ Q + ψ Q) P =
      ballBoundarySolution hH hLE hd hlam hLam B hB v₀ hR a T φ P +
      ballBoundarySolution hH hLE hd hlam hLam B hB v₀ hR a T ψ P := by
  have hφr := isKineticC112On_of_contDiffOn isOpen_univ
    (hφ.comp (evolutionProdCLE d).contDiff).contDiffOn
  have hψr := isKineticC112On_of_contDiffOn isOpen_univ
    (hψ.comp (evolutionProdCLE d).contDiff).contDiffOn
  have heq : forwardKineticOperator (ofTimeVelocityCoefficient B) (fun Q => φ Q + ψ Q) =
      fun Q => forwardKineticOperator (ofTimeVelocityCoefficient B) φ Q +
        forwardKineticOperator (ofTimeVelocityCoefficient B) ψ Q :=
    funext (fun Q => comparison_forwardOperator_add hφr hψr _ (mem_univ Q))
  obtain ⟨hFc, M, hM, hFb⟩ := boundary_probe_operator_bounded B hB φ hφ hcφ
  obtain ⟨hGc, N, hN, hGb⟩ := boundary_probe_operator_bounded B hB ψ hψ hcψ
  unfold ballBoundarySolution
  rw [heq, boundary_ballSourcePotential_add hH hLE hd hlam hLam B hB v₀ hR
    a T _ _ hFc.measurable hGc.measurable M N hM hN
    (fun Q _ => hFb Q) (fun Q _ => hGb Q)]
  ring

/-- The boundary reconstruction is homogeneous under scalar multiplication of probes. -/
theorem ballBoundarySolution_const_mul (a T c : ℝ) (φ : KineticPoint d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ (KineticPoint.equivProd d).symm)) (P : KineticPoint d) :
    ballBoundarySolution hH hLE hd hlam hLam B hB v₀ hR a T (fun Q => c * φ Q) P =
      c * ballBoundarySolution hH hLE hd hlam hLam B hB v₀ hR a T φ P := by
  have hφr := isKineticC112On_of_contDiffOn isOpen_univ
    (hφ.comp (evolutionProdCLE d).contDiff).contDiffOn
  have heq : forwardKineticOperator (ofTimeVelocityCoefficient B) (fun Q => c * φ Q) =
      fun Q => c * forwardKineticOperator (ofTimeVelocityCoefficient B) φ Q :=
    funext (fun Q => comparison_forwardOperator_const_mul hφr c _ (mem_univ Q))
  unfold ballBoundarySolution
  rw [heq, boundary_ballSourcePotential_const_mul]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
