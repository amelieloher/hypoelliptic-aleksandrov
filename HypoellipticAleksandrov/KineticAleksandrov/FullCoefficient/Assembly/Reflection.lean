module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ReflectionCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.CaseW
public import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem

/-!
# Reflection and coordinate swap of a full coefficient

A full coefficient `A(t,x,v)` on the
kinetic side is reflected to `Ã(s,X,v) = A(-s,-X,v)`; the Section 2 coefficient is
`B(σ,v,z) = Ã(σ,z,v)`, the argument swap of the same matrix field (kinetic side reads
`A t x v`, Section 2 side reads `B σ v z`).  We prove the operator identities
`K_Ã U = ∂_σ + B : D_v² + v·∇_z` in the coordinates `(σ,v,z) = (s,v,X)` and
`K_Ã (u ∘ ℛ) = -(P_A u) ∘ ℛ`, together with the transfer of smoothness, symmetry and
everywhere Loewner bounds.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Assembly

open HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.TheoremA
open scoped MatrixOrder

variable {d : ℕ}

/-- The argument swap `B σ v z = Ã σ z v` from the kinetic reading `(t,x,v)` of a full
coefficient to its Section 2 reading `(σ,v,z)`. -/
def swapCoefficient (A : FullKineticCoefficient d) : FullKineticCoefficient d :=
  fun σ v z => A σ z v

/-- The reflected full coefficient `Ã(s,X,v) = A(-s,-X,v)` (kinetic reading). -/
def reflectedCoefficient (A : FullKineticCoefficient d) : FullKineticCoefficient d :=
  fun s X v => A (-s) (-X) v

/-- The Section 2 coefficient `B(σ,v,z) = A(-σ,-z,v)` of a kinetic full coefficient `A`. -/
def sectionTwoCoefficient (A : FullKineticCoefficient d) : FullKineticCoefficient d :=
  swapCoefficient (reflectedCoefficient A)

/-- Pointwise formula for the Section 2 coefficient `B(σ,v,z) = A(-σ,-z,v)`. -/
theorem sectionTwoCoefficient_apply (A : FullKineticCoefficient d) (σ : ℝ) (v z : PDE.Vec d) :
    sectionTwoCoefficient A σ v z = A (-σ) (-z) v := rfl

/-- `K_Ã U = ∂_σ + B : D_v² + v·∇_z` in the coordinates `(σ,v,z) = (s,v,X)`, for the swapped
coefficient `B` and the identity drift. -/
theorem forwardKineticOperator_eq_transported (A : FullKineticCoefficient d)
    (U : KineticPoint d → ℝ) (P : KineticPoint d) :
    forwardKineticOperator A U P =
      transportedForwardOperator (swapCoefficient A) (identityDrift d) (U ∘ sectionTwoPoint)
        (sectionTwoPoint P) := by
  rw [forwardKineticOperator_apply, transportedForwardOperator_apply]
  have h1 : kineticTimeDerivative (U ∘ sectionTwoPoint) (sectionTwoPoint P) =
      kineticTimeDerivative U P := rfl
  have h2 : diffusedHessian (U ∘ sectionTwoPoint) (sectionTwoPoint P) =
      kineticVelocityHessian U P := rfl
  have h3 : kineticVelocityGradient (U ∘ sectionTwoPoint) (sectionTwoPoint P) =
      kineticPositionGradient U P := rfl
  have h4 : identityDrift d (sectionTwoPoint P).position = P.velocity := rfl
  have h5 : fullKineticCoefficientAt (swapCoefficient A) (sectionTwoPoint P) =
      A P.time P.position P.velocity := rfl
  rw [h1, h2, h3, h4, h5]
  exact add_right_comm _ _ _

/-- `K_Ã (u ∘ ℛ) = -(P_A u) ∘ ℛ` for the full reflected coefficient. -/
theorem reflectedOperator_reflection (A : FullKineticCoefficient d) (u : KineticPoint d → ℝ)
    (P : KineticPoint d) :
    forwardKineticOperator (reflectedCoefficient A) (u ∘ kineticReflection) P =
      -backwardOperator A u (kineticReflection P) := by
  rw [forwardKineticOperator_apply, backwardOperator_apply,
    kineticTimeDerivative_reflection, kineticPositionGradient_reflection,
    kineticVelocityHessian_reflection]
  have hdot : PDE.vecDot P.velocity (-kineticPositionGradient u (kineticReflection P)) =
      -PDE.vecDot P.velocity (kineticPositionGradient u (kineticReflection P)) := by
    simp [PDE.vecDot, Finset.sum_neg_distrib]
  have hA : fullKineticCoefficientAt A (kineticReflection P) =
      reflectedCoefficient A P.time P.position P.velocity := rfl
  rw [hdot, hA]
  simp only [kineticReflection]
  ring

/-- The reflected-and-swapped coefficient `B` realizes the operator identity
`L_B (U ∘ τ) = ...` with the kinetic reflected coefficient. -/
theorem transported_reflection (A : FullKineticCoefficient d) (u : KineticPoint d → ℝ)
    (P : KineticPoint d) :
    transportedForwardOperator (sectionTwoCoefficient A) (identityDrift d)
        ((u ∘ kineticReflection) ∘ sectionTwoPoint) (sectionTwoPoint P) =
      -backwardOperator A u (kineticReflection P) := by
  rw [sectionTwoCoefficient, ← forwardKineticOperator_eq_transported]
  exact reflectedOperator_reflection A u P

/-- Transfer of the hypothesis along the coefficient operation. -/
theorem isSmooth_reflectedCoefficient {A : FullKineticCoefficient d}
    (hA : IsSmoothFullKineticCoefficient A) :
    IsSmoothFullKineticCoefficient (reflectedCoefficient A) := fun i j =>
  (hA i j).comp (contDiff_fst.neg.prodMk
    ((contDiff_fst.comp contDiff_snd).neg.prodMk (contDiff_snd.comp contDiff_snd)))

/-- Transfer of the hypothesis along the coefficient operation. -/
theorem isSmooth_swapCoefficient {A : FullKineticCoefficient d}
    (hA : IsSmoothFullKineticCoefficient A) :
    IsSmoothFullKineticCoefficient (swapCoefficient A) := fun i j =>
  (hA i j).comp (contDiff_fst.prodMk
    ((contDiff_snd.comp contDiff_snd).prodMk (contDiff_fst.comp contDiff_snd)))

/-- Transfer of the hypothesis along the coefficient operation. -/
theorem isSmooth_sectionTwoCoefficient {A : FullKineticCoefficient d}
    (hA : IsSmoothFullKineticCoefficient A) :
    IsSmoothFullKineticCoefficient (sectionTwoCoefficient A) :=
  isSmooth_swapCoefficient (isSmooth_reflectedCoefficient hA)

/-- Transfer of the hypothesis along the coefficient operation. -/
theorem isSymmetric_sectionTwoCoefficient {A : FullKineticCoefficient d}
    (hA : ∀ P : KineticPoint d, (fullKineticCoefficientAt A P).IsSymm) :
    IsSymmetricFullKineticCoefficient (sectionTwoCoefficient A) := fun σ v z =>
  hA ⟨-σ, -z, v⟩

/-- Transfer of the hypothesis along the coefficient operation. -/
theorem hasEverywhereLoewnerBounds_sectionTwoCoefficient {A : FullKineticCoefficient d}
    {lam Lam : ℝ}
    (hA : ∀ P : KineticPoint d, lam • (1 : PDE.Mat d) ≤ fullKineticCoefficientAt A P ∧
      fullKineticCoefficientAt A P ≤ Lam • (1 : PDE.Mat d)) :
    HasEverywhereLoewnerBounds lam Lam (sectionTwoCoefficient A) := fun σ v z =>
  hA ⟨-σ, -z, v⟩

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Assembly
