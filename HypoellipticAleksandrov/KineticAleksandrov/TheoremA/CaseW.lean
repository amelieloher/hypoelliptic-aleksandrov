module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ReflectionCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.SourceNotation

/-!
# Case W: the reflected time-velocity coefficient is in the whole-space setting (W)

Companion paper, proof of Theorem 1.1: for a smooth coefficient `A(t,v)` independent of position,
reflection gives the operator of case (W), with `z = X`, `B(s,v) = A(-s,v)`, `b(v) = v`, `D = ℝ^d`
and `m = L_b = 1`.

Carrier dictionary.  A kinetic point `(s,X,v)` is read as the Section 2 point `(σ,v,z) = (s,v,X)`
(the `position` field of a Section 2 point is the diffused coordinate `v`, its `velocity` field the
transported coordinate `z`, see `Operator.lean`): this is the coordinate swap `sectionTwoPoint`.

* `forwardKineticOperator_eq_lop_identity`: (6.3) equals (2.3) for `b = id`, `z = X`;
* `reflected_lop_identity`: with (6.4), `L̃ (u ∘ ℛ) = -(P_A u) ∘ ℛ`;
* `caseW_sourceSetting`: `SourceSetting λ Λ 1 1 ℝ^d Ã id`, i.e. the reflected coefficient and the
  identity drift satisfy all Section 2 setting premises of case (W) (this is the shared discharge
  object of Proposition 2.1);
* `kinetic_aleksandrov_caseW`: the conjunction of the above.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.TheoremA

open Set
open HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay
open scoped MatrixOrder ContDiff Matrix.Norms.Elementwise

/-- A kinetic point `(s,X,v)` read as the Section 2 point `(σ,v,z) = (s,v,X)`. -/
def sectionTwoPoint {d : ℕ} (P : KineticPoint d) : KineticPoint d :=
  ⟨P.time, P.velocity, P.position⟩

/-- The coordinate swap is an involution. -/
theorem sectionTwoPoint_involutive {d : ℕ} :
    Function.Involutive (sectionTwoPoint (d := d)) := fun _ => rfl

/-- (6.3) is (2.3) with `z = X`, `b(v) = v` and the same time-velocity coefficient. -/
theorem forwardKineticOperator_eq_lop_identity {d : ℕ} (B : CoefficientField d)
    (U : KineticPoint d → ℝ) (P : KineticPoint d) :
    forwardKineticOperator (ofTimeVelocityCoefficient B) U P =
      lop B (identityDrift d) (U ∘ sectionTwoPoint) (sectionTwoPoint P) := by
  rw [forwardKineticOperator_apply, lop,
    transportedForwardOperatorOfTimeDiffusedCoefficient_apply]
  have h1 : kineticTimeDerivative (U ∘ sectionTwoPoint) (sectionTwoPoint P) =
      kineticTimeDerivative U P := rfl
  have h2 : diffusedHessian (U ∘ sectionTwoPoint) (sectionTwoPoint P) =
      kineticVelocityHessian U P := rfl
  have h3 : kineticVelocityGradient (U ∘ sectionTwoPoint) (sectionTwoPoint P) =
      kineticPositionGradient U P := rfl
  have h4 : identityDrift d (sectionTwoPoint P).position = P.velocity := rfl
  rw [h1, h2, h3, h4]
  exact add_right_comm _ _ _

/-- The reflected function solves (2.3) with `B(s,v) = A(-s,v)`, `b = id`, `z = X`. -/
theorem reflected_lop_identity {d : ℕ} (A : CoefficientField d) (u : KineticPoint d → ℝ)
    (P : KineticPoint d) :
    lop (kineticReflectedCoefficient A) (identityDrift d)
        ((u ∘ kineticReflection) ∘ sectionTwoPoint) (sectionTwoPoint P) =
      -backwardOperatorOfTimeVelocityCoefficient A u (kineticReflection P) := by
  rw [← forwardKineticOperator_eq_lop_identity]
  exact reflectedKineticOperator_reflection A u P

/-- Entrywise smoothness of the `z`-independent lift of a smooth time-velocity coefficient. -/
theorem isSmoothFullKineticCoefficient_zIndependent {d : ℕ} {B : CoefficientField d}
    (hB : IsSmoothCoefficient B) :
    IsSmoothFullKineticCoefficient (zIndependentCoefficient B) := by
  intro i j
  have hcomp : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × (PDE.Vec d × PDE.Vec d) =>
      coefficientAt B (q.1, q.2.1)) :=
    hB.comp (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd))
  exact (contDiff_pi.1 ((contDiff_pi.1 hcomp) i)) j

/-- The reflected coefficient and the identity drift satisfy the setting (W) premises,
with `m = L_b = 1` and `D = ℝ^d`. -/
theorem caseW_sourceSetting {d : ℕ} {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    {A : CoefficientField d} (hsm : IsSmoothCoefficient A) (hsymm : IsSymmetricCoefficient A)
    (hlo : HasLowerEllipticity lam A) (hhi : HasUpperEllipticity Lam A) :
    SourceSetting lam Lam 1 1 (wholeSpace d) (kineticReflectedCoefficient A)
      (identityDrift d) := by
  refine ⟨⟨hlam, hLam, isSmoothFullKineticCoefficient_zIndependent
      (isSmoothCoefficient_kineticReflectedCoefficient A hsm),
    isSymmetricCoefficient_kineticReflectedCoefficient A hsymm,
    fun s v => hlo (-s) v, fun s v => hhi (-s) v⟩,
    identityDrift_smooth d, one_pos, le_rfl, identityDrift_bounds d,
    Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩

/-- **Case W.**  A smooth symmetric coefficient `A(t,v)` with pointwise ellipticity bounds
is reflected into the whole-space setting (W): the reflected operator is (2.3) for `z = X`,
`B(s,v) = A(-s,v)`, `b(v) = v`, `D = ℝ^d`, `m = L_b = 1`, and `K_Ã (u ∘ ℛ) = -(P_A u) ∘ ℛ`. -/
theorem kinetic_aleksandrov_caseW {d : ℕ} {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    {A : CoefficientField d} (hsm : IsSmoothCoefficient A) (hsymm : IsSymmetricCoefficient A)
    (hlo : HasLowerEllipticity lam A) (hhi : HasUpperEllipticity Lam A) :
    SourceSetting lam Lam 1 1 (wholeSpace d) (kineticReflectedCoefficient A)
        (identityDrift d) ∧
      (∀ (s : ℝ) (v : PDE.Vec d), kineticReflectedCoefficient A s v = A (-s) v) ∧
      (∀ (U : KineticPoint d → ℝ) (P : KineticPoint d),
        forwardKineticOperator (ofTimeVelocityCoefficient (kineticReflectedCoefficient A)) U P =
          lop (kineticReflectedCoefficient A) (identityDrift d) (U ∘ sectionTwoPoint)
            (sectionTwoPoint P)) ∧
      (∀ (u : KineticPoint d → ℝ) (P : KineticPoint d),
        lop (kineticReflectedCoefficient A) (identityDrift d)
            ((u ∘ kineticReflection) ∘ sectionTwoPoint) (sectionTwoPoint P) =
          -backwardOperatorOfTimeVelocityCoefficient A u (kineticReflection P)) :=
  ⟨caseW_sourceSetting hlam hLam hsm hsymm hlo hhi, kineticReflectedCoefficient_apply A,
    forwardKineticOperator_eq_lop_identity _, reflected_lop_identity A⟩

end HypoellipticAleksandrov.KineticAleksandrov.TheoremA
