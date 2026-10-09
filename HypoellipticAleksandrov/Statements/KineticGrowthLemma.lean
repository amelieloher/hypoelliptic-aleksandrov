module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.Assembly
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Setting
public import Mathlib.Analysis.Matrix.MeasurableSpace

/-!
# Kinetic growth lemma

The growth lemma underlying the Hölder estimate of companion paper, Section 9, under the
standing assumptions of that section. Admissibility is a hypothesis; the covering and
propagation conclusions are not additional hypotheses.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set MeasureTheory
open scoped MatrixOrder

/-- Every positive sampling density gives a uniform lower bound on the target cylinder. -/
theorem kinetic_growth_lemma
    (d : ℕ) (hd : 1 ≤ d) (lam Lam p C_A : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (hp : 1 ≤ p) :
    ∃ theta : ℝ, 0 < theta ∧ theta < 1 ∧
      ∃ (P_Sigma : KineticPoint d) (r_Sigma : ℝ), 0 < r_Sigma ∧
        closure (backwardCylinder P_Sigma r_Sigma) ⊆
          backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 ∧
        ∀ beta : ℝ, 0 < beta → beta ≤ 1 →
          ∃ kappa_beta : ℝ, 0 < kappa_beta ∧
            ∀ A : FullKineticCoefficient d,
              Measurable (fullKineticCoefficientAt A) →
              (∀ P : KineticPoint d, (fullKineticCoefficientAt A P).IsSymm) →
              (∀ᵐ P ∂(volume : Measure (KineticPoint d)),
                lam • (1 : PDE.Mat d) ≤ fullKineticCoefficientAt A P) →
              (∀ᵐ P ∂(volume : Measure (KineticPoint d)),
                fullKineticCoefficientAt A P ≤ Lam • (1 : PDE.Mat d)) →
              ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
              ∀ O : Set (KineticPoint d), IsOpen O →
                closure (backwardCylinder P₀ R) ⊆ O →
              ∀ u : KineticPoint d → ℝ,
                (∀ P ∈ O, 0 ≤ u P) → IsAdmissibleSupersolution A O p C_A u →
                beta * (volume (kineticAffine P₀ R ''
                  backwardCylinder P_Sigma r_Sigma)).toReal ≤
                    (volume ({P | 1 ≤ u P} ∩ (kineticAffine P₀ R ''
                      backwardCylinder P_Sigma r_Sigma))).toReal →
                ∀ P ∈ backwardCylinder P₀ (theta * R), kappa_beta ≤ u P := by
  exact HypoellipticAleksandrov.KineticAleksandrov.kinetic_growth_lemma_aux
    d hd lam Lam p C_A hlam hLam hp

end HypoellipticAleksandrov.KineticAleksandrov.Holder
