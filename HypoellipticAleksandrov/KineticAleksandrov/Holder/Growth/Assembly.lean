module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.TerminalLevel
import Mathlib.Tactic

/-! # The all-density kinetic growth lemma -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open Set MeasureTheory Holder Holder.Growth
open scoped ENNReal MatrixOrder

/-- The kinetic growth lemma, with every intermediate estimate proved internally. -/
theorem kinetic_growth_lemma_aux
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
                ∀ P ∈ backwardCylinder P₀ (theta * R), kappa_beta ≤ u P  := by
  obtain ⟨theta, ht, ht1, S, r, hr, hS, hbeta⟩ :=
    exists_growth_parameters d hd lam Lam p C_A hlam hLam hp
  refine ⟨theta, ht, ht1, S, r, hr, hS, ?_⟩
  intro beta hb hb1
  obtain ⟨kappa, hk, hbound⟩ := hbeta beta hb hb1
  refine ⟨kappa, hk, ?_⟩
  intro A hmeas hsym hlo hhi
  exact hbound A ⟨hmeas, hsym, hlo, hhi⟩

end HypoellipticAleksandrov.KineticAleksandrov
