module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Absorb.Final
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Assembly.Smooth
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Borel.Passage
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Holder.Admissibility

/-!
# Proofs of the full-coefficient Aleksandrov and Hölder estimates

The Aleksandrov estimate for coefficients `A(t,x,v)` is assembled from the Green density bound
(`greenDensity_aux`), the smooth-coefficient estimate it implies,
and the passage to Borel coefficients; the Hölder estimate follows from the Aleksandrov estimate
at the threshold exponent through the Hölder theorem of the kinetic Aleksandrov principle.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal MatrixOrder

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open Holder

/-- The threshold `p ≥ 1 + 128 d² (Λ/λ)²/3` is the condition `p/(p-1) ≤ 1 + 3λ²/(128 d² Λ²)`. -/
theorem conjugate_le_of_threshold {d : ℕ} (hd : 1 ≤ d) {lam Lam p : ℝ} (hlam : 0 < lam)
    (hLam : lam ≤ Lam) (hp : 1 + 128 * (d : ℝ) ^ 2 * (Lam / lam) ^ 2 / 3 ≤ p) :
    1 < p ∧ p / (p - 1) ≤ 1 + 3 * lam ^ 2 / (128 * (d : ℝ) ^ 2 * Lam ^ 2) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hL : 0 < Lam := lt_of_lt_of_le hlam hLam
  have hp1 : 0 < 128 * (d : ℝ) ^ 2 * (Lam / lam) ^ 2 / 3 := by positivity
  have hp' : 1 < p := by linarith
  refine ⟨hp', ?_⟩
  have hp0 : 0 < p - 1 := by linarith
  have e : p / (p - 1) = 1 + 1 / (p - 1) := by field_simp; ring
  rw [e]
  have h1 : 128 * (d : ℝ) ^ 2 * (Lam / lam) ^ 2 / 3 ≤ p - 1 := by linarith
  have key : 1 / (p - 1) ≤ 3 * lam ^ 2 / (128 * (d : ℝ) ^ 2 * Lam ^ 2) := by
    rw [div_le_div_iff₀ hp0 (by positivity)]
    rw [div_pow, mul_div_assoc', div_div, div_le_iff₀ (by positivity)] at h1
    nlinarith
  linarith

/-- The proof of the kinetic Aleksandrov estimate for full coefficients. -/
theorem aleksandrov_aux
    (d : ℕ) (hd : 1 ≤ d) (lam Lam p : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hp : 1 + 128 * (d : ℝ) ^ 2 * (Lam / lam) ^ 2 / 3 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
      ∀ (A : FullKineticCoefficient d),
        Measurable (fullKineticCoefficientAt A) →
        (∀ P : KineticPoint d, (fullKineticCoefficientAt A P).IsSymm) →
        (∀ᵐ P ∂(volume : Measure (KineticPoint d)),
          lam • (1 : PDE.Mat d) ≤ fullKineticCoefficientAt A P) →
        (∀ᵐ P ∂(volume : Measure (KineticPoint d)),
          fullKineticCoefficientAt A P ≤ Lam • (1 : PDE.Mat d)) →
      ∀ (f u : KineticPoint d → ℝ),
        Measurable (fun P : backwardCylinder P₀ R => f P) →
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        Parabolic.IsKineticC112On u (backwardCylinder P₀ R) →
        (∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
          backwardOperator A u P ≤ f P) →
        MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
          (volume.restrict (backwardCylinder P₀ R)) →
        ∀ P ∈ closure (backwardCylinder P₀ R),
          u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
            C * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
              (eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0)) (ENNReal.ofReal p)
                (volume.restrict (backwardCylinder P₀ R))).toReal := by
  obtain ⟨hp', hqle⟩ := conjugate_le_of_threshold hd hlam hLam hp
  have hq : 1 < p / (p - 1) := by
    rw [lt_div_iff₀ (by linarith)]; linarith
  have hgreen := greenDensity_aux d hd lam (p / (p - 1)) hlam hq
  have hS := smooth_estimate_fullCoefficient_of_greenDensity d hd lam Lam p (p / (p - 1))
    hlam hLam hp' rfl hqle hgreen
  exact kinetic_aleksandrov_fullCoefficient_of_smooth d hd lam Lam p hlam hLam hp'.le hS

/-- The proof of the interior Hölder estimate for full coefficients. -/
theorem holder_aux
    (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧
      ∀ A : FullKineticCoefficient d,
        Measurable (fullKineticCoefficientAt A) →
        (∀ P : KineticPoint d, (fullKineticCoefficientAt A P).IsSymm) →
        (∀ᵐ P ∂(volume : Measure (KineticPoint d)),
          lam • (1 : PDE.Mat d) ≤ fullKineticCoefficientAt A P) →
        (∀ᵐ P ∂(volume : Measure (KineticPoint d)),
          fullKineticCoefficientAt A P ≤ Lam • (1 : PDE.Mat d)) →
      ∀ (Omega : Set (KineticPoint d)), IsOpen Omega →
      ∀ (u : KineticPoint d → ℝ),
        (∃ M : ℝ, ∀ P ∈ Omega, |u P| ≤ M) →
        Parabolic.IsKineticC112On u Omega →
        (∀ᵐ P ∂(volume.restrict Omega), backwardOperator A u P = 0) →
      ∀ (K : Set (KineticPoint d)), K ⊆ Omega → IsCompact K →
      ∀ (R₀ : ℝ), 0 < R₀ →
        (∀ P ∈ K, closure (backwardCylinder P (2 * R₀)) ⊆ Omega) →
      ∀ P ∈ K, ∀ P' ∈ K,
        |u P - u P'| ≤ C * oscillationOn u (holderNeighbourhood R₀ K) *
          (quasiDistance P P' / R₀) ^ alpha := by
  exact kinetic_holder_fullCoefficient_of_aleksandrov d hd lam Lam hlam hLam
    (aleksandrov_aux d hd lam Lam _ hlam hLam le_rfl)

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
