module

public import HypoellipticAleksandrov.Statements.KineticHolder
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Holder.TestSource
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Holder.Linear
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Admissibility
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonLinear
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonConstant

/-!
# Admissibility of bounded solutions for full coefficients, and the Hölder corollary

Fix `p = p_*`. If `u` is a bounded `C^{1,1,2}` solution
of `P_A u = 0` almost everywhere on an open set, then both `u` and `-u` are admissible
supersolutions with Aleksandrov data `(p_*, C)` in the sense of (9.6) of the companion paper: for
`ψ` smooth near the
closure of a cylinder, apply the localized Aleksandrov estimate to `ψ - u`, whose positivity set is
`{u < ψ}` and for which `P_A (ψ - u) = P_A ψ` almost everywhere. The implication
`kinetic_holder_of_aleksandrov` (companion paper, Theorem 9.1) then gives the Hölder corollary.
Because the coefficient satisfies
its bounds only almost everywhere, only the `L^p` norm of the localized source is used, and it is
computed almost everywhere.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open HypoellipticAleksandrov Parabolic Holder Set MeasureTheory
open scoped MatrixOrder ENNReal

/-- The localized Aleksandrov estimate for Borel full coefficients at one exponent with one
constant, as a predicate (the conclusion of the Aleksandrov estimate for full coefficients at
exponent `p`). -/
def FullAleksandrovEstimate {d : ℕ} (lam Lam p C : ℝ) : Prop :=
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
    (∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)), backwardOperator A u P ≤ f P) →
    MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
      (volume.restrict (backwardCylinder P₀ R)) →
    ∀ P ∈ closure (backwardCylinder P₀ R),
      u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
        C * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
          (eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0)) (ENNReal.ofReal p)
            (volume.restrict (backwardCylinder P₀ R))).toReal

/-- A `C^{1,1,2}` function with `P_A w = 0` almost everywhere on `Ω` is an admissible
supersolution with the data of the Aleksandrov estimate. -/
theorem full_isAdmissibleSupersolution_of_estimate {d : ℕ} {lam Lam p C : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (hE : FullAleksandrovEstimate (d := d) lam Lam p C)
    {A : FullKineticCoefficient d} (hBorel : Measurable (fullKineticCoefficientAt A))
    (hsymm : ∀ P : KineticPoint d, (fullKineticCoefficientAt A P).IsSymm)
    (hlo : ∀ᵐ P ∂(volume : Measure (KineticPoint d)),
      lam • (1 : PDE.Mat d) ≤ fullKineticCoefficientAt A P)
    (hhi : ∀ᵐ P ∂(volume : Measure (KineticPoint d)),
      fullKineticCoefficientAt A P ≤ Lam • (1 : PDE.Mat d))
    {Omega : Set (KineticPoint d)} {w : KineticPoint d → ℝ}
    (hw : IsKineticC112On w Omega)
    (hweq : ∀ᵐ P ∂(volume.restrict Omega), backwardOperator A w P = 0) :
    IsAdmissibleSupersolution A Omega p C w := by
  refine ⟨hw.continuousOn, ?_⟩
  intro P₀ R hR hQ psi hpsi
  obtain ⟨U, _hU, hUQ, hps⟩ := smoothNear_regular_of_full hpsi
  have hQQ : backwardCylinder P₀ R ⊆ Omega := subset_closure.trans hQ
  have hpr := comparison_regular_mono hps (subset_closure.trans hUQ)
  have hwr := comparison_regular_mono hw hQQ
  have hneg := comparison_regular_const_mul hwr (-1)
  have hdiff : IsKineticC112On (fun P => psi P - w P) (backwardCylinder P₀ R) := by
    simpa only [neg_one_mul, sub_eq_add_neg] using comparison_regular_add hpr hneg
  have hop : ∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
      backwardOperator A (fun Q => psi Q - w Q) P ≤ backwardOperator A psi P := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hQQ hweq,
      ae_restrict_mem (isOpen_backwardCylinder P₀ R hR).measurableSet] with P he hP
    rw [backwardOperator_sub_of_regular hpr hwr A hP, he]
    simp only [sub_zero, le_refl]
  obtain ⟨hmeas, hLp⟩ := full_test_source hlam hLam hBorel hlo hhi P₀ R hR hpsi
  have hn : {P | 0 < psi P - w P} = {P | w P < psi P} := by
    ext P
    exact sub_pos
  have hbnd := hE P₀ R hR A hBorel hsymm hlo hhi (backwardOperator A psi)
    (fun P => psi P - w P) hmeas
    (hpsi.continuousOn.sub (hw.continuousOn.mono hQ)) hdiff hop (hLp _)
  have hbnd' : ∀ P ∈ closure (backwardCylinder P₀ R), psi P - w P ≤
      sSup ((fun P => max (psi P - w P) 0) '' kineticBoundary P₀ R) +
        C * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
          (eLpNorm (localizedSource A psi w) (ENNReal.ofReal p)
            (volume.restrict (backwardCylinder P₀ R))).toReal := by
    simpa only [hn, localizedSource] using hbnd
  apply csSup_le
  · exact (backwardCylinder_nonempty P₀ hR).closure.image _
  · rintro y ⟨P, hP, rfl⟩
    exact hbnd' P hP

/-- A `C^{1,1,2}` solution of `P_A u = 0` almost everywhere is an admissible
solution: both `u` and `-u` are admissible supersolutions. -/
theorem full_isAdmissibleSolution_of_estimate {d : ℕ} {lam Lam p C : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (hE : FullAleksandrovEstimate (d := d) lam Lam p C)
    {A : FullKineticCoefficient d} (hBorel : Measurable (fullKineticCoefficientAt A))
    (hsymm : ∀ P : KineticPoint d, (fullKineticCoefficientAt A P).IsSymm)
    (hlo : ∀ᵐ P ∂(volume : Measure (KineticPoint d)),
      lam • (1 : PDE.Mat d) ≤ fullKineticCoefficientAt A P)
    (hhi : ∀ᵐ P ∂(volume : Measure (KineticPoint d)),
      fullKineticCoefficientAt A P ≤ Lam • (1 : PDE.Mat d))
    {Omega : Set (KineticPoint d)} (hOmega : IsOpen Omega) {u : KineticPoint d → ℝ}
    (hu : IsKineticC112On u Omega)
    (heq : ∀ᵐ P ∂(volume.restrict Omega), backwardOperator A u P = 0) :
    IsAdmissibleSolution A Omega p C u := by
  refine ⟨full_isAdmissibleSupersolution_of_estimate hlam hLam hE hBorel hsymm hlo hhi
    hu heq, ?_⟩
  have hneg : IsKineticC112On (fun P => -u P) Omega := by
    simpa only [neg_one_mul] using comparison_regular_const_mul hu (-1)
  refine full_isAdmissibleSupersolution_of_estimate hlam hLam hE hBorel hsymm hlo hhi
    hneg ?_
  filter_upwards [heq, ae_restrict_mem hOmega.measurableSet] with P he hP
  rw [backwardOperator_neg_of_regular hu A hP, he, neg_zero]

/-- Target A5: the localized Aleksandrov estimate for full coefficients at the single exponent
`p_* = 1 + (128 d²/3)(Λ/λ)²` implies the interior Hölder estimate for full coefficients. -/
theorem kinetic_holder_fullCoefficient_of_aleksandrov
    (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hAleks : ∃ C : ℝ, 0 ≤ C ∧
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
        MemLp (fun P => max (f P) 0)
          (ENNReal.ofReal (1 + 128 * (d : ℝ) ^ 2 * (Lam / lam) ^ 2 / 3))
          (volume.restrict (backwardCylinder P₀ R)) →
        ∀ P ∈ closure (backwardCylinder P₀ R),
          u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
            C * R ^ (2 - (4 * (d : ℝ) + 2) / (1 + 128 * (d : ℝ) ^ 2 * (Lam / lam) ^ 2 / 3)) *
              (eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0))
                (ENNReal.ofReal (1 + 128 * (d : ℝ) ^ 2 * (Lam / lam) ^ 2 / 3))
                (volume.restrict (backwardCylinder P₀ R))).toReal) :
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
  obtain ⟨C, _hC0, hC⟩ := hAleks
  have hratio : 0 ≤ (Lam / lam) ^ 2 := sq_nonneg _
  have hp : 1 ≤ 1 + 128 * (d : ℝ) ^ 2 * (Lam / lam) ^ 2 / 3 := by
    have : 0 ≤ 128 * (d : ℝ) ^ 2 * (Lam / lam) ^ 2 / 3 := by positivity
    linarith only [this]
  obtain ⟨alpha, C', ha, ha1, hholder⟩ := kinetic_holder_of_aleksandrov d hd lam Lam
    (1 + 128 * (d : ℝ) ^ 2 * (Lam / lam) ^ 2 / 3) C hlam hLam hp
  refine ⟨alpha, C', ha, ha1, ?_⟩
  intro A hBorel hsymm hlo hhi Omega hOmega u hbounded hu heq
  have hE : FullAleksandrovEstimate (d := d) lam Lam
      (1 + 128 * (d : ℝ) ^ 2 * (Lam / lam) ^ 2 / 3) C := hC
  exact hholder A hBorel hsymm hlo hhi Omega hOmega u hbounded
    (full_isAdmissibleSolution_of_estimate hlam hLam hE hBorel hsymm hlo hhi hOmega hu heq)

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
