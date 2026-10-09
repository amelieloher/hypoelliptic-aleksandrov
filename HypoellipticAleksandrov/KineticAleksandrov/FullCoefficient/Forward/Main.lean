module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Forward.General
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Forward.Slices
import HypoellipticAleksandrov.LinearAlgebra.LoewnerEntryBound

/-!
# The forward equation of the Green slices

The forward equation and the admissible test functions.  Setting (case W): a smooth symmetric
uniformly
elliptic full coefficient `B σ v z`, identity drift, a realization `(S, K)` of the terminal
evolution, a pole `p` at time `σ₀`, a horizon `T > 0` and the Green measure `Γ` of the point
mass at `p`.  For every admissible test function `φ` all terms of the forward integrand are
`Γ`-integrable and
`∫ (∂_τ φ + B(σ₀ + τ, y) : D_v² φ + v · ∇_z φ) dΓ = 0`.
The slice description of `Γ` (the slice description) is in `Forward/Slices.lean`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory Set
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal

variable {d : ℕ} {T : ℝ} {φ : ℝ → EvolutionAmbientState d → ℝ}

/-- A bounded continuous function of `(τ, y)` is integrable on the Green space of a finite
measure. -/
theorem integrable_comp_green {S : ℝ≥0∞} (Γ : Measure (ElapsedTime S × EvolutionAmbientState d))
    [IsFiniteMeasure Γ] {f : ℝ × EvolutionAmbientState d → ℝ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ q, |f q| ≤ C) :
    Integrable (fun q : ElapsedTime S × EvolutionAmbientState d => f (q.1.1, q.2)) Γ :=
  Integrable.of_bound (hf.comp ((continuous_subtype_val.comp continuous_fst).prodMk
    continuous_snd)).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun q => by simpa [Real.norm_eq_abs] using hC _)

/-- **The forward equation of the Green slices**.
For every admissible test function `φ`, the three terms of the forward integrand are
`Γ`-integrable and the integral of their sum against the Green measure of the point mass `p`
vanishes. -/
theorem forward_equation {lam Lam : ℝ} (hd : 1 ≤ d) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : FullKineticCoefficient d) (hB : IsSmoothFullKineticCoefficient B)
    (hBs : IsSymmetricFullKineticCoefficient B) (hell : HasEverywhereLoewnerBounds lam Lam B)
    (S : TerminalOperatorFamily (wholeSpace d) (fun _ => 0))
    (K : MovingFiberKernel (wholeSpace d) (fun _ => 0))
    (hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ B
      (identityDrift d) S K)
    (σ₀ : ℝ) (hT : 0 < T) (p : EvolutionState (wholeSpace d) (fun _ => 0) σ₀)
    (Γ : Measure (ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d))
    (hΓ : IsGreenMeasure K σ₀ (ENNReal.ofReal T) (Measure.dirac p) Γ)
    (hφ : IsAdmissibleTest T φ) :
    Integrable (fun q : ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d =>
      deriv (fun τ => φ τ q.2) q.1.1) Γ ∧
    Integrable (fun q : ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d =>
      velocityHessianContraction (B (σ₀ + q.1.1) q.2.1 q.2.2) (φ q.1.1) q.2) Γ ∧
    Integrable (fun q : ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d =>
      transportDerivative (φ q.1.1) q.2) Γ ∧
    ∫ q, (deriv (fun τ => φ τ q.2) q.1.1 +
      velocityHessianContraction (B (σ₀ + q.1.1) q.2.1 q.2.2) (φ q.1.1) q.2 +
        transportDerivative (φ q.1.1) q.2) ∂Γ = 0 := by
  have hΛ0 : 0 ≤ Lam := hlam.le.trans hLam
  have hBΛ : ∀ σ y z i j, |B σ y z i j| ≤ Lam := fun σ y z i j =>
    HypoellipticAleksandrov.abs_apply_le_of_loewner hlam (hell σ y z).1 (hell σ y z).2 i j
  have : IsFiniteMeasure Γ := ⟨lt_of_le_of_lt (greenMeasure_mass_le K σ₀ T hT
    (Measure.dirac p) Γ hΓ) (ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top)⟩
  obtain ⟨Ct, hCt⟩ := hφ.timeDeriv.2
  obtain ⟨Ch, hCh⟩ := exists_uniform_bound (fun (ij : Fin d × Fin d)
    (q : ℝ × EvolutionAmbientState d) => testHessian φ ij.1 ij.2 q)
    (fun ij => (hφ.velocityHess _ _).2)
  obtain ⟨Cw, hCw⟩ := exists_uniform_bound (fun (i : Fin d) (q : ℝ × EvolutionAmbientState d) =>
    q.2.1 i * testPosition φ i q) (fun i => (hφ.weightedTransport i i).2)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact integrable_comp_green Γ (f := fun q => deriv (fun τ => φ τ q.2) q.1) hφ.timeDeriv.1 hCt
  · refine integrable_comp_green Γ
      (f := fun q => ∑ i, ∑ j, B (σ₀ + q.1) q.2.1 q.2.2 i j * testHessian φ i j q) ?_
      (C := (d : ℝ) * d * (Lam * Ch)) fun q => ?_
    · exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
        ((hB i j).continuous.comp ((continuous_const.add continuous_fst).prodMk
          continuous_snd)).mul (hφ.velocityHess i j).1
    · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i, |∑ j, B (σ₀ + q.1) q.2.1 q.2.2 i j * testHessian φ i j q|
          ≤ ∑ _i : Fin d, ∑ _j : Fin d, Lam * Ch := by
            refine Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum fun j _ => ?_)
            rw [abs_mul]
            exact mul_le_mul (hBΛ _ _ _ _ _) (hCh (i, j) q) (abs_nonneg _) hΛ0
        _ = (d : ℝ) * d * (Lam * Ch) := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
  · refine integrable_comp_green Γ (f := fun q => ∑ i, q.2.1 i * testPosition φ i q)
      (continuous_finsetSum _ fun i _ => (hφ.weightedTransport i i).1)
      (C := (d : ℝ) * Cw) fun q => ?_
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |q.2.1 i * testPosition φ i q| ≤ ∑ _i : Fin d, Cw :=
          Finset.sum_le_sum fun i _ => hCw i q
      _ = (d : ℝ) * Cw := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  · exact integral_forwardIntegrand_green_eq_zero hd hlam hLam B hB hBs hell S K hreal σ₀ hT p Γ
      hΓ hφ

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
