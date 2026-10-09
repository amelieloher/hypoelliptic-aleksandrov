module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.FourierKernelsVariation
public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabSetting
public import HypoellipticAleksandrov.KineticAleksandrov.BoundedBorel

/-!
# The two predecessor conclusions consumed by Lemma 5.1 (case W)

Lemma 5.1 of the companion paper consumes the conclusions of Proposition 4.2 (the density of the
parabolic occupation measure and its `L^γ` bound) and of Proposition 3.1 ((3.1)).  This module only
states their conclusions, for the one realized kernel `K`, as `Prop`s used as explicit premises by
the conditional assembly `Green.SlabFourier`:

* `ParabolicOccupationConclusion d K`: for every finite positive measure `ρ`, start time `σ₀` and
  horizon `S > 0` there is a non-negative Borel density `g` on `(0,S) × ℝ^d` of the occupation
  measure `∫ρ(dv) ∫_0^S ∫ φ(τ,w) P_{σ₀,σ₀+τ}(v,dw) dτ`, with `‖g‖_{L^γ} ≤ C_γ M S^{β_γ}`
  for `1 ≤ γ ≤ γ₀`.  The constants `C_γ` are quantified before `ρ, σ₀, S`.
* `FourierDecayConclusion d K`: `‖K̂^ξ_{σ,τ}(v,·)‖_TV ≤ C exp(-c (τ-σ) |ξ|^{2/3})`.

Here `P_{σ₀,σ₀+τ}(v,·)` is the first marginal of the master kernel from `(σ₀, (v, 0))`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Green

open MeasureTheory Set
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal NNReal

/-- The parabolic velocity marginal `P_{σ,σ+t}(v,·)` of the realized kernel, for `t ≥ 0`
(negative `t` is clamped to `0`; only `t > 0` is used). -/
def occupationKernel {d : ℕ} (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (σ t : ℝ) (v : PDE.Vec d) : Measure (PDE.Vec d) :=
  K.firstMarginal (wholeSpaceQuery σ (σ + max t 0) (le_add_of_nonneg_right (le_max_right t 0)) v 0)

/-- `g` is a non-negative Borel density on `(0,S) × ℝ^d` of the occupation measure of `ρ`
(companion paper, (4.2)), tested against all bounded Borel `φ`. -/
def SlabOccupationDensity {d : ℕ} (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (σ₀ S : ℝ) (ρ : Measure (PDE.Vec d)) (g : ℝ × PDE.Vec d → ℝ) : Prop :=
  Measurable g ∧ (∀ q, 0 ≤ g q) ∧
    ∀ φ : BoundedBorel (ℝ × PDE.Vec d),
      (∫ q, φ q * g q ∂volume.restrict (Ioo (0 : ℝ) S ×ˢ (univ : Set (PDE.Vec d)))) =
        ∫ v, ∫ τ : ElapsedTime (ENNReal.ofReal S), ∫ w, φ (τ.1, w)
            ∂K.firstMarginal (wholeSpaceQuery σ₀ (σ₀ + τ.1)
              (le_add_of_nonneg_right τ.2.1.le) v 0)
          ∂elapsedVolume (ENNReal.ofReal S) ∂ρ

/-- The occupation estimate of Proposition 4.2 with constants `C` (whole-space case, kernel `K`):
nonnegative constants for `1 ≤ γ ≤ γ₀`, and for every finite `ρ`, start time and horizon an
occupation density with `‖g‖_{L^γ} ≤ C_γ M S^{β_γ}`. -/
def OccupationBoundedBy {d : ℕ}
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))) (C : ℝ → ℝ) : Prop :=
  (∀ γ : ℝ, 1 ≤ γ → γ ≤ slabGamma0 d → 0 ≤ C γ) ∧
    ∀ (ρ : Measure (PDE.Vec d)) [IsFiniteMeasure ρ] (σ₀ S : ℝ), 0 < S →
      ∃ g : ℝ × PDE.Vec d → ℝ, SlabOccupationDensity K σ₀ S ρ g ∧
        ∀ γ : ℝ, 1 ≤ γ → γ ≤ slabGamma0 d →
          MemLp g (ENNReal.ofReal γ) (volume.restrict (Ioo (0 : ℝ) S ×ˢ (univ : Set (PDE.Vec d)))) ∧
          (eLpNorm g (ENNReal.ofReal γ)
              (volume.restrict (Ioo (0 : ℝ) S ×ˢ (univ : Set (PDE.Vec d))))).toReal ≤
            C γ * (ρ univ).toReal * S ^ slabBeta d γ

/-- Conclusion of Proposition 4.2 (whole-space case) for the realized kernel `K`; the structural
constants `C_γ` are quantified before `ρ, σ₀, S`. -/
def ParabolicOccupationConclusion (d : ℕ)
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))) : Prop :=
  ∃ C : ℝ → ℝ, OccupationBoundedBy K C

/-- The decay estimate (3.1) with constants `C, c` for the kernel `K`. -/
def FourierDecayBoundedBy {d : ℕ}
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))) (C c : ℝ) : Prop :=
  ∀ (σ τ : ℝ) (h : σ < τ) (v ξ : PDE.Vec d),
    totalVariationNorm (fourierKernel K σ τ h.le ξ v) ≤
      ENNReal.ofReal (C * Real.exp (-(c * (τ - σ) * PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3))))

/-- Conclusion of Proposition 3.1, estimate (3.1), for the realized kernel `K`. -/
def FourierDecayConclusion (d : ℕ)
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ FourierDecayBoundedBy K C c

/-- Family form of the conclusion of Proposition 4.2 (case W): the structural constants `C_γ`
depend on `d, λ, Λ` only and serve every coefficient with bounds `λ, Λ` and every realizing
evolution `(S, K)`. -/
def ParabolicOccupationFamily (d : ℕ) (lam Lam : ℝ) : Prop :=
  ∃ C : ℝ → ℝ, ∀ B : CoefficientField d, IsSectionTwoCoefficient lam Lam B →
    ∀ (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
      (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))),
      RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d)) MeasurableSet.univ
        (zIndependentCoefficient B) (identityDrift d) S K → OccupationBoundedBy K C

/-- Family form of the conclusion of Proposition 3.1 (case W, (3.1)): constants `C, c > 0`
depend on `d, λ, Λ` only. -/
def FourierDecayFamily (d : ℕ) (lam Lam : ℝ) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ B : CoefficientField d, IsSectionTwoCoefficient lam Lam B →
    ∀ (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
      (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))),
      RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d)) MeasurableSet.univ
        (zIndependentCoefficient B) (identityDrift d) S K → FourierDecayBoundedBy K C c

end HypoellipticAleksandrov.KineticAleksandrov.Green
