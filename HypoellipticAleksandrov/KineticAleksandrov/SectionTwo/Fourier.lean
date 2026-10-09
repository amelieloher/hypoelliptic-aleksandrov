module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Realization
public import Mathlib.MeasureTheory.Measure.Complex
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
import Mathlib.Analysis.Complex.Trigonometric

/-! # Fourier projection by its unique measure characterization -/

@[expose] public section

noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

/-- Displacement Fourier phase, with terminal states ordered (v,z). -/
def fourierPhase {d : ℕ} (ξ z : PDE.Vec d) (q : EvolutionAmbientState d) : ℂ :=
  Complex.exp (-Complex.I * (PDE.vecDot ξ (q.2 - z) : ℂ))

/-- Exact source characterization of the Fourier-projected complex measure. -/
def IsFourierProjection {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    (K : MovingFiberKernel Ω γ) (q : EvolutionQuery Ω γ) (ξ : PDE.Vec d)
    (ν : ComplexMeasure (PDE.Vec d)) : Prop :=
  ∀ E : Set (PDE.Vec d), MeasurableSet E →
    ν E = ∫ w in E ×ˢ Set.univ, fourierPhase ξ q.1.2.2.2 w ∂K.master q

/-- The phase has modulus one. -/
theorem norm_fourierPhase {d : ℕ} (ξ z : PDE.Vec d) (q : EvolutionAmbientState d) :
    ‖fourierPhase ξ z q‖ = 1 := by
  simp [fourierPhase, Complex.norm_exp, Complex.mul_re]

/-- The phase is continuous. -/
theorem continuous_fourierPhase {d : ℕ} (ξ z : PDE.Vec d) :
    Continuous (fourierPhase ξ z) := by
  unfold fourierPhase PDE.vecDot
  fun_prop

/-- Master measures are finite by their sub-Markov bound. -/
instance master_isFiniteMeasure {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    (K : MovingFiberKernel Ω γ) (q : EvolutionQuery Ω γ) : IsFiniteMeasure (K.master q) :=
  ⟨(K.mass_le_one q).trans_lt ENNReal.one_lt_top⟩

/-- Modulus-one phases are integrable without additional hypotheses. -/
theorem fourierPhase_integrable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    (K : MovingFiberKernel Ω γ) (q : EvolutionQuery Ω γ) (ξ z : PDE.Vec d) :
    Integrable (fourierPhase ξ z) (K.master q) := by
  exact Integrable.mono' (integrable_const (1 : ℝ))
    (continuous_fourierPhase ξ z).measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun w => (norm_fourierPhase ξ z w).le))

/-- The concrete density pushforward has the source characterization. -/
theorem densityMap_isFourierProjection {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ) (q : EvolutionQuery Ω γ)
    (ξ : PDE.Vec d) : IsFourierProjection K q ξ
      (((K.master q).withDensityᵥ (fourierPhase ξ q.1.2.2.2)).map Prod.fst) := by
  intro E hE
  rw [VectorMeasure.map_apply _ measurable_fst hE,
    withDensityᵥ_apply (fourierPhase_integrable K q ξ _) (measurable_fst hE)]
  have hset : (Prod.fst : EvolutionAmbientState d → PDE.Vec d) ⁻¹' E = E ×ˢ univ := by
    ext w
    simp only [mem_preimage, mem_prod, mem_univ, and_true]
  rw [hset]

/-- Well-definedness must be proved before materializing the Fourier measure. -/
theorem existsUnique_fourierProjection {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ)
    (q : EvolutionQuery Ω γ) (ξ : PDE.Vec d) :
    ∃! ν : ComplexMeasure (PDE.Vec d), IsFourierProjection K q ξ ν := by
  refine ⟨_, densityMap_isFourierProjection K q ξ, ?_⟩
  intro ν hν
  apply VectorMeasure.ext
  intro E hE
  exact (hν E hE).trans ((densityMap_isFourierProjection K q ξ E hE).symm)


/-- Fourier measure selected only after existence and uniqueness are proved. -/
def fourierProjection {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    (K : MovingFiberKernel Ω γ) (q : EvolutionQuery Ω γ) (ξ : PDE.Vec d) :
    ComplexMeasure (PDE.Vec d) := (existsUnique_fourierProjection K q ξ).exists.choose

/-- The full characterization accompanies the unique-choice definition. -/
theorem fourierProjection_spec {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    (K : MovingFiberKernel Ω γ) (q : EvolutionQuery Ω γ) (ξ : PDE.Vec d) :
    IsFourierProjection K q ξ (fourierProjection K q ξ) :=
  (existsUnique_fourierProjection K q ξ).exists.choose_spec

/-- Any characterized measure equals the integrable density pushforward. -/
theorem fourierProjection_eq_densityMap {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ) (q : EvolutionQuery Ω γ)
    (ξ : PDE.Vec d) (ν : ComplexMeasure (PDE.Vec d)) (hν : IsFourierProjection K q ξ ν) :
    ν = ((K.master q).withDensityᵥ (fourierPhase ξ q.1.2.2.2)).map Prod.fst := by
  apply VectorMeasure.ext
  intro E hE
  exact (hν E hE).trans ((densityMap_isFourierProjection K q ξ E hE).symm)

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
