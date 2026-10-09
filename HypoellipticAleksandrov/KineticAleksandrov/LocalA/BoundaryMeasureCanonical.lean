module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundaryMeasure
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.Analysis.Complex.Trigonometric

/-! # Canonical ball exit measure, selected from its proved unique characterization -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory
open scoped ENNReal

variable (hH : HormanderHypoellipticityStatement)
  (hLE : LiebermanEllipsoidDirichletStatement)
  {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ}
  (hlam : 0 < lam) (hLam : lam ≤ Lam)
  (B : CoefficientField d) (hB : SectionTwo.IsSectionTwoCoefficient lam Lam B)
  (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)

/-- The actual finite exit measure, chosen only after full existence and uniqueness. -/
def ballExitRaw (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t}) :
    Measure (KineticPoint d) :=
  (existsUnique_ballExitMeasure hH hLE hd hlam hLam B hB v₀ hR P T).exists.choose

/-- Full finite-measure, trace-support and smooth-test characterization of the choice. -/
theorem ballExitRaw_spec (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t}) :
    IsFiniteMeasure (ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T) ∧
    ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T (localTrace P.1.time T.1 v₀ R)ᶜ = 0 ∧
    ∀ φ : KineticPoint d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) (φ ∘ (KineticPoint.equivProd d).symm) →
      HasCompactSupport φ →
      (∫ Q, φ Q ∂ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T) =
        ballBoundarySolution hH hLE hd hlam hLam B hB v₀ hR P.1.time T.1 φ P.1 :=
  (existsUnique_ballExitMeasure hH hLE hd hlam hLam B hB v₀ hR P T).exists.choose_spec

/-- The chosen exit measure is finite. -/
instance ballExitRaw_isFiniteMeasure (P : LocalBallStart v₀ R)
    (T : {t : ℝ // P.1.time < t}) :
    IsFiniteMeasure (ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T) :=
  (ballExitRaw_spec hH hLE hd hlam hLam B hB v₀ hR P T).1

/-- The stated smooth-test identity alone determines the selected finite ambient measure. -/
theorem ballExitRaw_unique (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})
    (μ : Measure (KineticPoint d)) [IsFiniteMeasure μ]
    (hμ : ∀ φ : KineticPoint d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) (φ ∘ (KineticPoint.equivProd d).symm) →
      HasCompactSupport φ → (∫ Q, φ Q ∂μ) =
        ballBoundarySolution hH hLE hd hlam hLam B hB v₀ hR P.1.time T.1 φ P.1) :
    μ = ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T := by
  apply boundary_measure_ext
  intro φ hφ hc
  exact (hμ φ hφ hc).trans ((ballExitRaw_spec hH hLE hd hlam hLam B hB v₀ hR P T).2.2
    φ hφ hc).symm

/-- Exit coordinates retain absolute exit time and exit velocity, and subtract free transport. -/
def ballExit (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t}) :
    Measure (PDE.Vec d × Parabolic.TimeVelocity d) :=
  Measure.map (exitCoordinates P.1 v₀) (ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T)

/-- The actual exit-coordinate measure is finite. -/
instance ballExit_isFiniteMeasure (P : LocalBallStart v₀ R)
    (T : {t : ℝ // P.1.time < t}) :
    IsFiniteMeasure (ballExit hH hLE hd hlam hLam B hB v₀ hR P T) := by
  unfold ballExit
  infer_instance

omit hH hLE hd hlam hLam B hB v₀ hR in
/-- The generic exit Fourier measure is the literal phase-density map to time and velocity. -/
def exitFourier (ω : Measure (PDE.Vec d × Parabolic.TimeVelocity d)) (ξ : PDE.Vec d) :
    ComplexMeasure (Parabolic.TimeVelocity d) :=
  (ω.withDensityᵥ (exitPhase ξ)).map Prod.snd

omit hH hLE hd hlam hLam B hB v₀ hR in
/-- The literal exit phase has modulus one. -/
theorem norm_exitPhase (ξ : PDE.Vec d) (Q : PDE.Vec d × Parabolic.TimeVelocity d) :
    ‖exitPhase ξ Q‖ = 1 := by
  simp [exitPhase, Complex.norm_exp, Complex.mul_re]

omit hH hLE hd hlam hLam B hB v₀ hR in
/-- The literal exit phase is continuous. -/
theorem continuous_exitPhase (ξ : PDE.Vec d) : Continuous (exitPhase ξ) := by
  unfold exitPhase PDE.vecDot
  fun_prop

omit hH hLE hd hlam hLam B hB v₀ hR in
/-- Every finite exit-coordinate measure admits the actual phase integral. -/
theorem integrable_exitPhase (ω : Measure (PDE.Vec d × Parabolic.TimeVelocity d))
    [IsFiniteMeasure ω] (ξ : PDE.Vec d) : Integrable (exitPhase ξ) ω :=
  Integrable.mono' (integrable_const (1 : ℝ))
    (continuous_exitPhase ξ).measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun Q => (norm_exitPhase ξ Q).le))

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
