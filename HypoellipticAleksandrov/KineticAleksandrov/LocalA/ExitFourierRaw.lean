module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitFourierBasic
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundaryMeasureTranslation
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.FourierKernelsComposition

/-! # Physical Fourier tests with absolute exit time and velocity -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo Parabolic ProbabilityTheory

/-- The literal physical test for a Fourier measure on an exit-data set. -/
def exitFourierTest {d : ℕ} (P : KineticPoint d) (v₀ ξ : PDE.Vec d)
    (E : Set (TimeVelocity d)) (Q : KineticPoint d) : ℂ :=
  {Q : KineticPoint d | (Q.time, Q.velocity) ∈ E}.indicator
    (exitPhase ξ ∘ exitCoordinates P v₀) Q

/-- Fourier tests are measurable for each Borel exit-data set. -/
theorem measurable_exitFourierTest {d : ℕ} (P : KineticPoint d) (v₀ ξ : PDE.Vec d)
    {E : Set (TimeVelocity d)} (hE : MeasurableSet E) :
    Measurable (exitFourierTest P v₀ ξ E) :=
  ((continuous_exitPhase ξ).comp (continuous_exitCoordinates P v₀)).measurable.indicator
    (hE.preimage (continuous_time.prodMk continuous_velocity).measurable)

/-- Every physical Fourier test has modulus at most one. -/
theorem norm_exitFourierTest_le_one {d : ℕ} (P : KineticPoint d) (v₀ ξ : PDE.Vec d)
    (E : Set (TimeVelocity d)) (Q : KineticPoint d) :
    ‖exitFourierTest P v₀ ξ E Q‖ ≤ 1 := by
  unfold exitFourierTest
  by_cases hQ : (Q.time, Q.velocity) ∈ E
  · rw [indicator_of_mem (show Q ∈ {Q | (Q.time, Q.velocity) ∈ E} from hQ)]
    exact (norm_exitPhase ξ _).le
  · rw [indicator_of_notMem (show Q ∉ {Q | (Q.time, Q.velocity) ∈ E} from hQ)]
    simp only [norm_zero, zero_le_one]

/-- The centered Fourier measure of any finite physical measure has the raw test formula. -/
theorem exitFourier_map_exitCoordinates_apply {d : ℕ}
    (μ : Measure (KineticPoint d)) [IsFiniteMeasure μ]
    (P : KineticPoint d) (v₀ ξ : PDE.Vec d)
    (E : Set (TimeVelocity d)) (hE : MeasurableSet E) :
    exitFourier (μ.map (exitCoordinates P v₀)) ξ E =
      ∫ Q, exitFourierTest P v₀ ξ E Q ∂μ := by
  rw [exitFourier_apply _ ξ E hE, ← integral_indicator (hE.preimage measurable_snd)]
  have hg : Measurable ((Prod.snd ⁻¹' E).indicator (exitPhase ξ)) :=
    (continuous_exitPhase ξ).measurable.indicator (hE.preimage measurable_snd)
  rw [integral_map (continuous_exitCoordinates P v₀).measurable.aemeasurable
    hg.aestronglyMeasurable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun Q => by
    by_cases hQ : (Q.time, Q.velocity) ∈ E <;>
      simp [exitFourierTest, exitCoordinates, hQ])

/-- Bochner Fubini holds for bounded complex Fourier tests in the genuine later mixture. -/
theorem ballExitRestart_integral_complex
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})
    (H : {t : ℝ // P.1.time < t ∧ t < T.1})
    (g : KineticPoint d → ℂ) (hg : Measurable g)
    (hgb : ∃ M : ℝ, ∀ Q, ‖g Q‖ ≤ M) :
    (∫ Q, g Q ∂ballExitRestart hH hLE hd hlam hLam B hB v₀ hR P T H) =
      ∫ w, (∫ Q, g Q ∂ballExitRaw hH hLE hd hlam hLam B hB v₀ hR
        (ballStateStart H.1 w) ⟨T.1, H.2.2⟩)
        ∂(localBallKernel hH hLE hd hlam hLam B hB v₀ hR).fiberKernel
          (PDE.isOpen_euclideanBall v₀ R).measurableSet P.1.time H.1 H.2.1.le
          (ballStartState P) := by
  have hf := ballExit_fiber_isFinite hH hLE hd hlam hLam B hB v₀ hR P ⟨H.1, H.2.1⟩
  let κ := (localBallKernel hH hLE hd hlam hLam B hB v₀ hR).fiberKernel
    (PDE.isOpen_euclideanBall v₀ R).measurableSet P.1.time H.1 H.2.1.le (ballStartState P)
  let K := ballBoundaryKernel hH hLE hd hlam hLam B hB v₀ hR H.1 T.1 H.2.2
  have heq : (K ∘ₖ Kernel.const Unit κ) () =
      ballExitRestart hH hLE hd hlam hLam B hB v₀ hR P T H := by
    rw [Kernel.comp_apply, Kernel.const_apply]
    rfl
  obtain ⟨M, hM⟩ := hgb
  have hi : Integrable g (ballExitRestart hH hLE hd hlam hLam B hB v₀ hR P T H) :=
    Integrable.of_bound hg.aestronglyMeasurable M (Filter.Eventually.of_forall hM)
  have h := Kernel.integral_comp (heq.symm ▸ hi)
  rw [heq] at h
  exact h

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
