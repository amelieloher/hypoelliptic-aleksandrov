module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitDecompositionSmooth

/-! # The finite actual later-exit mixture on valid terminal states -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo Parabolic

variable (hH : HormanderHypoellipticityStatement)
  (hLE : LiebermanEllipsoidDirichletStatement)
  {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ}
  (hlam : 0 < lam) (hLam : lam ≤ Lam)
  (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
  (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)

/-- The genuine later exit mixture, with no values assigned to invalid velocity starts. -/
def ballExitRestart (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})
    (H : {t : ℝ // P.1.time < t ∧ t < T.1}) : Measure (KineticPoint d) :=
  ((localBallKernel hH hLE hd hlam hLam B hB v₀ hR).fiberKernel
    (PDE.isOpen_euclideanBall v₀ R).measurableSet P.1.time H.1 H.2.1.le
    (ballStartState P)).bind
      (ballBoundaryKernel hH hLE hd hlam hLam B hB v₀ hR H.1 T.1 H.2.2)

/-- The actual later mixture has exactly the terminal-interior mass of the shorter strip. -/
theorem ballExitRestart_mass (P : LocalBallStart v₀ R)
    (T : {t : ℝ // P.1.time < t}) (H : {t : ℝ // P.1.time < t ∧ t < T.1}) :
    ballExitRestart hH hLE hd hlam hLam B hB v₀ hR P T H univ =
      ((localBallKernel hH hLE hd hlam hLam B hB v₀ hR).fiberKernel
        (PDE.isOpen_euclideanBall v₀ R).measurableSet P.1.time H.1 H.2.1.le
        (ballStartState P)) univ := by
  unfold ballExitRestart
  rw [Measure.bind_apply MeasurableSet.univ
    (ProbabilityTheory.Kernel.measurable _).aemeasurable]
  change (∫⁻ w, ballExitRaw hH hLE hd hlam hLam B hB v₀ hR
    (ballStateStart H.1 w) ⟨T.1, H.2.2⟩ univ ∂_) = _
  simp only [ballExitRaw_mass, lintegral_const, one_mul]

/-- The genuine later-exit mixture is finite. -/
instance ballExitRestart_isFinite (P : LocalBallStart v₀ R)
    (T : {t : ℝ // P.1.time < t}) (H : {t : ℝ // P.1.time < t ∧ t < T.1}) :
    IsFiniteMeasure (ballExitRestart hH hLE hd hlam hLam B hB v₀ hR P T H) := by
  refine ⟨?_⟩
  rw [ballExitRestart_mass]
  exact @measure_lt_top _ _ _ (ballExit_fiber_isFinite hH hLE hd hlam hLam B hB v₀ hR
    P ⟨H.1, H.2.1⟩) univ

/-- Bounded measurable data obey Fubini for the actual later exit mixture. -/
theorem ballExitRestart_integral (P : LocalBallStart v₀ R)
    (T : {t : ℝ // P.1.time < t}) (H : {t : ℝ // P.1.time < t ∧ t < T.1})
    (g : KineticPoint d → ℝ) (hg : Measurable g)
    (hgb : ∃ M : ℝ, ∀ Q, |g Q| ≤ M) :
    (∫ Q, g Q ∂ballExitRestart hH hLE hd hlam hLam B hB v₀ hR P T H) =
      ∫ w, (∫ Q, g Q ∂ballExitRaw hH hLE hd hlam hLam B hB v₀ hR
        (ballStateStart H.1 w) ⟨T.1, H.2.2⟩)
        ∂(localBallKernel hH hLE hd hlam hLam B hB v₀ hR).fiberKernel
          (PDE.isOpen_euclideanBall v₀ R).measurableSet P.1.time H.1 H.2.1.le
          (ballStartState P) := by
  have := ballExit_fiber_isFinite hH hLE hd hlam hLam B hB v₀ hR
    P ⟨H.1, H.2.1⟩
  obtain ⟨M, hM⟩ := hgb
  have hi : Integrable g (ballExitRestart hH hLE hd hlam hLam B hB v₀ hR P T H) :=
    Integrable.of_bound hg.aestronglyMeasurable M
      (Filter.Eventually.of_forall (fun Q => by simpa only [Real.norm_eq_abs] using hM Q))
  exact Autonomous.nested_integral_bind _ _
    (ProbabilityTheory.Kernel.measurable _) g hi

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
