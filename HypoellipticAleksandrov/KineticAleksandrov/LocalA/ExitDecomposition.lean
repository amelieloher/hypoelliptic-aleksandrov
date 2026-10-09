module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitDecompositionRestart
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundaryMeasureUnique

/-! # Corner-aware short-strip exit decomposition for bounded Borel data -/

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

/-- Equality of the actual measures upgrades smooth tests to every bounded Borel test. -/
theorem ballExit_short_strip_measure_decomposition
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})
    (H : {t : ℝ // P.1.time < t ∧ t < T.1}) :
    ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T =
      (ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P ⟨H.1, H.2.1⟩).restrict
        {Q | Q.velocity ∈ frontier (PDE.euclideanBall v₀ R)} +
      ballExitRestart hH hLE hd hlam hLam B hB v₀ hR P T H := by
  apply boundary_measure_ext
  intro φ hφ hc
  have hcont := boundary_probe_continuous φ hφ
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous hcont
  have hb : ∃ M : ℝ, ∀ Q, |φ Q| ≤ M :=
    ⟨M, fun Q => by simpa only [Real.norm_eq_abs] using hM Q⟩
  rw [integral_add_measure (hcont.integrable_of_hasCompactSupport hc)
    (hcont.integrable_of_hasCompactSupport hc),
    ballExitRestart_integral hH hLE hd hlam hLam B hB v₀ hR P T H φ hcont.measurable hb]
  exact ballExit_smooth_short_strip_decomposition hH hLE hd hlam hLam B hB v₀ hR
    P T H φ hφ hc

/-- The source decomposition uses the valid-state killed kernel and keeps the corner lateral. -/
theorem ballExit_short_strip_decomposition
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})
    (H : {t : ℝ // P.1.time < t ∧ t < T.1})
    (g : KineticPoint d → ℝ) (hg : Measurable g)
    (hgb : ∃ M : ℝ, ∀ Q, |g Q| ≤ M) :
    (∫ Q, g Q ∂ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T) =
      (∫ Q in {Q | Q.velocity ∈ frontier (PDE.euclideanBall v₀ R)},
        g Q ∂ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P ⟨H.1, H.2.1⟩) +
      ∫ w, (∫ Q, g Q ∂ballExitRaw hH hLE hd hlam hLam B hB v₀ hR
        (ballStateStart H.1 w) ⟨T.1, H.2.2⟩)
        ∂(localBallKernel hH hLE hd hlam hLam B hB v₀ hR).fiberKernel
          (PDE.isOpen_euclideanBall v₀ R).measurableSet P.1.time H.1 H.2.1.le
          (ballStartState P) := by
  obtain ⟨M, hM⟩ := hgb
  have hi (μ : Measure (KineticPoint d)) [IsFiniteMeasure μ] : Integrable g μ :=
    Integrable.of_bound hg.aestronglyMeasurable M
      (Filter.Eventually.of_forall (fun Q => by simpa only [Real.norm_eq_abs] using hM Q))
  rw [ballExit_short_strip_measure_decomposition hH hLE hd hlam hLam B hB v₀ hR P T H,
    integral_add_measure (hi _) (hi _),
    ballExitRestart_integral hH hLE hd hlam hLam B hB v₀ hR P T H g hg ⟨M, hM⟩]

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
