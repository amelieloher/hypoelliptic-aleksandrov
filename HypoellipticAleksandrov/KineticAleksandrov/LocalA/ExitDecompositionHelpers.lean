module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitDecompositionTerminalMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripKernelIntegral

/-! # Finite integrals and the literal lateral part of local exit measures -/

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

/-- Continuous bounded closed-strip data are integrable for the actual exit measure. -/
theorem ballExit_integrable_closed (P : LocalBallStart v₀ R)
    (T : {t : ℝ // P.1.time < t}) (u : KineticPoint d → ℝ)
    (hc : ContinuousOn u (localClosedStrip P.1.time T.1 v₀ R))
    (hb : ∃ M : ℝ, ∀ Q ∈ localClosedStrip P.1.time T.1 v₀ R, |u Q| ≤ M) :
    Integrable u (ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T) := by
  let μ := ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T
  have hclosed : ∀ᵐ Q ∂μ, Q ∈ localClosedStrip P.1.time T.1 v₀ R :=
    (ballExitRaw_ae_trace hH hLE hd hlam hLam B hB v₀ hR P T).mono
      (fun _ hQ => localTrace_subset_closed T.2.le v₀ R hQ)
  have hm := hc.aestronglyMeasurable (μ := μ)
    (isClosed_localClosedStrip P.1.time T.1 v₀ R).measurableSet
  rw [Measure.restrict_eq_self_of_ae_mem hclosed] at hm
  obtain ⟨M, hM⟩ := hb
  apply Integrable.of_bound hm M
  filter_upwards [hclosed] with Q hQ
  simpa only [Real.norm_eq_abs] using hM Q hQ

/-- The complement of the open terminal velocities is exactly the lateral measure,
including the terminal velocity corner. -/
theorem ballExit_lateral_restrict (P : LocalBallStart v₀ R)
    (T : {t : ℝ // P.1.time < t}) :
    (ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T).restrict
      {Q | Q.velocity ∈ PDE.euclideanBall v₀ R}ᶜ =
    (ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T).restrict
      {Q | Q.velocity ∈ frontier (PDE.euclideanBall v₀ R)} := by
  apply Measure.restrict_congr_set
  filter_upwards [ballExitRaw_ae_trace hH hLE hd hlam hLam B hB v₀ hR P T] with Q hQ
  apply propext
  change (Q.velocity ∉ PDE.euclideanBall v₀ R) ↔
    Q.velocity ∈ frontier (PDE.euclideanBall v₀ R)
  have hcl : Q.velocity ∈ closure (PDE.euclideanBall v₀ R) := by
    rcases hQ with hQ | hQ
    · exact hQ.2
    · exact frontier_subset_closure hQ.2.2
  rw [frontier, mem_sdiff, (PDE.isOpen_euclideanBall v₀ R).interior_eq]
  exact ⟨fun h => ⟨hcl, h⟩, fun h => h.2⟩

/-- The terminal valid-state transition is finite, as established by the face identity. -/
instance ballExit_fiber_isFinite (P : LocalBallStart v₀ R)
    (T : {t : ℝ // P.1.time < t}) :
    IsFiniteMeasure ((localBallKernel hH hLE hd hlam hLam B hB v₀ hR).fiberKernel
      (PDE.isOpen_euclideanBall v₀ R).measurableSet P.1.time T.1 T.2.le
      (ballStartState P)) := by
  let κ := (localBallKernel hH hLE hd hlam hLam B hB v₀ hR).fiberKernel
    (PDE.isOpen_euclideanBall v₀ R).measurableSet P.1.time T.1 T.2.le (ballStartState P)
  have h := congrArg (fun μ : Measure (KineticPoint d) => μ univ)
    (ballExit_terminal_interior_eq_map hH hLE hd hlam hLam B hB v₀ hR P T)
  rw [Measure.map_apply (continuous_ballStatePoint T.1 v₀ R).measurable
    MeasurableSet.univ, preimage_univ] at h
  refine ⟨?_⟩
  change κ univ < ⊤
  rw [← h]
  exact measure_lt_top _ _

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
