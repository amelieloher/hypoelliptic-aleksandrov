module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitDecompositionHelpers

/-! # Exact short-strip decomposition for compact smooth boundary tests -/

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

/-- Smooth tests split into the literal lateral part and the actual later exit kernel. -/
theorem ballExit_smooth_short_strip_decomposition
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})
    (H : {t : ℝ // P.1.time < t ∧ t < T.1})
    (φ : KineticPoint d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ (KineticPoint.equivProd d).symm))
    (hc : HasCompactSupport φ) :
    (∫ Q, φ Q ∂ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T) =
      (∫ Q in {Q | Q.velocity ∈ frontier (PDE.euclideanBall v₀ R)},
        φ Q ∂ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P ⟨H.1, H.2.1⟩) +
      ∫ w, (∫ Q, φ Q ∂ballExitRaw hH hLE hd hlam hLam B hB v₀ hR
        (ballStateStart H.1 w) ⟨T.1, H.2.2⟩)
        ∂(localBallKernel hH hLE hd hlam hLam B hB v₀ hR).fiberKernel
          (PDE.isOpen_euclideanBall v₀ R).measurableSet P.1.time H.1 H.2.1.le
          (ballStartState P) := by
  let μ := ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P ⟨H.1, H.2.1⟩
  let u := ballBoundarySolution hH hLE hd hlam hLam B hB v₀ hR P.1.time T.1 φ
  let S : Set (KineticPoint d) := {Q | Q.velocity ∈ PDE.euclideanBall v₀ R}
  let L : Set (KineticPoint d) := {Q | Q.velocity ∈ frontier (PDE.euclideanBall v₀ R)}
  let κ := (localBallKernel hH hLE hd hlam hLam B hB v₀ hR).fiberKernel
    (PDE.isOpen_euclideanBall v₀ R).measurableSet P.1.time H.1 H.2.1.le (ballStartState P)
  let j (w : EvolutionState (PDE.euclideanBall v₀ R) (fun _ => 0) H.1) :=
    (ballStateStart H.1 w).1
  have hS : MeasurableSet S :=
    (PDE.isOpen_euclideanBall v₀ R).measurableSet.preimage continuous_velocity.measurable
  have hL : MeasurableSet L := isClosed_frontier.measurableSet.preimage
    continuous_velocity.measurable
  have hu := ballBoundarySolution_smooth_traces hH hLE hd hlam hLam B hB v₀ hR
    P.1.time T.1 T.2 φ hφ hc
  have hcl : localClosedStrip P.1.time H.1 v₀ R ⊆
      localClosedStrip P.1.time T.1 v₀ R :=
    fun Q hQ => ⟨hQ.1, hQ.2.1.trans H.2.2.le, hQ.2.2⟩
  obtain ⟨M, hM⟩ := ballBoundarySolution_bounded hH hLE hd hlam hLam B hB v₀ hR
    P.1.time T.1 T.2 φ hφ hc
  have hui := ballExit_integrable_closed hH hLE hd hlam hLam B hB v₀ hR
    P ⟨H.1, H.2.1⟩ u (hu.2.2.1.mono hcl) ⟨M, fun Q hQ => hM Q (hcl hQ)⟩
  have hlat : (∫ Q in Sᶜ, u Q ∂μ) = ∫ Q in L, φ Q ∂μ := by
    rw [ballExit_lateral_restrict hH hLE hd hlam hLam B hB v₀ hR P ⟨H.1, H.2.1⟩]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hL,
      ae_restrict_of_ae (ballExitRaw_ae_trace hH hLE hd hlam hLam B hB v₀ hR
        P ⟨H.1, H.2.1⟩)] with Q hv hQ
    have hQc := localTrace_subset_closed H.2.1.le v₀ R hQ
    exact hu.2.2.2 (Or.inr ⟨hQc.1, hQc.2.1.trans H.2.2.le, hv⟩)
  have hterminal : (∫ Q in S, u Q ∂μ) =
      ∫ w, (∫ Q, φ Q ∂ballExitRaw hH hLE hd hlam hLam B hB v₀ hR
        (ballStateStart H.1 w) ⟨T.1, H.2.2⟩) ∂κ := by
    have hm := ballExit_terminal_interior_eq_map hH hLE hd hlam hLam B hB v₀ hR
      P ⟨H.1, H.2.1⟩
    have hum : AEStronglyMeasurable u (κ.map j) := by
      rw [← hm]
      exact hui.aestronglyMeasurable.restrict
    rw [hm, integral_map (continuous_ballStatePoint H.1 v₀ R).measurable.aemeasurable hum]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro w
    have hpoint : j w ∈ localClosedStrip H.1 T.1 v₀ R :=
      ⟨le_rfl, H.2.2.le, subset_closure (ball_state_velocity_mem H.1 w)⟩
    have heq := ballBoundarySolution_lowerTime_eq hH hLE hd hlam hLam B hB v₀ hR
      P.1.time H.1 T.1 H.2.1.le H.2.2 φ hφ hc hpoint
    exact heq.trans
      ((ballExitRaw_spec hH hLE hd hlam hLam B hB v₀ hR
        (ballStateStart H.1 w) ⟨T.1, H.2.2⟩).2.2 φ hφ hc).symm
  rw [ballExit_smooth_short_strip_representation hH hLE hd hlam hLam B hB v₀ hR
    P T H φ hφ hc, ← integral_add_compl hS hui, hlat, hterminal, add_comm]

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
